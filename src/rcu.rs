use std::{
    cell::OnceCell,
    fmt::Debug,
    mem::ManuallyDrop,
    ops::Deref,
    ptr::NonNull,
    sync::{
        atomic::{AtomicPtr, AtomicU8},
        Arc, RwLock, Weak,
    },
};

// the epoch counters of all threads that have ever accessed an Rcu
// threads that have finished will have a dangling Weak reference and can be cleand up
// having this be shared between all Rcu's is a tradeof,
// writes will be slower as more epoch counters need to be waited for
// reads should be faster as a thread only needs to register itself once on the first read
//
static EPOCH_COUNTERS: RwLock<Vec<Weak<AtomicU8>>> = RwLock::new(Vec::new());

thread_local! {
    // odd value means the current thread is about to access the active_epoch of an Rcu
    // a thread has a single epoch counter for all Rcu it accesses,
    // as a thread can only access one Rcu at a time
    static THREAD_EPOCH_COUNTER: OnceCell<Arc<AtomicU8>> = const { OnceCell::new() };
}

pub struct Rcu<T> {
    active_value: AtomicPtr<T>,
}

impl<T: std::fmt::Debug> std::fmt::Debug for Rcu<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let active_epoch = self.active_epoch();
        f.debug_struct("Rcu")
            .field("active_value", &active_epoch)
            .finish()
    }
}

impl<T> Rcu<T> {
    pub fn new(initial_value: T) -> Self {
        Rcu {
            active_value: AtomicPtr::new(Arc::into_raw(Arc::new(initial_value)).cast_mut()),
        }
    }

    pub fn active_epoch(&self) -> RcuRef<T, T> {
        THREAD_EPOCH_COUNTER.with(|epoch_counter| {
            let epoch_counter = epoch_counter.get_or_init(|| {
                let epoch_counter = Arc::new(AtomicU8::new(0));
                // register the current threads epoch counter on init
                EPOCH_COUNTERS
                    .write()
                    .unwrap()
                    .push(Arc::downgrade(&epoch_counter));
                epoch_counter
            });

            let old = epoch_counter.fetch_add(1, std::sync::atomic::Ordering::AcqRel);
            assert!(old % 2 == 0, "Old Epoch counter value should be even!");
        });

        let arc_ptr = self.active_value.load(std::sync::atomic::Ordering::Acquire);

        let arc = unsafe {
            // Safety:
            // - the ptr was created in Rcu::new or Rcu::replace with Arc::into_raw
            // - the Rcu is responsible for of the arc's strong refrences
            // - the Rcu is alive as this function takes a reference to the Rcu
            // - replace will wait with decrementing the old values strong count until our epoich counter is even again
            Arc::increment_strong_count(arc_ptr);
            // Safety:
            // - the ptr was created in Rcu::new or Rcu::replace with Arc::into_raw
            // - we have just ensured an additional strong count by incrementing the count
            Arc::from_raw(arc_ptr)
        };

        THREAD_EPOCH_COUNTER.with(|epoch_counter| {
            let old = epoch_counter
                .get().expect("we initialized the OnceCell when we incremented the epoch counter the fist time")
                .fetch_add(1, std::sync::atomic::Ordering::AcqRel);
            assert!(old % 2 != 0, "Old Epoch counter value should be odd!");
        });

        RcuRef {
            data: arc.deref().into(),
            arc,
        }
    }

    /*
     *  replace the Rcu'S content with a new value
     *
     *  This does not syncronize write and last to update the active_value pointer wins,
     *  all writes that do not win will be lost, though not leaked.
     *  This will block untill the old value can be reclaimed,
     *  i.e. all threads whitnest to be in the read critical sections
     *       have been witnest to have left the critical section at least once
     */
    pub fn replace(&self, new_value: T) {
        let arc_ptr = self.active_value.swap(
            Arc::into_raw(Arc::new(new_value)).cast_mut(),
            std::sync::atomic::Ordering::AcqRel,
        );

        // maually drop as we need to ensure not to drop the arc while
        // we have not witnest all threads to be or have been outside the read critical section
        // i.e. even epoch counter or different odd epoch counter
        // Safety:
        // - the ptr was created in Rcu::new or Rcu::replace with Arc::into_raw
        // - the Rcu itself holds one strong count
        let arc = unsafe { ManuallyDrop::new(Arc::from_raw(arc_ptr)) };

        let epochs = EPOCH_COUNTERS.read().unwrap().clone();
        let mut epochs = epochs
            .into_iter()
            .flat_map(|elem| {
                let arc = elem.upgrade()?;
                let init_val = arc.load(std::sync::atomic::Ordering::Acquire);
                if init_val % 2 == 0 {
                    // already even can be ignored
                    return None;
                }
                // odd initial value thread is in read critical section
                // need to wait for the value to change before we can drop the arc
                Some((init_val, elem))
            })
            .collect::<Vec<_>>();

        while !epochs.is_empty() {
            epochs.retain(|elem| {
                let Some(arc) = elem.1.upgrade() else {
                    // as the thread is dead it can't have a ref to old arc
                    return false;
                };
                // the epoch counter has not changed so the thread is still in the same instance of the critical section
                // any different value is ok as
                // - even values indicate the thread is outside the critical section
                // - a diffrent odd value indicates the thread has left the critical section and can subsequently only read the new active_value
                arc.load(std::sync::atomic::Ordering::Acquire) == elem.0
            })
        }

        // Safety:
        // - we have not dropped the arc another way
        // - we witnessed all threads either with an even epoch count or with a new odd count
        //   as such they must have left the critical section at some point
        ManuallyDrop::into_inner(arc);
    }
}

pub struct RcuRef<T, M>
where
    T: ?Sized,
    M: ?Sized,
{
    arc: Arc<T>,
    data: NonNull<M>,
}

impl<T: ?Sized, M: ?Sized + Debug> Debug for RcuRef<T, M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RcuRef")
            .field("data", &self.deref())
            .finish()
    }
}

// use assoiated functions rather than methods so that we don't overlap
// with functions of the Deref Target type
impl<T: ?Sized, M: ?Sized> RcuRef<T, M> {
    pub fn map<N: ?Sized, F: for<'a> FnOnce(&'a M) -> &'a N>(referece: Self, f: F) -> RcuRef<T, N> {
        RcuRef {
            arc: referece.arc,
            data: f(unsafe { referece.data.as_ref() }).into(),
        }
    }

    pub fn try_map<N: ?Sized, F: for<'a> FnOnce(&'a M) -> Option<&'a N>>(
        referece: Self,
        f: F,
    ) -> Option<RcuRef<T, N>> {
        let val = f(unsafe { referece.data.as_ref() })?;
        Some(RcuRef {
            arc: Arc::clone(&referece.arc),
            data: val.into(),
        })
    }

    pub fn same_epoch<M2>(this: &Self, other: &RcuRef<T, M2>) -> bool {
        Arc::ptr_eq(&this.arc, &other.arc)
    }

    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        this.data == other.data
    }

    pub fn clone(this: &Self) -> Self {
        Self {
            arc: Arc::clone(&this.arc),
            data: this.data,
        }
    }

    pub fn get_root(this: &Self) -> &T {
        &this.arc
    }
}

impl<T: ?Sized, M: ?Sized> Deref for RcuRef<T, M> {
    type Target = M;

    fn deref(&self) -> &Self::Target {
        // Safety: The pointer points into the arc we are holding
        // while we are alive so is the target
        // as the content is in an Rcu no mutable acess is given out
        unsafe { self.data.as_ref() }
    }
}
