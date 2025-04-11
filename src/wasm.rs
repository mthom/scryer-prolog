//! Wasm interface

use std::mem;
use std::sync::mpsc;
use std::sync::mpsc::{Receiver, Sender};

use ouroboros::self_referencing;
use wasm_bindgen::prelude::*;

use crate::*;

/// A builder for a `Machine`.
#[wasm_bindgen(js_name = MachineBuilder)]
#[derive(Default)]
pub struct WasmMachineBuilder {
    inner: MachineBuilder,
}

#[wasm_bindgen(js_class = MachineBuilder)]
impl WasmMachineBuilder {
    /// Creates a new `MachineBuilder` with the default configuration.
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        Default::default()
    }

    /// Creates a new `Machine`.
    pub fn build(&mut self) -> WasmMachine {
        WasmMachine {
            inner: Ok(std::mem::take(&mut self.inner).build()),
        }
    }
}

/// The Scryer Prolog `Machine`.
#[wasm_bindgen(js_name = Machine)]
pub struct WasmMachine {
    inner: Result<Machine, Receiver<Machine>>,
}

#[wasm_bindgen(js_class = Machine)]
impl WasmMachine {
    fn ensure_machine_ownership(&mut self) -> Result<(), JsValue> {
        if self.inner.is_err() {
            // We have a receiver, try to get the Machine
            let machine = self
                .inner
                .as_mut()
                .unwrap_err()
                .try_recv()
                .map_err(|_| js_sys::Error::new("Another query is still active"))?;
            let _ = mem::replace(&mut self.inner, Ok(machine));
        }
        Ok(())
    }

    /// Runs a query.
    ///
    /// You can only have one query at a time. If you try to do anything with this machine while
    /// doing a query an error will be thrown.
    #[wasm_bindgen(js_name = runQuery)]
    pub fn run_query(&mut self, query: String) -> Result<JsValue, JsValue> {
        self.ensure_machine_ownership()?;
        assert!(self.inner.is_ok());

        // Installs a receiver and gets the machine
        let (sender, receiver) = mpsc::channel();
        let machine = mem::replace(&mut self.inner, Err(receiver)).unwrap();

        let query_state: JsValue = WasmQueryState {
            inner: Some(
                WasmQueryStateInnerBuilder {
                    machine,
                    drop_channel: sender,
                    query_state_builder: move |m: &mut Machine| m.run_query(query),
                }
                .build(),
            ),
        }
        .into();
        self_iterable(&query_state);

        Ok(query_state)
    }

    /// Consults a module.
    #[wasm_bindgen(js_name = consultModuleString)]
    pub fn consult_module_string(
        &mut self,
        module: String,
        program: String,
    ) -> Result<(), JsValue> {
        self.ensure_machine_ownership()?;
        assert!(self.inner.is_ok());

        let inner = self.inner.as_mut().unwrap();
        inner.consult_module_string(&module, program);

        Ok(())
    }
}

#[self_referencing]
struct WasmQueryStateInner {
    machine: Machine,
    drop_channel: Sender<Machine>,
    #[covariant]
    #[borrows(mut machine)]
    query_state: QueryState<'this>,
}

/// The state of a running query.
#[wasm_bindgen(js_name = QueryState)]
pub struct WasmQueryState {
    inner: Option<WasmQueryStateInner>,
}

#[wasm_bindgen(js_class = QueryState)]
impl WasmQueryState {
    /// Gets the next leaf answer.
    ///
    /// This follows the Javascript iterator protocol, so it returns an object that
    /// contains a `done` field and a `value` field. If `done` is `false`, then the query ended
    /// and control of the `Machine` will be given back to the `Machine` that created this query.
    /// Any call after that will result in an error.
    #[wasm_bindgen(js_name = next)]
    pub fn next_answer(&mut self) -> Result<JsValue, JsValue> {
        let ret = js_sys::Object::new();
        let mut error = None;
        let mut to_drop = false;
        match &mut self.inner {
            Some(ref mut inner) => {
                inner.with_query_state_mut(|query_state| match query_state.next() {
                    Some(Ok(leaf_answer)) => {
                        js_sys::Reflect::set(&ret, &"value".into(), &leaf_answer.into()).unwrap();
                        js_sys::Reflect::set(&ret, &"done".into(), &false.into()).unwrap();
                    }
                    Some(Err(error_term)) => {
                        let js_error = js_sys::Error::new("Prolog error");
                        js_error.set_cause(&error_term.into());
                        error = Some(js_error);
                    }
                    None => {
                        js_sys::Reflect::set(&ret, &"done".into(), &true.into()).unwrap();
                        to_drop = true;
                    }
                })
            }
            None => return Err(js_sys::Error::new("This query was already dropped").into()),
        }

        if let Some(e) = error {
            self.drop_inner();
            return Err(JsValue::from(e));
        }

        if to_drop {
            self.drop_inner();
        }

        Ok(ret.into())
    }

    /// Drops the query.
    ///
    /// This is useful to end a query early. Like finishing a query, control will be given back
    /// to the `Machine` and any call to `next` after that will result in an error.
    #[wasm_bindgen(js_name = drop)]
    pub fn drop_inner(&mut self) {
        let ouroboros_impl_wasm_query_state_inner::Heads {
            machine,
            drop_channel,
        } = self.inner.take().unwrap().into_heads();
        drop_channel.send(machine).unwrap();
    }
}

/// Sets a [JsValue] as the `Symbol.iterator` property of the [JsValue].
///
/// If the [JsValue] conforms to the [JavaScript iterator interface](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Guide/Iterators_and_generators),
/// this function will make the [JsValue] iterable.
#[wasm_bindgen(inline_js = "
    export function self_iterable(obj) {
        obj[Symbol.iterator] = function () {
            return this;
        };
    }
")]
extern "C" {
    fn self_iterable(obj: &JsValue);
}

impl From<LeafAnswer> for JsValue {
    fn from(leaf_answer: LeafAnswer) -> JsValue {
        match leaf_answer {
            LeafAnswer::True => true.into(),
            LeafAnswer::False => false.into(),
            LeafAnswer::Exception(e) => {
                let obj = js_sys::Object::new();
                js_sys::Reflect::set(&obj, &"type".into(), &"exception".into()).unwrap();
                js_sys::Reflect::set(&obj, &"exception".into(), &e.into()).unwrap();
                obj.into()
            }
            LeafAnswer::LeafAnswer { bindings } => {
                let bindings_obj = js_sys::Object::new();
                for (var, term) in bindings.into_iter() {
                    js_sys::Reflect::set(&bindings_obj, &var.into(), &term.into()).unwrap();
                }

                let leaf_answer_obj = js_sys::Object::new();
                js_sys::Reflect::set(&leaf_answer_obj, &"type".into(), &"leafAnswer".into())
                    .unwrap();
                js_sys::Reflect::set(&leaf_answer_obj, &"bindings".into(), &bindings_obj.into())
                    .unwrap();
                leaf_answer_obj.into()
            }
        }
    }
}

impl From<Term> for JsValue {
    fn from(term: Term) -> JsValue {
        match term {
            Term::Integer(i) => {
                let obj = js_sys::Object::new();
                js_sys::Reflect::set(&obj, &"type".into(), &"integer".into()).unwrap();
                js_sys::Reflect::set(
                    &obj,
                    &"integer".into(),
                    &js_sys::BigInt::new(&i.to_string().into()).unwrap().into(),
                )
                .unwrap();
                obj.into()
            }
            Term::Rational(r) => {
                let obj = js_sys::Object::new();
                js_sys::Reflect::set(&obj, &"type".into(), &"rational".into()).unwrap();
                js_sys::Reflect::set(
                    &obj,
                    &"numerator".into(),
                    &js_sys::BigInt::new(&r.numerator().to_string().into())
                        .unwrap()
                        .into(),
                )
                .unwrap();
                js_sys::Reflect::set(
                    &obj,
                    &"denominator".into(),
                    &js_sys::BigInt::new(&r.denominator().to_string().into())
                        .unwrap()
                        .into(),
                )
                .unwrap();
                obj.into()
            }
            Term::Float(f) => {
                let obj = js_sys::Object::new();
                js_sys::Reflect::set(&obj, &"type".into(), &"float".into()).unwrap();
                js_sys::Reflect::set(&obj, &"float".into(), &f.into()).unwrap();
                obj.into()
            }
            Term::Atom(a) => {
                let obj = js_sys::Object::new();
                js_sys::Reflect::set(&obj, &"type".into(), &"atom".into()).unwrap();
                js_sys::Reflect::set(&obj, &"atom".into(), &a.into()).unwrap();
                obj.into()
            }
            Term::String(s) => {
                let obj = js_sys::Object::new();
                js_sys::Reflect::set(&obj, &"type".into(), &"string".into()).unwrap();
                js_sys::Reflect::set(&obj, &"string".into(), &s.into()).unwrap();
                obj.into()
            }
            Term::List(l) => {
                let list = js_sys::Array::new();
                for term in l {
                    list.push(&term.into());
                }

                let obj = js_sys::Object::new();
                js_sys::Reflect::set(&obj, &"type".into(), &"list".into()).unwrap();
                js_sys::Reflect::set(&obj, &"list".into(), &list.into()).unwrap();
                obj.into()
            }
            Term::Compound(functor, args) => {
                let args_list = js_sys::Array::new();
                for term in args {
                    args_list.push(&term.into());
                }

                let obj = js_sys::Object::new();
                js_sys::Reflect::set(&obj, &"type".into(), &"compound".into()).unwrap();
                js_sys::Reflect::set(&obj, &"functor".into(), &functor.into()).unwrap();
                js_sys::Reflect::set(&obj, &"args".into(), &args_list.into()).unwrap();
                obj.into()
            }
            Term::Var(v) => {
                let obj = js_sys::Object::new();
                js_sys::Reflect::set(&obj, &"type".into(), &"variable".into()).unwrap();
                js_sys::Reflect::set(&obj, &"variable".into(), &v.into()).unwrap();
                obj.into()
            }
        }
    }
}
