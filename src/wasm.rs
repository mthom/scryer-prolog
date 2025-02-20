//! Wasm interface

#![allow(missing_docs)]

use std::mem;
use std::sync::mpsc;
use std::sync::mpsc::{Receiver, Sender};

use ouroboros::self_referencing;
use wasm_bindgen::prelude::*;

use crate::*;

#[wasm_bindgen(js_name = MachineBuilder)]
#[derive(Default)]
pub struct WasmMachineBuilder {
    inner: MachineBuilder,
}

#[wasm_bindgen(js_class = MachineBuilder)]
impl WasmMachineBuilder {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        Default::default()
    }

    pub fn build(&mut self) -> WasmMachine {
        WasmMachine {
            inner: Ok(std::mem::take(&mut self.inner).build()),
        }
    }
}

#[wasm_bindgen(js_name = Machine)]
pub struct WasmMachine {
    inner: Result<Machine, Receiver<Machine>>,
}

#[wasm_bindgen(js_class = Machine)]
impl WasmMachine {
    #[wasm_bindgen(js_name = runQuery)]
    pub fn run_query(&mut self, query: String) -> Result<JsValue, JsValue> {
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

        Ok(query_state)
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

#[wasm_bindgen(js_name = QueryState)]
pub struct WasmQueryState {
    inner: Option<WasmQueryStateInner>,
}

#[wasm_bindgen(js_class = QueryState)]
impl WasmQueryState {
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

    #[wasm_bindgen(js_name = drop)]
    pub fn drop_inner(&mut self) {
        let ouroboros_impl_wasm_query_state_inner::Heads {
            machine,
            drop_channel,
        } = self.inner.take().unwrap().into_heads();
        drop_channel.send(machine).unwrap();
    }
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
