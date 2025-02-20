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

#[wasm_bindgen(inline_js = "
    export function self_iterable(obj) {
        obj[Symbol.iterator] = function () {
            return this
        };
    }
")]
extern "C" {
    fn self_iterable(obj: &JsValue);
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

        self_iterable(&query_state);
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

#[wasm_bindgen(inline_js = r#"
    export class LeafAnswer {
        constructor(bindings) {
            this.bindings = bindings;
        }
    }

    export class PrologInteger {
        constructor(integerStr) {
            this.type = "integer";
            this.integer = BigInt(integerStr);
        }
    }

    export class PrologRational {
        constructor(numeratorStr, denominatorStr) {
            this.type = "rational";
            this.numerator = BigInt(numeratorStr);
            this.denominator = BigInt(denominatorStr);
        }
    }

    export class PrologFloat {
        constructor(float) {
            this.type = "float";
            this.float = float;
        }
    }

    export class PrologAtom {
        constructor(atom) {
            this.type = "atom";
            this.atom = atom;
        }
    }

    export class PrologString {
        constructor(string) {
            this.type = "string";
            this.string = string;
        }
    }

    export class PrologList {
        constructor(list) {
            this.type = "list";
            this.list = list;
        }
    }

    export class PrologCompound {
        constructor(functor, args) {
            this.type = "compound";
            this.functor = functor;
            this.args = args;
        }
    }

    export class PrologVariable {
        constructor(variable) {
            this.type = "variable";
            this.variable = variable;
        }
    }

    export class PrologException {
        constructor(exception) {
            this.exception = exception;
        }
    }
"#)]
extern "C" {
    #[wasm_bindgen(js_name = LeafAnswer)]
    pub type JsLeafAnswer;

    #[wasm_bindgen(constructor, js_class = LeafAnswer)]
    pub fn new(bindings: js_sys::Object) -> JsLeafAnswer;

    #[wasm_bindgen(js_name = PrologInteger)]
    pub type JsPrologInteger;

    #[wasm_bindgen(constructor, js_class = PrologInteger)]
    pub fn new(int_str: &str) -> JsPrologInteger;

    #[wasm_bindgen(js_name = PrologRational)]
    pub type JsPrologRational;

    #[wasm_bindgen(constructor, js_class = PrologRational)]
    pub fn new(numer_str: &str, denom_str: &str) -> JsPrologRational;

    #[wasm_bindgen(js_name = PrologFloat)]
    pub type JsPrologFloat;

    #[wasm_bindgen(constructor, js_class = PrologFloat)]
    pub fn new(float: f64) -> JsPrologFloat;

    #[wasm_bindgen(js_name = PrologAtom)]
    pub type JsPrologAtom;

    #[wasm_bindgen(constructor, js_class = PrologAtom)]
    pub fn new(atom: &str) -> JsPrologAtom;

    #[wasm_bindgen(js_name = PrologString)]
    pub type JsPrologString;

    #[wasm_bindgen(constructor, js_class = PrologString)]
    pub fn new(string: &str) -> JsPrologString;

    #[wasm_bindgen(js_name = PrologList)]
    pub type JsPrologList;

    #[wasm_bindgen(constructor, js_class = PrologList)]
    pub fn new(list: js_sys::Array) -> JsPrologList;

    #[wasm_bindgen(js_name = PrologCompound)]
    pub type JsPrologCompound;

    #[wasm_bindgen(constructor, js_class = PrologCompound)]
    pub fn new(functor: &str, args: js_sys::Array) -> JsPrologCompound;

    #[wasm_bindgen(js_name = PrologVariable)]
    pub type JsPrologVariable;

    #[wasm_bindgen(constructor, js_class = PrologVariable)]
    pub fn new(variable: &str) -> JsPrologVariable;

    #[wasm_bindgen(js_name = PrologException)]
    pub type JsPrologException;

    #[wasm_bindgen(constructor, js_class = PrologException)]
    pub fn new(exception: JsValue) -> JsPrologException;
}

impl From<LeafAnswer> for JsValue {
    fn from(leaf_answer: LeafAnswer) -> JsValue {
        match leaf_answer {
            LeafAnswer::True => true.into(),
            LeafAnswer::False => false.into(),
            LeafAnswer::Exception(e) => JsPrologException::new(e.into()).into(),
            LeafAnswer::LeafAnswer { bindings } => {
                let bindings_obj = js_sys::Object::new();
                for (var, term) in bindings.into_iter() {
                    js_sys::Reflect::set(&bindings_obj, &var.into(), &term.into()).unwrap();
                }
                JsLeafAnswer::new(bindings_obj).into()
            }
        }
    }
}

impl From<Term> for JsValue {
    fn from(term: Term) -> JsValue {
        match term {
            Term::Integer(i) => JsPrologInteger::new(&i.to_string()).into(),
            Term::Rational(r) => {
                JsPrologRational::new(&r.numerator().to_string(), &r.denominator().to_string())
                    .into()
            }
            Term::Float(f) => JsPrologFloat::new(f).into(),
            Term::Atom(a) => JsPrologAtom::new(&a).into(),
            Term::String(s) => JsPrologString::new(&s).into(),
            Term::List(l) => JsPrologList::new(l.into_iter().map(JsValue::from).collect()).into(),
            Term::Compound(functor, args) => {
                JsPrologCompound::new(&functor, args.into_iter().map(JsValue::from).collect())
                    .into()
            }
            Term::Var(v) => JsPrologVariable::new(&v).into(),
        }
    }
}
