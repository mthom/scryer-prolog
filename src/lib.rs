#![recursion_limit = "4112"]

#[macro_use]
extern crate static_assertions;

#[macro_use]
pub mod macros;
#[macro_use]
pub mod atom_table;
#[macro_use]
pub mod arena;
#[macro_use]
pub mod parser;
mod allocator;
mod arithmetic;
pub mod codegen;
mod debray_allocator;
#[cfg(feature = "ffi")]
mod ffi;
mod variable_records;
mod forms;
mod heap_iter;
pub mod heap_print;
#[cfg(feature = "http")]
mod http;
mod indexing;
#[macro_use]
pub mod instructions {
    include!(concat!(env!("OUT_DIR"), "/instructions.rs"));
}
mod iterators;
pub mod machine;
mod raw_block;
pub mod read;
#[cfg(feature = "repl")]
mod repl_helper;
mod targets;
pub mod types;

use instructions::instr;

use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn eval_code(s: &str) -> String {
    use web_sys::console;
    console::log_1(&"Rust got code: ".into());
    console::log_1(&s.into());

    use machine::mock_wam::*;

    let mut wam = Machine::with_test_streams();
    let bytes = wam.test_load_string(s);
    String::from_utf8_lossy(&bytes).to_string()
}

//"env"."LIMBS_are_zero": [I32, I32] -> [I32]
#[wasm_bindgen]
pub fn LIMBS_are_zero(a: i32, b: i32) -> i32 {
    a + b
}

//"env"."GFp_ChaCha20_ctr32": [I32, I32, I32, I32, I32] -> []
#[wasm_bindgen]
pub fn GFp_ChaCha20_ctr32(a: i32, b: i32, c: i32, d: i32, e: i32) {
}

//"env"."LIMBS_less_than": [I32, I32, I32] -> [I32]
#[wasm_bindgen]
pub fn LIMBS_less_than(a: i32, b: i32, c: i32) -> i32 {
    a
}

//"env"."GFp_memcmp": [I32, I32, I32] -> [I32]
#[wasm_bindgen]
pub fn GFp_memcmp(a: i32, b: i32, c: i32) -> i32 {
    a
}

//"env"."GFp_poly1305_finish": [I32, I32] -> []
#[wasm_bindgen]
pub fn GFp_poly1305_finish(a: i32, b: i32) {
}

//"env"."GFp_poly1305_init": [I32, I32] -> []
#[wasm_bindgen]
pub fn GFp_poly1305_init(a: i32, b: i32) {
}

//"env"."GFp_poly1305_update": [I32, I32, I32] -> []
#[wasm_bindgen]
pub fn GFp_poly1305_update(a: i32, b: i32, c: i32) {
}

//"env"."GFp_x25519_ge_frombytes_vartime": [I32, I32] -> [I32]
#[wasm_bindgen]
pub fn GFp_x25519_ge_frombytes_vartime(a: i32, b: i32) -> i32 {
    a + b
}

//"env"."GFp_x25519_fe_neg": [I32] -> []
#[wasm_bindgen]
pub fn GFp_x25519_fe_neg(a: i32) {
}

//"env"."GFp_x25519_sc_reduce": [I32] -> []
#[wasm_bindgen]
pub fn GFp_x25519_sc_reduce(a: i32) {
}

//"env"."GFp_x25519_ge_double_scalarmult_vartime": [I32, I32, I32, I32] -> []
#[wasm_bindgen]
pub fn GFp_x25519_ge_double_scalarmult_vartime(a: i32, b: i32, c: i32, d: i32) {
}

//"env"."GFp_x25519_fe_invert": [I32, I32] -> []
#[wasm_bindgen]
pub fn GFp_x25519_fe_invert(a: i32, b: i32) {
}

//"env"."GFp_x25519_fe_mul_ttt": [I32, I32, I32] -> []
#[wasm_bindgen]
pub fn GFp_x25519_fe_mul_ttt(a: i32, b: i32, c: i32) {
}

//"env"."GFp_x25519_fe_tobytes": [I32, I32] -> []
#[wasm_bindgen]
pub fn GFp_x25519_fe_tobytes(a: i32, b: i32) {
}

//"env"."GFp_x25519_fe_isnegative": [I32] -> [I32]
#[wasm_bindgen]
pub fn GFp_x25519_fe_isnegative(a: i32) -> i32 {
    a
}

//"env"."GFp_x25519_sc_mask": [I32] -> []
#[wasm_bindgen]
pub fn GFp_x25519_sc_mask(a: i32) {
}

//"env"."GFp_x25519_ge_scalarmult_base": [I32, I32] -> []
#[wasm_bindgen]
pub fn GFp_x25519_ge_scalarmult_base(a: i32, b: i32) {
}

//"env"."GFp_x25519_sc_muladd": [I32, I32, I32, I32] -> []
#[wasm_bindgen]
pub fn GFp_x25519_sc_muladd(a: i32, b: i32, c: i32, d: i32) {
}
