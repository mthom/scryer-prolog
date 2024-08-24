use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn eval_code(s: &str) -> String {
    use machine::mock_wam::*;

    console_error_panic_hook::set_once();

    let mut wam = Machine::with_test_streams();
    let bytes = wam.test_load_string(s);
    String::from_utf8_lossy(&bytes).to_string()
}
