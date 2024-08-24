#[cfg(not(target_arch = "wasm32"))]
pub mod shared_library;
#[cfg(target_arch = "wasm32")]
pub mod wasm;
