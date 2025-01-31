fn main() -> std::process::ExitCode {
    #[cfg(target_arch = "wasm32")]
    return std::process::ExitCode::SUCCESS;

    #[cfg(not(target_arch = "wasm32"))]
    return scryer_prolog::run_binary();
}
