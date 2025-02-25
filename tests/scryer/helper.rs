use scryer_prolog::MachineBuilder;

pub(crate) trait Expectable {
    #[track_caller]
    fn assert_eq(self, other: &[u8]);
}

impl Expectable for &str {
    #[track_caller]
    fn assert_eq(self, other: &[u8]) {
        if let Ok(other_str) = std::str::from_utf8(other) {
            assert_eq!(other_str, self)
        } else {
            // should always fail as other is not valid utf-8 but self is
            // just for consistent assert error message
            assert_eq!(other, self.as_bytes())
        }
    }
}

impl Expectable for &[u8] {
    #[track_caller]
    fn assert_eq(self, other: &[u8]) {
        assert_eq!(other, self)
    }
}

/// Tests whether the file can be successfully loaded
/// and produces the expected output during it
pub(crate) fn load_module_test<T: Expectable>(file: &str, expected: T) {
    use scryer_prolog::MachineBuilder;

    let mut wam = MachineBuilder::default().build();
    expected.assert_eq(wam.test_load_file(file).as_slice());
}

pub(crate) fn load_module_test_with_tokio_runtime<T: Expectable>(file: &str, expected: T) {
    #[cfg(not(target_arch = "wasm32"))]
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .unwrap();

    runtime.block_on(async move {
        let mut wam = MachineBuilder::default().build();
        expected.assert_eq(wam.test_load_file(file).as_slice())
    });
}
