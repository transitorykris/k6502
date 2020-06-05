#[test]
fn test_run() {
    if k6502::run().is_err() {
        panic!("Unexpected error");
    }
}