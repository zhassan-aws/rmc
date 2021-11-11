#![feature(asm)]
fn foo() {
    unsafe {
        asm!("nop");
    }
}

#[no_mangle]
fn main() {
    foo();
    assert!(1 + 1 == 3);
}
