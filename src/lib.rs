use std::error::Error;

pub fn run() -> Result<(), Box<dyn Error>> {
    println!("Hello k6502!");

    Ok(())
}