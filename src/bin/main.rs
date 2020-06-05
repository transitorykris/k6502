use k6502::run;

fn main() {
    println!("Hello k6502!");

    match run() {
        Ok(_) => println!("Processor halted normally"),
        Err(_) => println!("Processor halted abnormally"),
    }
}
