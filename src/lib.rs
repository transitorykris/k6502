use std::error::Error;

type Register8 = u8;
type Register16 = u16;
type Instruction = u8;

pub struct Processor {
    a: Register8,       // Accumulator
    x: Register8,       // X index
    y: Register8,       // Y index
    p: Register8,       // Processor status
    pc: Register16,     // Program counter
    sp: Register8,      // Stack pointer
    ir: Instruction,    // Instruction register
}

impl Processor {
    pub fn new() -> Processor {
        Processor {
            a: 0x00,
            x: 0x00,
            y: 0x00,
            p: 0x00,
            pc: 0x0000,
            sp: 0x00,
            ir: 0x00,
        }
    }
}

pub fn run() -> Result<(), Box<dyn Error>> {
    println!("Hello k6502!");

    let _p = Processor::new();

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::Processor;

    #[test]
    fn test_default_processor() {
        let p = Processor::new();
        assert_eq!(p.a, 0x00);
        assert_eq!(p.x, 0x00);
        assert_eq!(p.y, 0x00);
    }
}