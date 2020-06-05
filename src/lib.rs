#![allow(dead_code)]

use std::error::Error;

const MAX_MEMORY_SIZE: usize = 65536;
type Memory = [u8; MAX_MEMORY_SIZE];

const NMI_VECTOR: u16 = 0xFFFA;
const RESET_VECTOR: u16 = 0xFFFC;
const IRQ_VECTOR: u16 = 0xFFFE;

type Register8 = u8;
type Register16 = u16;
type Instruction = u8;

struct Processor {
    a: Register8,       // Accumulator
    x: Register8,       // X index
    y: Register8,       // Y index
    p: Register8,       // Processor status
    pc: Register16,     // Program counter
    sp: Register8,      // Stack pointer
    ir: Instruction,    // Instruction register
    memory: Memory,     // One big flat space for now
}

impl Processor {
    fn new() -> Processor {
        Processor {
            a: 0x00,
            x: 0x00,
            y: 0x00,
            p: 0x00,
            pc: 0x0000,
            sp: 0x00,
            ir: 0x00,
            memory: [0x00; MAX_MEMORY_SIZE],
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
        assert_eq!(p.p, 0x00);
        assert_eq!(p.pc, 0x0000);
        assert_eq!(p.sp, 0x00);
        assert_eq!(p.ir, 0x00);
        for l in p.memory.iter() {
            assert_eq!(*l, 0x00);
        }
    }
}