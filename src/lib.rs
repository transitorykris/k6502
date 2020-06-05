#![allow(dead_code)]

use std::error::Error;

const MAX_MEMORY_SIZE: usize = 65536;
type Memory = [u8; MAX_MEMORY_SIZE];
type Address = u16;

const NMI_VECTOR: Address = 0xFFFA;
const RESET_VECTOR: Address = 0xFFFC;
const IRQ_VECTOR: Address = 0xFFFE;

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

// Processor status register flags
const NEGATIVE_FLAG: u8 = 0b10000000;
const OVERFLOW_FLAG: u8 = 0b01000000;
const BRK_FLAG: u8 = 0b00010000;
const DECIMAL_MODE: u8 = 0b00001000;
const INTERRUPT_DISABLE: u8 = 0b00000100;
const ZERO_FLAG: u8 = 0b00000010;
const CARRY_FLAG: u8 = 0b00000001;

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

    fn move_pc(&mut self, address: Address) {
        self.pc = address;
    }

    // Performs a hardware reset of the Processor Status Register (p)
    // Only the Decimal and Interrupt disable mode select bits are affected
    fn reset_p(&mut self) {
        self.p = self.p & !DECIMAL_MODE;
        self.p = self.p & !INTERRUPT_DISABLE;
    }

    // Performs a reset on the processor
    fn reset(&mut self) {
        self.move_pc(
            (self.memory[RESET_VECTOR as usize + 1] as u16).wrapping_shl(8) +
            self.memory[RESET_VECTOR as usize] as u16
        );
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
    use super::RESET_VECTOR;
    use super::DECIMAL_MODE;
    use super::INTERRUPT_DISABLE;

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

    #[test]
    fn test_move_pc() {
        let mut p = Processor::new();
        p.move_pc(0x1234);
        assert_eq!(p.pc, 0x1234);
    }

    #[test]
    fn test_reset_p() {
        let mut p = Processor::new();
        p.p = 0xFF;
        p.reset_p();
        assert_eq!(p.p & DECIMAL_MODE, 0);
        assert_eq!(p.p & INTERRUPT_DISABLE, 0);
    }

    #[test]
    fn test_reset() {
        let mut p = Processor::new();
        p.memory[RESET_VECTOR as usize] = 0x34;
        p.memory[RESET_VECTOR as usize + 1] = 0x12;
        p.reset();
        assert_eq!(p.pc, 0x1234);
    }
}