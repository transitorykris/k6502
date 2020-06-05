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
const NEGATIVE_FLAG: u8 = 0b1000_0000;
const OVERFLOW_FLAG: u8 = 0b0100_0000;
const BRK_FLAG: u8 = 0b0001_0000;
const DECIMAL_MODE: u8 = 0b0000_1000;
const INTERRUPT_DISABLE: u8 = 0b0000_0100;
const ZERO_FLAG: u8 = 0b0000_0010;
const CARRY_FLAG: u8 = 0b0000_0001;

impl Processor {
    fn new() -> Processor {
        Processor {
            a: 0x00,
            x: 0x00,
            y: 0x00,
            p: 0b0010_0000,  // 6th bit is always 1
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
        self.p &= !DECIMAL_MODE;
        self.p &= !INTERRUPT_DISABLE;
    }

    // Performs a reset on the processor
    fn reset(&mut self) {
        self.move_pc(
            (self.memory[RESET_VECTOR as usize + 1] as u16).wrapping_shl(8) +
            self.memory[RESET_VECTOR as usize] as u16
        );
    }

    // Move the Program Counter to the next location
    fn increment_pc(&mut self) {
        self.pc = self.pc.overflowing_add(1).0;
    }

    // Fetches the next opcode and operand
    fn fetch(&mut self) -> Result<(Instruction, Vec<u8>), Box<dyn Error>> {
        let opcode = self.next().unwrap();
        match opcode {
            0xEA => { // NOP
                Ok((0xEA, Vec::new()))
            },
            0xDB => { // STP
                Ok((0xDB, Vec::new()))
            }
            _ => {
                panic!("Unknown opcode {}", opcode);
            }
        }
    }

    // Execute the given opcode
    fn execute(&mut self, opcode: Instruction) -> Option<()> {
        match opcode {
            0xEA => { // NOP
                Some(())
            },
            0xDB => { // STP
                None
            },
            _ => {
                panic!("Unknown opcode {}", opcode);
            }
        }
    }
}

impl Iterator for Processor {
    type Item = u8;

    fn next(&mut self) -> Option<u8> {
        let val = self.memory[self.pc as usize];
        self.increment_pc();        
        Some(val)
    }
}

pub fn run() -> Result<(), Box<dyn Error>> {
    let mut _p = Processor::new();

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
        assert_eq!(p.p, 0b00100000);
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

    #[test]
    fn test_processor_next() {
        let mut p = Processor::new();
        p.memory[RESET_VECTOR as usize] = 0x34;
        p.memory[RESET_VECTOR as usize + 1] = 0x12;
        p.memory[0x1234] = 0xab;
        p.reset();
        assert_eq!(p.next().unwrap(), 0xab);
        assert_eq!(p.pc, 0x1235);
    }

    #[test]
    fn test_increment_pc() {
        let mut p = Processor::new();
        p.increment_pc();
        assert_eq!(p.pc, 0x0001);
        // Make sure we wrap around to 0x0000
        p.pc = u16::MAX;
        p.increment_pc();
        assert_eq!(p.pc, 0x0000);
    }

    #[test]
    fn test_simple_code() {
        let mut p = Processor::new();
        p.memory[0xFFFC] = 0x34;
        p.memory[0xFFFD] = 0x12;
        p.memory[0x1234] = 0xEA;    // NOP
        p.memory[0x1235] = 0xEA;    // NOP
        p.memory[0x1236] = 0xDB;    // STP
        p.reset();
        assert_eq!(p.next().unwrap(), 0xEA);
        assert_eq!(p.next().unwrap(), 0xEA);
        assert_eq!(p.next().unwrap(), 0xDB);
        assert_eq!(p.pc, 0x1237);
    }

    #[test]
    fn test_execute() {
        let mut p = Processor::new();
        p.memory[0xFFFC] = 0x34;
        p.memory[0xFFFD] = 0x12;
        p.memory[0x1234] = 0xEA;    // NOP
        p.memory[0x1235] = 0xDB;    // STP
        p.reset();
        let a = p.a;
        let x = p.x;
        let y = p.y;
        let ps = p.p;
        let sp = p.sp;
        let opcode = p.next().unwrap();
        assert_eq!(p.execute(opcode), Some(()));
        assert_eq!(p.a, a);
        assert_eq!(p.x, x);
        assert_eq!(p.y, y);
        assert_eq!(p.p, ps);
        assert_eq!(p.sp, sp);
        assert_eq!(p.pc, 0x1235);
        let opcode = p.next().unwrap();
        assert_eq!(p.execute(opcode), None);
    }

    #[test]
    fn test_fetch() {
        let mut p = Processor::new();
        p.memory[0xFFFC] = 0x34;
        p.memory[0xFFFD] = 0x12;
        p.memory[0x1234] = 0xEA;    // NOP
        p.memory[0x1235] = 0xDB;    // STP
        p.reset();
        let (opcode, operand) = p.fetch().unwrap();
        assert_eq!(opcode, 0xEA);
        assert_eq!(operand.len(), 0);
        let (opcode, operand) = p.fetch().unwrap();
        assert_eq!(opcode, 0xDB);
        assert_eq!(operand.len(), 0);
    }
}
