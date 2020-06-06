#![allow(dead_code)]

use std::error::Error;

const MAX_MEMORY_SIZE: usize = 65536;
type Memory = [u8; MAX_MEMORY_SIZE];
type Address = u16;

const NMI_VECTOR: Address = 0xFFFA;
const RESET_VECTOR: Address = 0xFFFC;
const IRQ_VECTOR: Address = 0xFFFE;

const ADDRESS_MODE_MASK: u8 = 0b0001_1100;

type Register8 = u8;
type Register16 = u16;
type Opcode = u8;
type Operand = Vec<u8>;

struct Processor {
    a: Register8,   // Accumulator
    x: Register8,   // X index
    y: Register8,   // Y index
    p: Register8,   // Processor status
    pc: Register16, // Program counter
    sp: Register8,  // Stack pointer
    ir: Opcode,     // Instruction register
    memory: Memory, // One big flat space for now
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
            p: 0b0010_0000, // 6th bit is always 1
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
            (self.memory[RESET_VECTOR as usize + 1] as u16).wrapping_shl(8)
                + self.memory[RESET_VECTOR as usize] as u16,
        );
    }

    // Move the Program Counter to the next location
    fn increment_pc(&mut self) {
        self.pc = self.pc.overflowing_add(1).0;
    }

    // Set the value of the A register
    fn set_a(&mut self, value: u8) {
        self.a = value;
    }

    // Set the value of the X register
    fn set_x(&mut self, value: u8) {
        self.x = value;
    }

    // Set the value of the Y register
    fn set_y(&mut self, value: u8) {
        self.y = value;
    }

    // Get the value of the A register
    fn get_a(&mut self) -> u8 {
        self.a
    }

    // Get the value of the X register
    fn get_x(&mut self) -> u8 {
        self.x
    }

    // Get the value of the Y register
    fn get_y(&mut self) -> u8 {
        self.y
    }

    // Fetches the next opcode and operand
    fn fetch(&mut self) -> Result<(Opcode, Operand), Box<dyn Error>> {
        let opcode = self.next().unwrap();
        let mut operand = Vec::new();

        // Handle exceptional cases
        match opcode {
            0x40 | 0x60 | 0xEA => return Ok((opcode, operand)),
            0x20 | 0xA0 | 0xC0 | 0xE0 => {
                operand.push(self.next().unwrap());
                return Ok((opcode, operand))
            },
            _ => {},    // pass through to next set of cases
        };

        // Handle the happy cases
        match opcode & ADDRESS_MODE_MASK {
            0b0000_0000 | 0b0000_0100 | 0b0000_1000 | 0b0001_0000 |  0b0001_0100 => {
                operand.push(self.next().unwrap());
            },
            0b0000_1100 | 0b0001_1100 => {
                operand.push(self.next().unwrap());
                operand.push(self.next().unwrap());
            },
            _ => {},    // 1 byte opcodes
        };
        Ok((opcode, operand))
    }

    // Execute the given opcode
    fn execute(&mut self, opcode: Opcode, operand: Operand) -> Option<()> {
        match opcode {
            // ADC
            0x69 => {Some(())},
            0x65 => {Some(())},
            0x75 => {Some(())},
            0x6D => {Some(())},
            0x7D => {Some(())},
            0x79 => {Some(())},
            0x61 => {Some(())},
            0x71 => {Some(())},

            // AND
            0x29 => {Some(())},
            0x25 => {Some(())},
            0x35 => {Some(())},
            0x2D => {Some(())},
            0x3D => {Some(())},
            0x39 => {Some(())},
            0x21 => {Some(())},
            0x31 => {Some(())},

            // ASL
            0x0A => {Some(())},
            0x06 => {Some(())},
            0x16 => {Some(())},
            0x0E => {Some(())},
            0x1E => {Some(())},

            // BCC
            0x90 => {Some(())},

            // BCS
            0xB0 => {Some(())},

            // BEQ
            0xF0 => {Some(())},

            // BIT
            0x24 => {Some(())},
            0x2C => {Some(())},

            // BMI
            0x30 => {Some(())},

            // BNE
            0xD0 => {Some(())},

            // BPL
            0x10 => {Some(())},

            // BRK
            0x00 => {Some(())},

            // BVC
            0x50 => {Some(())},

            // BVS
            0x70 => {Some(())},

            // CLC
            0x18 => {Some(())},

            // CLD
            0xD8 => {Some(())},

            // CLI
            0x58 => {Some(())},

            // CLV
            0xB8 => {Some(())},

            // CMP
            0xC9 => {Some(())},
            0xC5 => {Some(())},
            0xD5 => {Some(())},
            0xCD => {Some(())},
            0xDD => {Some(())},
            0xD9 => {Some(())},
            0xC1 => {Some(())},
            0xD1 => {Some(())},

            // CPX
            0xE0 => {Some(())},
            0xE4 => {Some(())},
            0xEC => {Some(())},

            // CPY
            0xC0 => {Some(())},
            0xC4 => {Some(())},
            0xCC => {Some(())},

            // DEC
            0xC6 => {Some(())},
            0xD6 => {Some(())},
            0xCE => {Some(())},
            0xDE => {Some(())},

            // DEX
            0xCA => {Some(())},

            // DEY
            0x88 => {Some(())},

            // EOR
            0x49 => {Some(())},
            0x45 => {Some(())},
            0x55 => {Some(())},
            0x4D => {Some(())},
            0x5D => {Some(())},
            0x59 => {Some(())},
            0x41 => {Some(())},
            0x51 => {Some(())},

            // INC
            0xE6 => {Some(())},
            0xF6 => {Some(())},
            0xEE => {Some(())},
            0xFE => {Some(())},

            // INX
            0xE8 => {Some(())},

            // INY
            0xC8 => {Some(())},

            // JMP
            0x4C => {Some(())},
            0x6C => {Some(())},

            // JSR
            0x20 => {Some(())},

            // LDA
            0xA9 => {
                self.set_a(operand[0]);
                Some(())
            },
            0xA5 | 0xAD => {
                let value = self.get_memory_value(bytes_to_u16(operand));
                self.set_a(value);
                Some(())
            },
            0xB5 => {
                let x = self.get_x() as u16;
                let value = self.get_memory_value(bytes_to_u16(operand).overflowing_add(x).0);
                self.set_a(value);
                Some(())
            },
            0xBD => {
                let x = self.get_x() as u16;
                let value = self.get_memory_value(bytes_to_u16(operand).overflowing_add(x).0);
                self.set_a(value);
                Some(())
            },
            0xB9 => {Some(())},
            0xA1 => {Some(())},
            0xB1 => {Some(())},

            // LDX
            0xA2 => {Some(())},
            0xA6 => {Some(())},
            0xB6 => {Some(())},
            0xAE => {Some(())},
            0xBE => {Some(())},

            // LSR
            0xA0 => {Some(())},
            0xA4 => {Some(())},
            0xB4 => {Some(())},
            0xAC => {Some(())},
            0xBC => {Some(())},

            // NOP
            0xEA => Some(()),

            // ORA
            0x09 => {Some(())},
            0x05 => {Some(())},
            0x15 => {Some(())},
            0x0D => {Some(())},
            0x1D => {Some(())},
            0x19 => {Some(())},
            0x01 => {Some(())},
            0x11 => {Some(())},

            // PHA
            0x48 => {Some(())},

            // PHP
            0x08 => {Some(())},

            // PLA
            0x68 => {Some(())},

            // PLP
            0x28 => {Some(())},

            // ROL
            0x2A => {Some(())},
            0x26 => {Some(())},
            0x36 => {Some(())},
            0x2E => {Some(())},
            0x3E => {Some(())},

            // ROR
            0x6A => {Some(())},
            0x66 => {Some(())},
            0x76 => {Some(())},
            0x6E => {Some(())},
            0x7E => {Some(())},

            // RTI
            0x40 => {Some(())},

            // RTS
            0x60 => {Some(())},

            // SBC
            0xE9 => {Some(())},
            0xE5 => {Some(())},
            0xF5 => {Some(())},
            0xED => {Some(())},
            0xFD => {Some(())},
            0xF9 => {Some(())},
            0xE1 => {Some(())},
            0xF1 => {Some(())},

            // SEC
            0x38 => {Some(())},

            // SED
            0xF8 => {Some(())},

            // SEI
            0x78 => {Some(())},

            // STA
            0x85 => {Some(())},
            0x95 => {Some(())},
            0x8D => {Some(())},
            0x9D => {Some(())},
            0x99 => {Some(())},
            0x81 => {Some(())},
            0x91 => {Some(())},

            // STP (WDC 65c02)
            0xDB => None,

            // STX
            0x86 => {Some(())},
            0x96 => {Some(())},
            0x8E => {Some(())},

            // STY
            0x84 => {Some(())},
            0x94 => {Some(())},
            0x8C => {Some(())},

            // TAX
            0xAA => {Some(())},

            // TAY
            0xA8 => {Some(())},

            // TSX
            0xBA => {Some(())},

            // TXA
            0x8A => {Some(())},

            // TXS
            0x9A => {Some(())},

            // TYA
            0x98 => {Some(())},

            _ => panic!("Unknown opcode {}", opcode),
        }
    }

    // Retrieve the memory value at the given address
    fn get_memory_value(&mut self, address: u16) -> u8 {
        self.memory[address as usize]
    }
}

// Returns a u16 of the first two little endian bytes
fn bytes_to_u16(bytes: Vec<u8>) -> u16 {
    if bytes.len() == 1 {
        bytes[0] as u16
    } else {
        (bytes[1] as u16).wrapping_shl(8) + bytes[0] as u16
    }
}

impl Iterator for Processor {
    type Item = u8;

    fn next(&mut self) -> Option<u8> {
        let val = self.get_memory_value(self.pc);
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
    use super::bytes_to_u16;
    use super::Processor;
    use super::DECIMAL_MODE;
    use super::INTERRUPT_DISABLE;
    use super::RESET_VECTOR;

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
        p.memory[0x1234] = 0xEA; // NOP
        p.memory[0x1235] = 0xEA; // NOP
        p.memory[0x1236] = 0xDB; // STP
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
        p.memory[0x1234] = 0xEA; // NOP
        p.memory[0x1235] = 0xDB; // STP
        p.memory[0x1236] = 0xA9; // LDA #
        p.memory[0x1237] = 0x34; // Lo byte
        p.memory[0x1238] = 0x12; // Hi byte
        p.reset();
        let a = p.a;
        let x = p.x;
        let y = p.y;
        let ps = p.p;
        let sp = p.sp;
        let opcode = p.next().unwrap();
        let operand = Vec::new();
        assert_eq!(p.execute(opcode, operand), Some(()));
        assert_eq!(p.a, a);
        assert_eq!(p.x, x);
        assert_eq!(p.y, y);
        assert_eq!(p.p, ps);
        assert_eq!(p.sp, sp);
        assert_eq!(p.pc, 0x1235);
        let opcode = p.next().unwrap();
        let operand = Vec::new();
        assert_eq!(p.execute(opcode, operand), None);
    }

    #[test]
    fn test_fetch() {
        let mut p = Processor::new();
        p.memory[0xFFFC] = 0x34;
        p.memory[0xFFFD] = 0x12;
        p.memory[0x1234] = 0xEA; // NOP
        p.memory[0x1235] = 0xDB; // STP
        p.memory[0x1236] = 0xAD; // LDA $
        p.memory[0x1237] = 0x34; // Lo byte
        p.memory[0x1238] = 0x12; // Hi byte
        p.reset();
        let (opcode, operand) = p.fetch().unwrap();
        assert_eq!(opcode, 0xEA);
        assert_eq!(operand.len(), 0);
        let (opcode, operand) = p.fetch().unwrap();
        assert_eq!(opcode, 0xDB);
        assert_eq!(operand.len(), 0);
        let (opcode, operand) = p.fetch().unwrap();
        assert_eq!(opcode, 0xAD);
        assert_eq!(operand[0], 0x34);
        assert_eq!(operand[1], 0x12);
        assert_eq!(p.pc, 0x1239);
    }

    #[test]
    fn test_fetch_and_execute() {
        let mut p = Processor::new();
        p.memory[0xFFFC] = 0x34;
        p.memory[0xFFFD] = 0x12;
        p.memory[0x1234] = 0xAD; // LDA #
        p.memory[0x1235] = 0x34; // Lo byte
        p.memory[0x1236] = 0x12; // Hi byte
        p.memory[0x1237] = 0xEA; // NOP
        p.reset();
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.a, 0xAD); // We're loading the value at 0x1234 into A
        let (opcode, operand) = p.fetch().unwrap();
        assert_eq!(opcode, 0xEA);
        assert_eq!(operand.len(), 0);
    }

    #[test]
    fn test_bytes_to_u16() {
        assert_eq!(bytes_to_u16(vec![0xAB]), 0xAB);
        assert_eq!(bytes_to_u16(vec![0x34, 0x12]), 0x1234);
    }

    #[test]
    fn get_memory_value() {
        let mut p = Processor::new();
        p.memory[0x1234] = 0xAB;
        assert_eq!(p.get_memory_value(0x1234), 0xAB);
    }

    #[test]
    fn test_lda() {
        let mut p = Processor::new();
        p.memory[0xFFFC] = 0x34;
        p.memory[0xFFFD] = 0x12;
        p.memory[0x1234] = 0xAD; // LDA $
        p.memory[0x1235] = 0x34; // Lo byte
        p.memory[0x1236] = 0x12; // Hi byte
        p.reset();
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.a, 0xAD); // We're loading the value at 0x1234 into A

        p.memory[0x1237] = 0xA9; // LDA #
        p.memory[0x1238] = 0xDE;
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.a, 0xDE);

        p.memory[0x0001] = 0x56; // LDA zp
        p.memory[0x1239] = 0xA5;
        p.memory[0x123A] = 0x01;
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.a, 0x56);

        p.memory[0x001A] = 0x67; // LDA zp,X
        p.memory[0x123B] = 0xB5;
        p.memory[0x123C] = 0x10;
        p.set_x(0x0A);
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.a, 0x67);

        p.memory[0x1005] = 0x78; // LDA $,x
        p.memory[0x123D] = 0xBD;
        p.memory[0x123E] = 0x00;
        p.memory[0x123F] = 0x10;
        p.set_x(0x05);
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.a, 0x78);
    }
}
