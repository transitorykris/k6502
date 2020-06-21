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

    // Set the stack pointer
    fn set_sp(&mut self, sp: u8) {
        self.sp = sp;
    }

    // Get the stack pointer
    fn get_sp(&mut self) -> u8 {
        self.sp
    }

    // Manipulate processor status flags
    fn set_negative(&mut self) {
        self.p |= NEGATIVE_FLAG;
    }

    fn clear_negative(&mut self) {
        self.p &= !NEGATIVE_FLAG;
    }

    fn is_negative(&mut self) -> bool {
        if self.p & NEGATIVE_FLAG == NEGATIVE_FLAG {
            return true
        }
        false
    }

    fn test_and_set_negative(&mut self, value: u8) -> bool {
        if value & 0b1000_0000 == 0b1000_0000 {
            self.set_negative();
            return true
        }
        false
    }

    fn set_overflow(&mut self) {
        self.p |= OVERFLOW_FLAG;
    }

    fn clear_overflow(&mut self) {
        self.p &= !OVERFLOW_FLAG;
    }

    fn is_overflow(&mut self) -> bool {
        if self.p & OVERFLOW_FLAG == OVERFLOW_FLAG {
            return true
        }
        false
    }

    fn set_brk(&mut self) {
        self.p |= BRK_FLAG;
    }

    fn clear_brk(&mut self) {
        self.p &= !BRK_FLAG;
    }

    fn is_brk(&mut self) -> bool {
        if self.p & BRK_FLAG == BRK_FLAG {
            return true
        }
        false
    }

    fn set_decimal(&mut self) {
        self.p |= DECIMAL_MODE;
    }

    fn clear_decimal(&mut self) {
        self.p &= !DECIMAL_MODE;
    }

    fn is_decimal(&mut self) -> bool {
        if self.p & DECIMAL_MODE == DECIMAL_MODE {
            return true
        }
        false
    }

    fn set_interrupt_disable(&mut self) {
        self.p |= INTERRUPT_DISABLE;
    }

    fn clear_interrupt_disable(&mut self) {
        self.p &= !INTERRUPT_DISABLE;
    }

    fn is_interrupt_disable(&mut self) -> bool {
        if self.p & INTERRUPT_DISABLE == INTERRUPT_DISABLE {
            return true
        }
        false
    }

    fn set_zero(&mut self) {
        self.p |= ZERO_FLAG;
    }

    fn clear_zero(&mut self) {
        self.p &= !ZERO_FLAG;
    }

    fn is_zero(&mut self) -> bool {
        if self.p & ZERO_FLAG == ZERO_FLAG {
            return true
        }
        false
    }

    fn test_and_set_zero(&mut self, value: u8) -> bool {
        if value == 0 {
            self.set_zero();
            return true
        }
        false
    }

    fn set_carry(&mut self) {
        self.p |= CARRY_FLAG;
    }

    fn clear_carry(&mut self) {
        self.p &= !CARRY_FLAG;
    }
    
    fn is_carry(&mut self) -> bool {
        if self.p & CARRY_FLAG == CARRY_FLAG {
            return true
        }
        false
    }

    // Fetches the next opcode and operand
    fn fetch(&mut self) -> Result<(Opcode, Operand), Box<dyn Error>> {
        let opcode = self.next().unwrap();
        let mut operand = Vec::new();

        // Handle exceptional cases
        match opcode {
            0xAA | 0xA8 | 0xBA | 0x88 | 0x8A | 0x9A | 0x98 |
            0x40 | 0x60 | 0xDB | 0xEA | 0xE8 | 0xCA |
            0xC8 => {
                return Ok((opcode, operand))
            }
            0x20 | 0xA0 | 0xC0 | 0xE0 => {
                operand.push(self.next().unwrap());
                return Ok((opcode, operand))
            },
            0xB9 => {
                operand.push(self.next().unwrap());
                operand.push(self.next().unwrap());
                return Ok((opcode, operand))
            },
            _ => {},    // pass through to next set of cases
        };

        // Handle the happy cases
        match opcode & ADDRESS_MODE_MASK {
            0b0000_0000 | 0b0000_0100 | 0b0000_1000 | 0b0001_0000 |
            0b0001_0100 => {
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
            0x69 => {},
            0x65 => {},
            0x75 => {},
            0x6D => {},
            0x7D => {},
            0x79 => {},
            0x61 => {},
            0x71 => {},

            // AND
            0x29 => {},
            0x25 => {},
            0x35 => {},
            0x2D => {},
            0x3D => {},
            0x39 => {},
            0x21 => {},
            0x31 => {},

            // ASL
            0x0A => {},
            0x06 => {},
            0x16 => {},
            0x0E => {},
            0x1E => {},

            // BCC
            0x90 => {},

            // BCS
            0xB0 => {},

            // BEQ
            0xF0 => {},

            // BIT
            0x24 => {},
            0x2C => {},

            // BMI
            0x30 => {},

            // BNE
            0xD0 => {},

            // BPL
            0x10 => {},

            // BRK
            0x00 => {},

            // BVC
            0x50 => {},

            // BVS
            0x70 => {},

            // CLC
            0x18 => self.clear_carry(),

            // CLD
            0xD8 => self.clear_decimal(),

            // CLI
            0x58 => self.clear_interrupt_disable(),

            // CLV
            0xB8 => self.clear_overflow(),

            // CMP
            0xC9 => {},
            0xC5 => {},
            0xD5 => {},
            0xCD => {},
            0xDD => {},
            0xD9 => {},
            0xC1 => {},
            0xD1 => {},

            // CPX
            0xE0 => {},
            0xE4 => {},
            0xEC => {},

            // CPY
            0xC0 => {},
            0xC4 => {},
            0xCC => {},

            // DEC
            0xC6 => {},
            0xD6 => {},
            0xCE => {},
            0xDE => {},

            // DEX
            0xCA => {
                self.set_x(self.x.overflowing_sub(1).0);
                self.clear_zero();
                self.clear_negative();
                if self.get_x() == 0x00 {
                    self.set_zero();
                } else if self.x & 0b1000_0000 == 0b1000_0000 {
                    self.set_negative();
                }
            },

            // DEY
            0x88 => {
                self.set_y(self.y.overflowing_sub(1).0);
                self.clear_zero();
                self.clear_negative();
                if self.get_y() == 0x00 {
                    self.set_zero();
                } else if self.y & 0b1000_0000 == 0b1000_0000 {
                    self.set_negative();
                }
            },

            // EOR
            0x49 => {},
            0x45 => {},
            0x55 => {},
            0x4D => {},
            0x5D => {},
            0x59 => {},
            0x41 => {},
            0x51 => {},

            // INC
            0xE6 => {},
            0xF6 => {},
            0xEE => {},
            0xFE => {},

            // INX
            // BUG! Fix me -- zero should be set not overflow
            0xE8 => {
                self.x = self.x.overflowing_add(1).0;
                if self.x == 0 {
                    self.set_zero();
                } else if self.x & 0b1000_0000 == 0b1000_0000 {
                    self.set_negative();
                }
            },

            // INY
            // BUG! Fix me -- zero should be set not overflow
            0xC8 => {
                self.y = self.y.overflowing_add(1).0;
                if self.y == 0 {
                    self.set_zero();
                } else if self.y & 0b1000_0000 == 0b1000_0000 {
                    self.set_negative();
                }
            },

            // JMP
            0x4C => self.pc = bytes_to_u16(operand),
            0x6C => {
                let indirect = bytes_to_u16(operand);
                let addr_lo = self.memory[indirect as usize];
                let addr_hi = self.memory[(indirect + 1) as usize];
                let address = bytes_to_u16(vec![addr_lo, addr_hi]);
                self.pc = address;
            },

            // JSR
            0x20 => {},

            // LDA
            0xA9 => self.set_a(operand[0]),
            0xA5 | 0xAD => {
                let value = self.get_memory_value(bytes_to_u16(operand));
                self.set_a(value);
            },
            0xB5 => {
                let x = self.get_x();
                let address = operand[0].overflowing_add(x).0 as u16;
                let value = self.get_memory_value(address);
                self.set_a(value);
            },
            0xBD => {
                let x = self.get_x() as u16;
                let address = bytes_to_u16(operand).overflowing_add(x).0;
                let value = self.get_memory_value(address);
                self.set_a(value);
            },
            0xB9 => {            
                let y = self.get_y() as u16;
                let address = bytes_to_u16(operand).overflowing_add(y).0;
                let value = self.get_memory_value(address);
                self.set_a(value);
            },
            0xA1 => {
                let x = self.get_x();
                let table_address = operand[0].overflowing_add(x).0;
                let address = vec![
                    self.get_memory_value(table_address as u16),
                    self.get_memory_value((table_address+1) as u16)
                ];
                let value = self.get_memory_value(bytes_to_u16(address));
                self.set_a(value);
            },
            0xB1 => {
                let y = self.get_y();
                let base_address = vec![
                    self.get_memory_value(operand[0] as u16),
                    self.get_memory_value((operand[0] + 1) as u16)
                ];
                let address = bytes_to_u16(base_address) + y as u16;
                let value = self.get_memory_value(address);
                self.set_a(value);
            },

            // LDX
            0xA2 => {},
            0xA6 => {},
            0xB6 => {},
            0xAE => {},
            0xBE => {},

            // LSR
            0xA0 => {},
            0xA4 => {},
            0xB4 => {},
            0xAC => {},
            0xBC => {},

            // NOP
            0xEA => {},

            // ORA
            0x09 => {},
            0x05 => {},
            0x15 => {},
            0x0D => {},
            0x1D => {},
            0x19 => {},
            0x01 => {},
            0x11 => {},

            // PHA
            0x48 => {},

            // PHP
            0x08 => {},

            // PLA
            0x68 => {},

            // PLP
            0x28 => {},

            // ROL
            0x2A => {},
            0x26 => {},
            0x36 => {},
            0x2E => {},
            0x3E => {},

            // ROR
            0x6A => {},
            0x66 => {},
            0x76 => {},
            0x6E => {},
            0x7E => {},

            // RTI
            0x40 => {},

            // RTS
            0x60 => {},

            // SBC
            0xE9 => {},
            0xE5 => {},
            0xF5 => {},
            0xED => {},
            0xFD => {},
            0xF9 => {},
            0xE1 => {},
            0xF1 => {},

            // SEC
            0x38 => self.set_carry(),

            // SED
            0xF8 => self.set_decimal(),

            // SEI
            0x78 => self.set_interrupt_disable(),

            // STA
            0x85 => {},
            0x95 => {},
            0x8D => {},
            0x9D => {},
            0x99 => {},
            0x81 => {},
            0x91 => {},

            // STP (WDC 65c02)
            0xDB => return None,

            // STX
            0x86 => {},
            0x96 => {},
            0x8E => {},

            // STY
            0x84 => {},
            0x94 => {},
            0x8C => {},

            // TAX
            0xAA => {
                let a = self.get_a();
                self.set_x(a);
                if self.get_x() == 0 {
                    self.set_zero();
                } else if self.get_x() & 0b1000_0000 == 0b1000_0000 {
                    self.set_negative();
                }
            },

            // TAY
            0xA8 => {
                let a = self.get_a();
                self.set_y(a);
                if self.get_y() == 0 {
                    self.set_zero();
                } else if self.get_y() & 0b1000_0000 == 0b1000_0000 {
                    self.set_negative();
                }
            },

            // TSX
            0xBA => {
                let sp = self.get_sp();
                self.set_x(sp);
                if self.get_x() == 0 {
                    self.set_zero();
                } else if self.get_x() & 0b1000_0000 == 0b1000_0000 {
                    self.set_negative();
                }
            },

            // TXA
            0x8A => {
                let x = self.get_x();
                self.set_a(x);
                if self.get_a() == 0 {
                    self.set_zero();
                } else if self.get_a() & 0b1000_0000 == 0b1000_0000 {
                    self.set_negative();
                }
            },

            // TXS
            0x9A => {
                let x = self.get_x();
                self.set_sp(x);
            },

            // TYA
            0x98 => {
                let y = self.get_y();
                self.set_a(y);
                if self.get_a() == 0 {
                    self.set_zero();
                } else if self.get_a() & 0b1000_0000 == 0b1000_0000 {
                    self.set_negative();
                }
            },

            _ => panic!("Unknown opcode {}", opcode),
        }
        Some(())
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
        p.memory[0x0000] = 0x78; // LDA zp,X
        p.memory[0x123D] = 0xB5;
        p.memory[0x123E] = 0xFF;
        p.set_x(0x01);
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.a, 0x78);

        p.memory[0x1005] = 0x87; // LDA $,X
        p.memory[0x123F] = 0xBD;
        p.memory[0x1240] = 0x00;
        p.memory[0x1241] = 0x10;
        p.set_x(0x05);
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.a, 0x87);

        p.memory[0x1005] = 0x89; // LDA $,Y
        p.memory[0x1242] = 0xB9;
        p.memory[0x1243] = 0x00;
        p.memory[0x1244] = 0x10;
        p.set_y(0x05);
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.a, 0x89);

        p.memory[0x0010] = 0x78; // LDA (zp,X)
        p.memory[0x0011] = 0x56;
        p.memory[0x5678] = 0x9A;
        p.memory[0x1245] = 0xA1;
        p.memory[0x1246] = 0x0F;
        p.set_x(0x01);
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.a, 0x9A);

        p.memory[0x000F] = 0x89; // LDA (zp),Y
        p.memory[0x0010] = 0x67;
        p.memory[0x678A] = 0xAB;
        p.memory[0x1247] = 0xB1;
        p.memory[0x1248] = 0x0F;
        p.set_y(0x01);
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.a, 0xAB);
    }

    use super::BRK_FLAG;
    use super::CARRY_FLAG;
    use super::NEGATIVE_FLAG;
    use super::OVERFLOW_FLAG;
    use super::ZERO_FLAG;
    #[test]
    fn test_flag_functions() {
        let mut p = Processor::new();

        // BRK FLAG
        p.p = 0b1111_1111 & !BRK_FLAG;
        assert_eq!(p.is_brk(), false);
        p.set_brk();
        assert_eq!(p.is_brk(), true);
        assert_eq!(p.p, 0b1111_1111);
        p.clear_brk();
        assert_eq!(p.is_brk(), false);
        assert_eq!(p.p, 0b1111_1111 & !BRK_FLAG);

        p.p = 0b0000_0000;
        assert_eq!(p.is_brk(), false);
        p.set_brk();
        assert_eq!(p.is_brk(), true);
        assert_eq!(p.p, 0b0000_0000 | BRK_FLAG);
        p.clear_brk();
        assert_eq!(p.is_brk(), false);
        assert_eq!(p.p, 0b0000_0000);

        // CARRY FLAG
        p.p = 0b1111_1111 & !CARRY_FLAG;
        assert_eq!(p.is_carry(), false);
        p.set_carry();
        assert_eq!(p.is_carry(), true);
        p.clear_carry();
        assert_eq!(p.is_carry(), false);
        assert_eq!(p.p, 0b1111_1111 & !CARRY_FLAG);

        p.p = 0b0000_0000;
        assert_eq!(p.is_carry(), false);
        p.set_carry();
        assert_eq!(p.is_carry(), true);
        assert_eq!(p.p, 0b0000_0000 | CARRY_FLAG);
        p.clear_carry();
        assert_eq!(p.is_carry(), false);
        assert_eq!(p.p, 0b0000_0000);

        // DECIMAL FLAG
        p.p = 0b1111_1111 & !DECIMAL_MODE;
        assert_eq!(p.is_decimal(), false);
        p.set_decimal();
        assert_eq!(p.is_decimal(), true);
        p.clear_decimal();
        assert_eq!(p.is_decimal(), false);
        assert_eq!(p.p, 0b1111_1111 & !DECIMAL_MODE);

        p.p = 0b0000_0000;
        assert_eq!(p.is_decimal(), false);
        p.set_decimal();
        assert_eq!(p.is_decimal(), true);
        assert_eq!(p.p, 0b0000_0000 | DECIMAL_MODE);
        p.clear_decimal();
        assert_eq!(p.is_decimal(), false);
        assert_eq!(p.p, 0b0000_0000);

        // INTERRUPT DISABLE FLAG
        p.p = 0b1111_1111 & !INTERRUPT_DISABLE;
        assert_eq!(p.is_interrupt_disable(), false);
        p.set_interrupt_disable();
        assert_eq!(p.is_interrupt_disable(), true);
        p.clear_interrupt_disable();
        assert_eq!(p.is_interrupt_disable(), false);
        assert_eq!(p.p, 0b1111_1111 & !INTERRUPT_DISABLE);

        p.p = 0b0000_0000;
        assert_eq!(p.is_interrupt_disable(), false);
        p.set_interrupt_disable();
        assert_eq!(p.is_interrupt_disable(), true);
        assert_eq!(p.p, 0b0000_0000 | INTERRUPT_DISABLE);
        p.clear_interrupt_disable();
        assert_eq!(p.is_interrupt_disable(), false);
        assert_eq!(p.p, 0b0000_0000);

        // NEGATIVE FLAG
        p.p = 0b1111_1111 & !NEGATIVE_FLAG;
        assert_eq!(p.is_negative(), false);
        p.set_negative();
        assert_eq!(p.is_negative(), true);
        p.clear_negative();
        assert_eq!(p.is_negative(), false);
        assert_eq!(p.p, 0b1111_1111 & !NEGATIVE_FLAG);

        p.p = 0b0000_0000;
        assert_eq!(p.is_overflow(), false);
        p.set_overflow();
        assert_eq!(p.is_overflow(), true);
        assert_eq!(p.p, 0b0000_0000 | OVERFLOW_FLAG);
        p.clear_overflow();
        assert_eq!(p.is_overflow(), false);
        assert_eq!(p.p, 0b0000_0000);

        // OVERFLOW FLAG
        p.p = 0b1111_1111 & !OVERFLOW_FLAG;
        assert_eq!(p.is_overflow(), false);
        p.set_overflow();
        assert_eq!(p.is_overflow(), true);
        p.clear_overflow();
        assert_eq!(p.is_overflow(), false);
        assert_eq!(p.p, 0b1111_1111 & !OVERFLOW_FLAG);

        p.p = 0b0000_0000;
        assert_eq!(p.is_overflow(), false);
        p.set_overflow();
        assert_eq!(p.is_overflow(), true);
        assert_eq!(p.p, 0b0000_0000 | OVERFLOW_FLAG);
        p.clear_overflow();
        assert_eq!(p.is_overflow(), false);
        assert_eq!(p.p, 0b0000_0000);

        // ZERO FLAG
        p.p = 0b1111_1111 & !ZERO_FLAG;
        assert_eq!(p.is_zero(), false);
        p.set_zero();
        assert_eq!(p.is_zero(), true);
        p.clear_zero();
        assert_eq!(p.is_zero(), false);
        assert_eq!(p.p, 0b1111_1111 & !ZERO_FLAG);
    
        p.p = 0b0000_0000;
        assert_eq!(p.is_zero(), false);
        p.set_zero();
        assert_eq!(p.is_zero(), true);
        assert_eq!(p.p, 0b0000_0000 | ZERO_FLAG);
        p.clear_zero();
        assert_eq!(p.is_zero(), false);
        assert_eq!(p.p, 0b0000_0000);
    }

    #[test]
    fn test_set_clear_instructions() {
        let mut p = Processor::new();
        p.memory[0xFFFC] = 0x34;
        p.memory[0xFFFD] = 0x12;
        p.memory[0x1234] = 0x38; // SEC
        p.memory[0x1235] = 0x18; // CLC
        p.memory[0x1236] = 0xF8; // SED
        p.memory[0x1237] = 0xD8; // CLD
        p.memory[0x1238] = 0x78; // SEI
        p.memory[0x1239] = 0x58; // CLI
        p.memory[0x123A] = 0xB8; // CLV
        p.reset();
        p.p = 0b0000_0000;  // Note: 6th bit is normally statically 1

        // CARRY
        assert_eq!(p.p, 0b0000_0000);
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.p & CARRY_FLAG, CARRY_FLAG);
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.p, 0b0000_0000);

        // DECIMAL
        assert_eq!(p.p, 0b0000_0000);
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.p & DECIMAL_MODE, DECIMAL_MODE);
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.p, 0b0000_0000);

        // INTERRUPT
        assert_eq!(p.p, 0b0000_0000);
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.p | INTERRUPT_DISABLE, INTERRUPT_DISABLE);
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.p, 0b0000_0000);

        // OVERFLOW
        p.p &= OVERFLOW_FLAG;
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.p & !OVERFLOW_FLAG, 0b0000_0000);
    }

    #[test]
    fn test_inx_iny() {
        let mut p = Processor::new();
        p.memory[0xFFFC] = 0x34;
        p.memory[0xFFFD] = 0x12;
        p.memory[0x1234] = 0xE8;
        p.memory[0x1235] = 0xE8;
        p.memory[0x1236] = 0xE8;
        p.memory[0x1237] = 0xC8;
        p.memory[0x1238] = 0xC8;
        p.memory[0x1239] = 0xC8;
        p.reset();

        let flags = p.p;
        assert_eq!(p.get_x(), 0);
        let (opcode, operand) = p.fetch().unwrap();
        assert_eq!(operand.len(), 0);
        p.execute(opcode, operand);
        assert_eq!(p.get_x(), 1);
        assert_eq!(p.p, flags);

        p.set_x(0xFF);
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.get_x(), 0);
        assert_eq!(p.p & ZERO_FLAG, ZERO_FLAG);

        p.set_x(0x7F);
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.p & NEGATIVE_FLAG, NEGATIVE_FLAG);

        let flags = p.p;
        assert_eq!(p.get_y(), 0);
        let (opcode, operand) = p.fetch().unwrap();
        assert_eq!(operand.len(), 0);
        p.execute(opcode, operand);
        assert_eq!(p.get_y(), 1);
        assert_eq!(p.p, flags);

        p.set_y(0xFF);
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.get_y(), 0);
        assert_eq!(p.p & ZERO_FLAG, ZERO_FLAG);

        p.set_y(0x7F);
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.p & NEGATIVE_FLAG, NEGATIVE_FLAG);
    }

    #[test]
    fn test_transfer_instructions() {
        let mut p = Processor::new();
        p.memory[0xFFFC] = 0x34;
        p.memory[0xFFFD] = 0x12;
        p.memory[0x1234] = 0xAA;
        p.memory[0x1235] = 0xAA;
        p.memory[0x1236] = 0xAA;
        p.memory[0x1237] = 0xA8;
        p.memory[0x1238] = 0xA8;
        p.memory[0x1239] = 0xA8;
        p.memory[0x123A] = 0xBA;
        p.memory[0x123B] = 0xBA;
        p.memory[0x123C] = 0xBA;
        p.memory[0x123D] = 0x8A;
        p.memory[0x123E] = 0x8A;
        p.memory[0x123F] = 0x8A;
        p.memory[0x1240] = 0x9A;
        p.memory[0x1241] = 0x98;
        p.memory[0x1242] = 0x98;
        p.memory[0x1243] = 0x98;
        p.reset();

        // TAX
        p.set_a(0x12);
        let (opcode, operand) = p.fetch().unwrap();
        let operand_len = operand.len();
        p.execute(opcode, operand);
        assert_eq!(operand_len, 0);
        assert_eq!(p.get_a(), p.get_x());

        p.set_a(0x00);
        p.clear_zero();
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.is_zero(), true);

        p.set_a(0b1000_0000);
        p.clear_negative();
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.is_negative(), true);

        // TAY
        let (opcode, operand) = p.fetch().unwrap();
        let operand_len = operand.len();
        p.execute(opcode, operand);
        assert_eq!(operand_len, 0);
        assert_eq!(p.get_a(), p.get_y());

        p.set_a(0x00);
        p.clear_zero();
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.is_zero(), true);

        p.set_a(0b1000_0000);
        p.clear_negative();
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.is_negative(), true);

        // TSX
        p.sp = 0x34;
        let (opcode, operand) = p.fetch().unwrap();
        let operand_len = operand.len();
        p.execute(opcode, operand);
        assert_eq!(operand_len, 0);
        assert_eq!(p.get_x(), p.sp);

        p.sp = 0x00;
        p.clear_zero();
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.is_zero(), true);

        p.sp = 0b1000_0000;
        p.clear_negative();
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.is_negative(), true);

        // TXA
        p.set_x(0x34);
        let (opcode, operand) = p.fetch().unwrap();
        let operand_len = operand.len();
        p.execute(opcode, operand);
        assert_eq!(operand_len, 0);
        assert_eq!(p.get_a(), p.get_x());

        p.set_x(0x00);
        p.clear_zero();
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.is_zero(), true);

        p.set_x(0b1000_0000);
        p.clear_negative();
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.is_negative(), true);

        // TXS
        p.set_x(0x56);
        let (opcode, operand) = p.fetch().unwrap();
        let operand_len = operand.len();
        p.execute(opcode, operand);
        assert_eq!(operand_len, 0);
        assert_eq!(p.get_x(), p.sp);

        // TYA
        p.set_y(0x78);
        let (opcode, operand) = p.fetch().unwrap();
        let operand_len = operand.len();
        p.execute(opcode, operand);
        assert_eq!(operand_len, 0);
        assert_eq!(p.get_y(), p.get_a());

        p.set_y(0x00);
        p.clear_zero();
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.is_zero(), true);

        p.set_y(0b1000_0000);
        p.clear_negative();
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.is_negative(), true);
    }

    #[test]
    fn test_jmp_instruction() {
        let mut p = Processor::new();
        p.memory[0xFFFC] = 0x34;
        p.memory[0xFFFD] = 0x12;
        p.memory[0x1234] = 0x4C;    // JMP absolute
        p.memory[0x1235] = 0x40;    // Little endian
        p.memory[0x1236] = 0x12;
        p.memory[0x1240] = 0xEA;
        p.memory[0x1241] = 0x6C;    // JMP indirect
        p.memory[0x1242] = 0x35;
        p.memory[0x1243] = 0x12;
        p.reset();

        let (opcode, operand) = p.fetch().unwrap();
        assert_eq!(operand.len(), 2);
        p.execute(opcode, operand);
        assert_eq!(p.pc, 0x1240);
        let (opcode, operand) = p.fetch().unwrap();
        assert_eq!(opcode, 0xEA);
        p.execute(opcode, operand);

        let (opcode, operand) = p.fetch().unwrap();
        assert_eq!(opcode, 0x6C);
        assert_eq!(operand.len(), 2);
        p.execute(opcode, operand);
        assert_eq!(p.pc, 0x1240);
        let (opcode, _) = p.fetch().unwrap();
        assert_eq!(opcode, 0xEA);
    }

    #[test]
    fn test_dex_dey_instructions() {
        let mut p = Processor::new();
        p.memory[0xFFFC] = 0x34;
        p.memory[0xFFFD] = 0x12;
        p.memory[0x1234] = 0xCA;    // DEX
        p.memory[0x1235] = 0xCA;
        p.memory[0x1236] = 0xCA;
        p.memory[0x1237] = 0x88;    // DEY
        p.memory[0x1238] = 0x88;
        p.memory[0x1239] = 0x88;
        p.reset();

        p.set_x(0x02);
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.get_x(), 0x01);
        assert_eq!(p.is_negative(), false);
        assert_eq!(p.is_zero(), false);

        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.get_x(), 0x00);
        assert_eq!(p.is_negative(), false);
        assert_eq!(p.is_zero(), true);

        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.get_x(), 0xFF);
        assert_eq!(p.is_negative(), true);
        assert_eq!(p.is_zero(), false);

        p.set_y(0x02);
        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.get_y(), 0x01);
        assert_eq!(p.is_negative(), false);
        assert_eq!(p.is_zero(), false);

        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.get_y(), 0x00);
        assert_eq!(p.is_negative(), false);
        assert_eq!(p.is_zero(), true);

        let (opcode, operand) = p.fetch().unwrap();
        p.execute(opcode, operand);
        assert_eq!(p.get_y(), 0xFF);
        assert_eq!(p.is_negative(), true);
        assert_eq!(p.is_zero(), false);
    }
}
