use crate::opcodes;
use crate::Bus;
use std::collections::HashMap;

bitflags! {
    /// # Status Register (P) http://wiki.nesdev.com/w/index.php/Status_flags
    ///
    ///  7 6 5 4 3 2 1 0
    ///  N V _ B D I Z C
    ///  | |   | | | | +--- Carry Flag
    ///  | |   | | | +----- Zero Flag
    ///  | |   | | +------- Interrupt Disable
    ///  | |   | +--------- Decimal Mode (not used on NES)
    ///  | |   +----------- Break Command
    ///  | +--------------- Overflow Flag
    ///  +----------------- Negative Flag
    ///
    pub struct CpuFlags: u8 {
        const CARRY             = 0b00000001;
        const ZERO              = 0b00000010;
        const INTERRUPT_DISABLE = 0b00000100;
        const DECIMAL_MODE      = 0b00001000;
        const BREAK             = 0b00010000;
        const BREAK2            = 0b00100000;
        const OVERFLOW          = 0b01000000;
        const NEGATIVE          = 0b10000000;
    }
}

const STACK: u16 = 0x0100;
const STACK_RESET: u8 = 0xfd;

pub struct CPU {
    pub register_a: u8,
    pub register_x: u8,
    pub register_y: u8,
    pub status: CpuFlags,
    pub program_counter: u16,
    pub stack_pointer: u8,
    pub bus: Bus,
}

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    Immediate,
    ZeroPage,
    ZeroPage_X,
    ZeroPage_Y,
    Absolute,
    Absolute_X,
    Absolute_Y,
    Indirect_X,
    Indirect_Y,
    NoneAddressing,
}

pub trait Mem {
    fn mem_read(&self, addr: u16) -> u8;

    fn mem_write(&mut self, addr: u16, data: u8);

    fn mem_read_u16(&self, pos: u16) -> u16 {
        let lo = self.mem_read(pos) as u16;
        let hi = self.mem_read(pos + 1) as u16;
        (hi << 8) | (lo as u16)
    }

    fn mem_write_u16(&mut self, pos: u16, data: u16) {
        let hi = (data >> 8) as u8;
        let lo = (data & 0xff) as u8;
        self.mem_write(pos, lo);
        self.mem_write(pos + 1, hi);
    }
}

impl Mem for CPU {
    fn mem_read(&self, addr: u16) -> u8 {
        self.bus.mem_read(addr)
    }

    fn mem_write(&mut self, addr: u16, data: u8) {
        self.bus.mem_write(addr, data)
    }
}

impl CPU {
    pub fn new(bus: Bus) -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: CpuFlags::BREAK2 | CpuFlags::INTERRUPT_DISABLE,
            program_counter: 0,
            stack_pointer: STACK_RESET,
            bus: bus,
        }
        //println!("at birth PC:{}", self.mem_read_u16(0xFFFC));
    }

    pub fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.register_y = 0;
        self.status = CpuFlags::BREAK2 | CpuFlags::INTERRUPT_DISABLE;
        self.program_counter = self.mem_read_u16(0xFFFC);
        println!("reset PC:{}", self.program_counter);
    }

    pub fn load(&mut self, program: Vec<u8>) {
        for i in 0..(program.len() as u16) {
            self.mem_write(0x8600 + i, program[i as usize]);
        }
        self.mem_write_u16(0xFFFC, 0x8600);
    }

    pub fn load_and_run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.run()
    }

    pub fn run(&mut self) {
        self.run_with_callback(|_| {});
    }

    pub fn run_with_callback<F>(&mut self, mut callback: F)
    where
        F: FnMut(&mut CPU),
    {
        let ref opcodes: HashMap<u8, &'static opcodes::OpCode> = *opcodes::OPCODES_MAP;

        loop {
            callback(self);

            let code = self.mem_read(self.program_counter);
            self.program_counter += 1;
            let program_counter_state = self.program_counter;

            let opcode = opcodes
                .get(&code)
                .expect(&format!("OpCode 0x{:x} is not recognized", code));
            //println!("> {} {}", self.program_counter, code);
            match code {
                0x69 | 0x65 | 0x75 | 0x6d | 0x7d | 0x79 | 0x61 | 0x71 => {
                    self.adc(&opcode.mode);
                }

                0x29 | 0x25 | 0x35 | 0x2d | 0x3d | 0x39 | 0x21 | 0x31 => {
                    self.and(&opcode.mode);
                }

                0x24 | 0x2c => {
                    self.bit(&opcode.mode);
                }

                0xc9 | 0xc5 | 0xd5 | 0xcd | 0xdd | 0xd9 | 0xc1 | 0xd1 => {
                    self.compare(&opcode.mode, self.register_a);
                }

                0xe0 | 0xe4 | 0xec => {
                    self.compare(&opcode.mode, self.register_x);
                }

                0xc0 | 0xc4 | 0xcc => {
                    self.compare(&opcode.mode, self.register_y);
                }

                0xc6 | 0xd6 | 0xce | 0xde => {
                    self.dec(&opcode.mode);
                }

                0xe6 | 0xf6 | 0xee | 0xfe => {
                    self.inc(&opcode.mode);
                }

                0xa9 | 0xa5 | 0xb5 | 0xad | 0xbd | 0xb9 | 0xa1 | 0xb1 => {
                    self.lda(&opcode.mode);
                }

                0xa2 | 0xa6 | 0xb6 | 0xae | 0xbe => {
                    self.ldx(&opcode.mode);
                }

                0xa0 | 0xa4 | 0xb4 | 0xac | 0xbc => {
                    self.ldy(&opcode.mode);
                }

                0x4a /*| 0x46 | 0x56 | 0x4e | 0x5e*/ => {
                    self.lsr();
                }

                0xe9 | 0xe5 | 0xf5 | 0xed | 0xfd | 0xf9 | 0xe1 | 0xf1 => {
                    self.sbc(&opcode.mode);
                }

                0x85 | 0x95 | 0x8d | 0x9d | 0x99 | 0x81 | 0x91 => {
                    self.sta(&opcode.mode);
                }

                0xf0 => self.beq(),
                0xd0 => self.bne(),
                0xb0 => self.bcs(),
                0x90 => self.bcc(),
                0x10 => self.bpl(),

                0x18 => self.clc(),
                0xca => self.dex(),
                0xe8 => self.inx(),
                0x4c => self.jmp(),
                0x20 => self.jsr(),
                0xea => {
                    // NOP - do nothing
                }
                0x60 => self.rts(),
                0x38 => self.sec(),
                0xaa => self.tax(),
                0x8a => self.txa(),

                //0x78 => self.status.insert(CpuFlags::INTERRUPT_DISABLE), // SEI

                0x00 => return,
                _ => todo!(),
            }

            if program_counter_state == self.program_counter {
                self.program_counter += (opcode.len - 1) as u16;
            }
        }
    }

    fn get_operand_address(&self, mode: &AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate => self.program_counter,

            AddressingMode::ZeroPage => self.mem_read(self.program_counter) as u16,

            AddressingMode::Absolute => self.mem_read_u16(self.program_counter),

            AddressingMode::ZeroPage_X => {
                let pos = self.mem_read(self.program_counter);
                let addr = pos.wrapping_add(self.register_x) as u16;
                addr
            }
            AddressingMode::ZeroPage_Y => {
                let pos = self.mem_read(self.program_counter);
                let addr = pos.wrapping_add(self.register_y) as u16;
                addr
            }

            AddressingMode::Absolute_X => {
                let base = self.mem_read_u16(self.program_counter);
                let addr = base.wrapping_add(self.register_x as u16);
                addr
            }
            AddressingMode::Absolute_Y => {
                let base = self.mem_read_u16(self.program_counter);
                let addr = base.wrapping_add(self.register_y as u16);
                addr
            }

            AddressingMode::Indirect_X => {
                let base = self.mem_read(self.program_counter);

                let ptr: u8 = (base as u8).wrapping_add(self.register_x);
                let lo = self.mem_read(ptr as u16);
                let hi = self.mem_read(ptr.wrapping_add(1) as u16);
                (hi as u16) << 8 | (lo as u16)
            }
            AddressingMode::Indirect_Y => {
                let base = self.mem_read(self.program_counter);

                let lo = self.mem_read(base as u16);
                let hi = self.mem_read((base as u8).wrapping_add(1) as u16);
                let deref_base = (hi as u16) << 8 | (lo as u16);
                let deref = deref_base.wrapping_add(self.register_y as u16);
                deref
            }

            AddressingMode::NoneAddressing => {
                panic!("mode {:?} is not supported", mode);
            }
        }
    }

    fn stack_pop(&mut self) -> u8 {
        self.stack_pointer = self.stack_pointer.wrapping_add(1);
        self.mem_read((STACK as u16) + self.stack_pointer as u16)
    }

    fn stack_push(&mut self, data: u8) {
        self.mem_write((STACK as u16) + self.stack_pointer as u16, data);
        self.stack_pointer = self.stack_pointer.wrapping_sub(1)
    }

    fn stack_push_u16(&mut self, data: u16) {
        let hi = (data >> 8) as u8;
        let lo = (data & 0xff) as u8;
        self.stack_push(hi);
        self.stack_push(lo);
    }

    fn stack_pop_u16(&mut self) -> u16 {
        let lo = self.stack_pop() as u16;
        let hi = self.stack_pop() as u16;

        hi << 8 | lo
    }

    fn adc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.add_to_register_a(value);
    }

    fn and(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.register_a &= value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn beq(&mut self) {
        self.branch(self.status.contains(CpuFlags::ZERO));
    }

    fn bne(&mut self) {
        self.branch(!self.status.contains(CpuFlags::ZERO));
    }

    fn bcs(&mut self) {
        self.branch(self.status.contains(CpuFlags::CARRY));
    }

    fn bcc(&mut self) {
        self.branch(!self.status.contains(CpuFlags::CARRY));
    }

    fn bpl(&mut self) {
        self.branch(!self.status.contains(CpuFlags::NEGATIVE));
    }

    fn bit(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        let and = self.register_a & data;

        self.status.set(CpuFlags::ZERO, and == 0);
        self.status.set(CpuFlags::NEGATIVE, data & 0b10000000 > 0);
        self.status.set(CpuFlags::OVERFLOW, data & 0b01000000 > 0);
    }

    fn compare(&mut self, mode: &AddressingMode, register: u8) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);

        self.status.set(CpuFlags::CARRY, data <= register);
        self.update_zero_and_negative_flags(register.wrapping_sub(data));
    }

    fn clc(&mut self) {
        self.status.remove(CpuFlags::CARRY);
    }

    fn dec(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        data = data.wrapping_sub(1);
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
    }

    fn dex(&mut self) {
        self.register_x = self.register_x.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn inc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        data = data.wrapping_add(1);
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
    }

    fn inx(&mut self) {
        self.register_x = self.register_x.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn jmp(&mut self) {
        let mem_address = self.mem_read_u16(self.program_counter);
        self.program_counter = mem_address;
    }

    fn jsr(&mut self) {
        self.stack_push_u16(self.program_counter + 2 - 1);
        self.program_counter = self.mem_read_u16(self.program_counter);
    }

    fn lda(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn ldx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.register_x = value;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn ldy(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.register_y = value;
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn lsr(&mut self) {
        let mut data = self.register_a;
        self.status.set(CpuFlags::CARRY, data & 1 == 1);

        data = data >> 1;
        self.register_a = data;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn rts(&mut self) {
        self.program_counter = self.stack_pop_u16() + 1;
    }

    fn sbc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let data = self.mem_read(addr);
        self.add_to_register_a(((data as i8).wrapping_neg().wrapping_sub(1)) as u8);
    }

    fn sec(&mut self) {
        self.status.insert(CpuFlags::CARRY);
    }

    fn sta(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_a);
    }

    fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn txa(&mut self) {
        self.register_a = self.register_x;
        self.update_zero_and_negative_flags(self.register_a);
    }

    /// Note: Ignoring decimal mode
    /// http://www.righto.com/2012/12/the-6502-overflow-flag-explained.html
    fn add_to_register_a(&mut self, data: u8) {
        let sum = self.register_a as u16
            + data as u16
            + (if self.status.contains(CpuFlags::CARRY) {
                1
            } else {
                0
            }) as u16;

        self.status.set(CpuFlags::CARRY, sum > 0xff);

        let result = sum as u8;
        self.register_a = result;

        let overflow = (data ^ result) & (result ^ self.register_a) & 0x80 != 0;
        self.status.set(CpuFlags::OVERFLOW, overflow);
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn branch(&mut self, condition: bool) {
        if condition {
            let jump: i8 = self.mem_read(self.program_counter) as i8;
            let jump_addr = self
                .program_counter
                .wrapping_add(1)
                .wrapping_add(jump as u16);

            self.program_counter = jump_addr;
        }
    }

    fn update_zero_and_negative_flags(&mut self, result: u8) {
        self.status.set(CpuFlags::ZERO, result == 0);
        self.status
            .set(CpuFlags::NEGATIVE, result & 0b1000_0000 != 0);
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::cartridge::test;

    const OP_LDA: u8 = 0xa9;

    #[test]
    fn test_lda_immediate_load_data() {
        let bus = Bus::new(test::test_rom(vec![OP_LDA, 0x05, 0x00]));
        let mut cpu = CPU::new(bus);
        cpu.reset();
        cpu.run();
        assert_eq!(cpu.register_a, 0x05);
        assert!(!cpu.status.contains(CpuFlags::ZERO));
        assert!(!cpu.status.contains(CpuFlags::NEGATIVE));
    }

    #[test]
    fn test_lda_immediate_load_negative() {
        let bus = Bus::new(test::test_rom(vec![OP_LDA, 0x80, 0x00]));
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![OP_LDA, 0x80, 0x00]);
        assert!(cpu.status.contains(CpuFlags::NEGATIVE));
    }

    #[test]
    fn test_lda_zero_flag() {
        let bus = Bus::new(test::test_rom(vec![OP_LDA, 0x00, 0x00]));
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![OP_LDA, 0x00, 0x00]);
        assert!(cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_lda_from_memory() {
        let bus = Bus::new(test::test_rom(vec![0xa5, 0x10, 0x00]));
        let mut cpu = CPU::new(bus);
        cpu.mem_write(0x10, 0x55);

        cpu.load_and_run(vec![0xa5, 0x10, 0x00]);

        assert_eq!(cpu.register_a, 0x55);
    }
/* 
    #[test]
    fn test_ldx_immediate_load_data() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![0xa2, 0x05, 0x00]);
        assert_eq!(cpu.register_x, 0x05);
        assert!(!cpu.status.contains(CpuFlags::ZERO));
        assert!(!cpu.status.contains(CpuFlags::NEGATIVE));
    }

    #[test]
    fn test_ldy_immediate_load_data() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![0xa0, 0x05, 0x00]);
        assert_eq!(cpu.register_y, 0x05);
        assert!(!cpu.status.contains(CpuFlags::ZERO));
        assert!(!cpu.status.contains(CpuFlags::NEGATIVE));
    }

    #[test]
    fn test_tax_move_a_to_x_zero() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![0xaa, 0x00]);

        assert_eq!(cpu.register_x, 0);
        assert!(cpu.status.contains(CpuFlags::ZERO));
        assert!(!cpu.status.contains(CpuFlags::NEGATIVE));
    }

    #[test]
    fn test_tax_move_a_to_x_positive() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![OP_LDA, 10, 0xaa, 0x00]);

        assert_eq!(cpu.register_x, 10);
        assert!(!cpu.status.contains(CpuFlags::ZERO));
        assert!(!cpu.status.contains(CpuFlags::NEGATIVE));
    }

    #[test]
    fn test_tax_move_a_to_x_negative() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![OP_LDA, 0x80, 0xaa, 0x00]);

        assert_eq!(cpu.register_x, 0x80);
        assert!(!cpu.status.contains(CpuFlags::ZERO));
        assert!(cpu.status.contains(CpuFlags::NEGATIVE));
    }

    #[test]
    fn test_txa_positive() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![0xa2, 0x55, 0x8a, 0x00]);

        assert_eq!(cpu.register_a, 0x55);
        assert!(!cpu.status.contains(CpuFlags::ZERO));
        assert!(!cpu.status.contains(CpuFlags::NEGATIVE));
    }

    #[test]
    fn test_5_ops_working_together() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![OP_LDA, 0xc0, 0xaa, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 0xc1)
    }

    #[test]
    fn test_inx_overflow() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![OP_LDA, 0xff, 0xaa, 0xe8, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 1)
    }

    #[test]
    fn test_dex() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![0xca, 0x00]);

        assert_eq!(cpu.register_x, 0xff);
        assert!(cpu.status.contains(CpuFlags::NEGATIVE));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_and_positive() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![OP_LDA, 0xf0, 0x29, 0x77, 0x00]);
        assert_eq!(cpu.register_a, 0x70);
        assert!(!cpu.status.contains(CpuFlags::ZERO));
        assert!(!cpu.status.contains(CpuFlags::NEGATIVE));
    }

    #[test]
    fn test_and_zero() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![OP_LDA, 0xf0, 0x29, 0x0f, 0x00]);
        assert_eq!(cpu.register_a, 0x0);
        assert!(cpu.status.contains(CpuFlags::ZERO));
        assert!(!cpu.status.contains(CpuFlags::NEGATIVE));
    }

    #[test]
    fn test_adc() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![OP_LDA, 0xf0, 0x69, 0x77, 0x00]);
        assert_eq!(cpu.register_a, 0x67);
        assert!(cpu.status.contains(CpuFlags::CARRY));
    }

    #[test]
    fn test_cmp_zero() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![OP_LDA, 0x55, 0xc9, 0x55, 0x00]);
        assert_eq!(cpu.register_a, 0x55);
        assert!(cpu.status.contains(CpuFlags::CARRY));
        assert!(cpu.status.contains(CpuFlags::ZERO));
        assert!(!cpu.status.contains(CpuFlags::NEGATIVE));
    }

    #[test]
    fn test_cmp_negative() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![OP_LDA, 0x7f, 0xc9, 0xf0, 0x00]);
        assert_eq!(cpu.register_a, 0x7f);
        assert!(!cpu.status.contains(CpuFlags::CARRY));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
        assert!(cpu.status.contains(CpuFlags::NEGATIVE));
    }

    #[test]
    fn test_lsr() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![OP_LDA, 0x04, 0x4a, 0x00]);
        assert_eq!(cpu.register_a, 0x02);
        assert!(!cpu.status.contains(CpuFlags::CARRY));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
        assert!(!cpu.status.contains(CpuFlags::NEGATIVE));
    }
    */
}
