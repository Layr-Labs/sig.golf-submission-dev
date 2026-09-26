import SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstHash67

/-! The first keygen hash uses the private-seed query layout. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstHashFields67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstHash67
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

private theorem addi_pc (s : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    (execInstrBr s (.ADDI rd rs imm)).pc = s.pc + 4 := by
  simp [execInstrBr]
private theorem lui_pc (s : MachineState) (rd : Reg) (imm : BitVec 20) :
    (execInstrBr s (.LUI rd imm)).pc = s.pc + 4 := by
  simp [execInstrBr]
private theorem ld_pc (s : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    (execInstrBr s (.LD rd rs imm)).pc = s.pc + 4 := by
  simp [execInstrBr]
private theorem sd_pc (s : MachineState) (rs1 rs2 : Reg) (imm : BitVec 12) :
    (execInstrBr s (.SD rs1 rs2 imm)).pc = s.pc + 4 := by
  simp [execInstrBr]
private theorem slli_pc (s : MachineState) (rd rs : Reg) (shamt : BitVec 6) :
    (execInstrBr s (.SLLI rd rs shamt)).pc = s.pc + 4 := by
  simp [execInstrBr]
private theorem add_pc (s : MachineState) (rd rs1 rs2 : Reg) :
    (execInstrBr s (.ADD rd rs1 rs2)).pc = s.pc + 4 := by
  simp [execInstrBr]

theorem pre_hash_pc (s : MachineState) (pc : s.pc = 0x10a0) :
    (preHashState s).pc = 0x1138 := by
  have h0 (t : MachineState) : (headerState t).pc = t.pc + 56 := by
    simp only [headerState, addi_pc, lui_pc, ld_pc, sd_pc, slli_pc, add_pc]
    simp [BitVec.add_assoc]
  have h1 (t : MachineState) : (index0State t).pc = t.pc + 24 := by
    simp only [index0State, addi_pc, lui_pc, ld_pc, sd_pc]
    simp [BitVec.add_assoc]
  have h2 (t : MachineState) : (index1State t).pc = t.pc + 24 := by
    simp only [index1State, addi_pc, lui_pc, ld_pc, sd_pc]
    simp [BitVec.add_assoc]
  have h3 (t : MachineState) : (index2State t).pc = t.pc + 24 := by
    simp only [index2State, addi_pc, lui_pc, ld_pc, sd_pc]
    simp [BitVec.add_assoc]
  have h4 (t : MachineState) : (regsState t).pc = t.pc + 24 := by
    simp only [regsState, addi_pc, lui_pc]
    simp [BitVec.add_assoc]
  simp only [preHashState, h4, h3, h2, h1, h0, pc]
  decide

private theorem regs_regs (s : MachineState) :
    (regsState s).getReg .x5 = 1 ∧
    (regsState s).getReg .x10 = 0x80000 ∧
    (regsState s).getReg .x11 = 512 ∧
    (regsState s).getReg .x12 = 0x80300 := by
  simp [regsState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem pre_hash_regs (s : MachineState) :
    (preHashState s).getReg .x5 = 1 ∧
    (preHashState s).getReg .x10 = 0x80000 ∧
    (preHashState s).getReg .x11 = 512 ∧
    (preHashState s).getReg .x12 = 0x80300 := by
  exact regs_regs _

private theorem header_x19 (s : MachineState) :
    (headerState s).getReg .x19 = s.getReg .x19 := by
  simp [headerState,execInstrBr,MachineState.getReg_setReg_ne]
private theorem index0_x19 (s : MachineState) :
    (index0State s).getReg .x19 = s.getReg .x19 := by
  simp [index0State,execInstrBr,MachineState.getReg_setReg_ne]
private theorem index1_x19 (s : MachineState) :
    (index1State s).getReg .x19 = s.getReg .x19 := by
  simp [index1State,execInstrBr,MachineState.getReg_setReg_ne]
private theorem index2_x19 (s : MachineState) :
    (index2State s).getReg .x19 = s.getReg .x19 := by
  simp [index2State,execInstrBr,MachineState.getReg_setReg_ne]
private theorem regs_x19 (s : MachineState) :
    (regsState s).getReg .x19 = s.getReg .x19 := by
  simp [regsState,execInstrBr,MachineState.getReg_setReg_ne]

theorem pre_hash_x19 (s : MachineState) :
    (preHashState s).getReg .x19 = s.getReg .x19 := by
  simp only [preHashState,regs_x19,index2_x19,index1_x19,index0_x19,header_x19]

#print axioms pre_hash_pc
#print axioms pre_hash_regs
#print axioms pre_hash_x19
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstHashFields67
