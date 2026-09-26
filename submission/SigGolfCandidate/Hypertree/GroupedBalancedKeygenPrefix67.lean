import SigGolfCandidate.Hypertree.GroupedBalancedKeygenImage67
import SigGolfCandidate.Hypertree.KeygenBlocks
import SigGolfCandidate.Hypertree.KeygenTrace

/-! The direct67 key generator sets its root level, tree address, and counters before its first branch. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenPrefix67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def image : Image := GroupedBalancedKeygenImage67.image

def entryState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 156)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 48)
  execInstrBr s (.SD .x28 .x6 0)

private theorem entry_code :
    Keygen.instructionAt image 0x1000 = some (.base (.ADDI .x6 .x0 156)) ∧
    Keygen.instructionAt image 0x1004 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1008 = some (.base (.ADDI .x28 .x28 0)) ∧
    Keygen.instructionAt image 0x100c = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1010 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x1014 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1018 = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x101c = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1020 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x1024 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1028 = some (.base (.ADDI .x28 .x28 16)) ∧
    Keygen.instructionAt image 0x102c = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1030 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x1034 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1038 = some (.base (.ADDI .x28 .x28 24)) ∧
    Keygen.instructionAt image 0x103c = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1040 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x1044 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1048 = some (.base (.ADDI .x28 .x28 48)) ∧
    Keygen.instructionAt image 0x104c = some (.base (.SD .x28 .x6 0)) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide

theorem entry_steps (s : MachineState) (pc : s.pc = 0x1000) :
    OrdinarySteps image s 20 (entryState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 156)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.ADDI .x6 .x0 0)
  let s6 := execInstrBr s5 (.LUI .x28 0x81)
  let s7 := execInstrBr s6 (.ADDI .x28 .x28 8)
  let s8 := execInstrBr s7 (.SD .x28 .x6 0)
  let s9 := execInstrBr s8 (.ADDI .x6 .x0 0)
  let s10 := execInstrBr s9 (.LUI .x28 0x81)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 16)
  let s12 := execInstrBr s11 (.SD .x28 .x6 0)
  let s13 := execInstrBr s12 (.ADDI .x6 .x0 0)
  let s14 := execInstrBr s13 (.LUI .x28 0x81)
  let s15 := execInstrBr s14 (.ADDI .x28 .x28 24)
  let s16 := execInstrBr s15 (.SD .x28 .x6 0)
  let s17 := execInstrBr s16 (.ADDI .x6 .x0 0)
  let s18 := execInstrBr s17 (.LUI .x28 0x81)
  let s19 := execInstrBr s18 (.ADDI .x28 .x28 48)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19⟩ := entry_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 156)) 19
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 18
  · have hp : s1.pc = 0x1004 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 17
  · have hp : s2.pc = 0x1008 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 16
  · have hp : s3.pc = 0x100c := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [s1,s2,s3,s4,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x6 .x0 0)) 15
  · have hp : s4.pc = 0x1010 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 0x81)) 14
  · have hp : s5.pc = 0x1014 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 8)) 13
  · have hp : s6.pc = 0x1018 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x6 0)) 12
  · have hp : s7.pc = 0x101c := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x6 .x0 0)) 11
  · have hp : s8.pc = 0x1020 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 0x81)) 10
  · have hp : s9.pc = 0x1024 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 16)) 9
  · have hp : s10.pc = 0x1028 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.SD .x28 .x6 0)) 8
  · have hp : s11.pc = 0x102c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x6 .x0 0)) 7
  · have hp : s12.pc = 0x1030 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.LUI .x28 0x81)) 6
  · have hp : s13.pc = 0x1034 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.ADDI .x28 .x28 24)) 5
  · have hp : s14.pc = 0x1038 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.SD .x28 .x6 0)) 4
  · have hp : s15.pc = 0x103c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s16 s17 _ (.base (.ADDI .x6 .x0 0)) 3
  · have hp : s16.pc = 0x1040 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s17.pc = 0x1044 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.ADDI .x28 .x28 48)) 1
  · have hp : s18.pc = 0x1048 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · rfl
  apply OrdinarySteps.step s19 (entryState s) _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s19.pc = 0x104c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,entryState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem entry_trace (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1000) :
    Trace hash image s 20 20 0 0 (entryState s) :=
  (entry_steps s pc).trace

theorem entry_pc (s : MachineState) (pc : s.pc = 0x1000) :
    (entryState s).pc = 0x1050 := by
  simp [entryState,execInstrBr,pc]

theorem entry_words (s : MachineState) :
    (entryState s).getMem 0x81000 = 156 ∧
    (entryState s).getMem 0x81008 = 0 ∧
    (entryState s).getMem 0x81010 = 0 ∧
    (entryState s).getMem 0x81018 = 0 ∧
    (entryState s).getMem 0x81030 = 0 := by
  simp [entryState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem entry_mem_other (s : MachineState) (a : Word)
    (h0 : a ≠ 0x81000) (h8 : a ≠ 0x81008)
    (h10 : a ≠ 0x81010) (h18 : a ≠ 0x81018)
    (h30 : a ≠ 0x81030) :
    (entryState s).getMem a = s.getMem a := by
  simp [entryState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  split_ifs <;> simp_all

#print axioms entry_trace
#print axioms entry_words

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenPrefix67
