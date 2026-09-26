import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureDigitAfter67

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureWriteAfter67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def pointer (s : MachineState) : Word :=
  s.getMem 0x810f0 + (s.getReg .x6 <<< 4)

def writeState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.SLLI .x6 .x6 4)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xf0)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.ADD .x7 .x7 .x6)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x20)
  let s := execInstrBr s (.LD .x13 .x28 0)
  let s := execInstrBr s (.LD .x14 .x28 8)
  let s := execInstrBr s (.SD .x7 .x13 0)
  execInstrBr s (.SD .x7 .x14 8)

private theorem write_code :
    Keygen.instructionAt image 0x1a80 = some (.base (.SLLI .x6 .x6 4)) ∧
    Keygen.instructionAt image 0x1a84 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1a88 = some (.base (.ADDI .x28 .x28 0xf0)) ∧
    Keygen.instructionAt image 0x1a8c = some (.base (.LD .x7 .x28 0)) ∧
    Keygen.instructionAt image 0x1a90 = some (.base (.ADD .x7 .x7 .x6)) ∧
    Keygen.instructionAt image 0x1a94 = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 0x1a98 = some (.base (.ADDI .x28 .x28 0x20)) ∧
    Keygen.instructionAt image 0x1a9c = some (.base (.LD .x13 .x28 0)) ∧
    Keygen.instructionAt image 0x1aa0 = some (.base (.LD .x14 .x28 8)) ∧
    Keygen.instructionAt image 0x1aa4 = some (.base (.SD .x7 .x13 0)) ∧
    Keygen.instructionAt image 0x1aa8 = some (.base (.SD .x7 .x14 8)) := by decide

theorem write_steps (s : MachineState) (pc : s.pc = 0x1a80)
    (safe : accessValid (pointer s) 8 = true)
    (safeNext : accessValid (pointer s + 8) 8 = true) :
    OrdinarySteps image s 11 (writeState s) := by
  let p := pointer s
  let s1 := execInstrBr s (.SLLI .x6 .x6 4)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0xf0)
  let s4 := execInstrBr s3 (.LD .x7 .x28 0)
  let s5 := execInstrBr s4 (.ADD .x7 .x7 .x6)
  let s6 := execInstrBr s5 (.LUI .x28 0x80)
  let s7 := execInstrBr s6 (.ADDI .x28 .x28 0x20)
  let s8 := execInstrBr s7 (.LD .x13 .x28 0)
  let s9 := execInstrBr s8 (.LD .x14 .x28 8)
  let s10 := execInstrBr s9 (.SD .x7 .x13 0)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10⟩ := write_code
  apply OrdinarySteps.step s s1 _ (.base (.SLLI .x6 .x6 4)) 10
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 9
  · simpa [Keygen.fetch_at,s1,execInstrBr,pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0xf0)) 8
  · simpa [Keygen.fetch_at,s1,s2,execInstrBr,pc] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x7 .x28 0)) 7
  · simpa [Keygen.fetch_at,s1,s2,s3,execInstrBr,pc] using c3
  · have haddr : s3.getReg .x28 = 0x810f0 := by
      simp [s1,s2,s3,p,p,pointer,execInstrBr,signExtend12,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    change (if accessValid (s3.getReg .x28 + signExtend12 (0 : BitVec 12)) 8
      then some s4 else none) = some s4
    simp [haddr,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADD .x7 .x7 .x6)) 6
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,execInstrBr,pc] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 0x80)) 5
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,execInstrBr,pc] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 0x20)) 4
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,execInstrBr,pc] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.LD .x13 .x28 0)) 3
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc] using c7
  · have haddr : s7.getReg .x28 = 0x80020 := by
      simp [s1,s2,s3,s4,s5,s6,s7,p,pointer,execInstrBr,signExtend12,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    change (if accessValid (s7.getReg .x28 + signExtend12 (0 : BitVec 12)) 8
      then some s8 else none) = some s8
    simp [haddr,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  apply OrdinarySteps.step s8 s9 _ (.base (.LD .x14 .x28 8)) 2
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc] using c8
  · have haddr : s8.getReg .x28 = 0x80020 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,p,pointer,execInstrBr,signExtend12,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    change (if accessValid (s8.getReg .x28 + signExtend12 (8 : BitVec 12)) 8
      then some s9 else none) = some s9
    simp [haddr,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  apply OrdinarySteps.step s9 s10 _ (.base (.SD .x7 .x13 0)) 1
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc] using c9
  · have haddr : s9.getReg .x7 = p := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,p,pointer,execInstrBr,signExtend12,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    change (if accessValid (s9.getReg .x7 + signExtend12 (0 : BitVec 12)) 8
      then some s10 else none) = some s10
    simpa [haddr,signExtend12] using safe
  apply OrdinarySteps.step s10 (writeState s) _ (.base (.SD .x7 .x14 8)) 0
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc] using c10
  · have haddr : s10.getReg .x7 = p := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,p,pointer,execInstrBr,signExtend12,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    change (if accessValid (s10.getReg .x7 + signExtend12 (8 : BitVec 12)) 8
      then some (writeState s) else none) = some (writeState s)
    simpa [haddr,signExtend12] using safeNext
  exact OrdinarySteps.refl _

theorem write_pc (s : MachineState) (pc : s.pc = 0x1a80) :
    (writeState s).pc = 0x1aac := by
  simp [writeState,execInstrBr,pc]

theorem write_mem (s : MachineState) (a : Word) :
    (writeState s).getMem a =
      if a = pointer s + 8 then s.getMem 0x80028
      else if a = pointer s then s.getMem 0x80020
      else s.getMem a := by
  simp [writeState,pointer,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  rfl

private theorem ptr_ne_next (p : Word) : p ≠ p + 8 := by
  intro h
  have hn := congrArg (fun x : Word => x - p) h
  rw [BitVec.sub_self, BitVec.add_comm p 8, BitVec.add_sub_cancel] at hn
  exact (by decide : (0#64) ≠ 8) hn

theorem write_values (s : MachineState) :
    (writeState s).getMem (pointer s) = s.getMem 0x80020 ∧
    (writeState s).getMem (pointer s + 8) = s.getMem 0x80028 := by
  constructor
  · rw [write_mem,if_neg (ptr_ne_next (pointer s)),if_pos rfl]
  · rw [write_mem,if_pos rfl]

theorem write_frame (s : MachineState) (a : Word)
    (h0 : a ≠ pointer s) (h1 : a ≠ pointer s + 8) :
    (writeState s).getMem a = s.getMem a := by
  rw [write_mem,if_neg h1,if_neg h0]

theorem write_regs (s : MachineState) :
    (writeState s).getReg .x19 = s.getReg .x19 ∧
    (writeState s).getReg .x20 = s.getReg .x20 ∧
    (writeState s).getReg .x21 = s.getReg .x21 ∧
    (writeState s).getReg .x10 = s.getReg .x10 ∧
    (writeState s).getReg .x11 = s.getReg .x11 ∧
    (writeState s).getReg .x12 = s.getReg .x12 ∧
    (writeState s).getReg .x5 = s.getReg .x5 := by
  simp [writeState,execInstrBr,MachineState.getReg_setReg_ne]

#print axioms write_steps
#print axioms write_values
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureWriteAfter67
