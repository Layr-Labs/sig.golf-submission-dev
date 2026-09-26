import SigGolfCandidate.Hypertree.KeygenBlocks
import SigGolfCandidate.Hypertree.GroupedBalancedSignImage67Byte

/-! The upper tree return copies its root and advances the witness pointer. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperPostRoot67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67Byte.image

def postState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xc0)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.LD .x10 .x7 0)
  let s := execInstrBr s (.LD .x11 .x7 8)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x500)
  let s := execInstrBr s (.SD .x7 .x10 0)
  let s := execInstrBr s (.SD .x7 .x11 8)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xf8)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x60)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.SLLI .x7 .x7 4)
  let s := execInstrBr s (.ADD .x6 .x6 .x7)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xf0)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x100)
  execInstrBr s (.SD .x28 .x6 0)

theorem post_pc (s : MachineState) (pc : s.pc = 0x1c34) :
    (postState s).pc = 0x1c94 := by
  simp [postState,execInstrBr,pc]

theorem post_words (s : MachineState) (p : Word)
    (source : s.getMem 0x810c0 = p) :
    (postState s).getMem 0x80500 = s.getMem p ∧
    (postState s).getMem 0x80508 = s.getMem (p+8) ∧
    (postState s).getMem 0x810f0 =
      s.getMem 0x810f8 + (s.getMem 0x81060 <<< 4) ∧
    (postState s).getMem 0x81100 = 0 := by
  have source' : s.getMem (528576#64) = p := source
  simp [postState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,source']

theorem post_frame (s : MachineState) (a : Word)
    (h0 : a ≠ 0x80500) (h1 : a ≠ 0x80508)
    (h2 : a ≠ 0x810f0) (h3 : a ≠ 0x81100) :
    (postState s).getMem a = s.getMem a := by
  simp [postState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  split_ifs <;> simp_all

private theorem post_code :
    Keygen.instructionAt image 0x1c34 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1c38 = some (.base (.ADDI .x28 .x28 0xc0)) ∧
    Keygen.instructionAt image 0x1c3c = some (.base (.LD .x7 .x28 0)) ∧
    Keygen.instructionAt image 0x1c40 = some (.base (.LD .x10 .x7 0)) ∧
    Keygen.instructionAt image 0x1c44 = some (.base (.LD .x11 .x7 8)) ∧
    Keygen.instructionAt image 0x1c48 = some (.base (.LUI .x7 0x80)) ∧
    Keygen.instructionAt image 0x1c4c = some (.base (.ADDI .x7 .x7 0x500)) ∧
    Keygen.instructionAt image 0x1c50 = some (.base (.SD .x7 .x10 0)) ∧
    Keygen.instructionAt image 0x1c54 = some (.base (.SD .x7 .x11 8)) ∧
    Keygen.instructionAt image 0x1c58 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1c5c = some (.base (.ADDI .x28 .x28 0xf8)) ∧
    Keygen.instructionAt image 0x1c60 = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x1c64 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1c68 = some (.base (.ADDI .x28 .x28 0x60)) ∧
    Keygen.instructionAt image 0x1c6c = some (.base (.LD .x7 .x28 0)) ∧
    Keygen.instructionAt image 0x1c70 = some (.base (.SLLI .x7 .x7 4)) ∧
    Keygen.instructionAt image 0x1c74 = some (.base (.ADD .x6 .x6 .x7)) ∧
    Keygen.instructionAt image 0x1c78 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1c7c = some (.base (.ADDI .x28 .x28 0xf0)) ∧
    Keygen.instructionAt image 0x1c80 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1c84 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x1c88 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1c8c = some (.base (.ADDI .x28 .x28 0x100)) ∧
    Keygen.instructionAt image 0x1c90 = some (.base (.SD .x28 .x6 0)) := by decide

theorem post_steps (s : MachineState) (pc : s.pc = 0x1c34)
    (valid0 : accessValid (s.getMem 0x810c0) 8 = true)
    (valid8 : accessValid (s.getMem 0x810c0 + 8) 8 = true) :
    OrdinarySteps image s 24 (postState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0xc0)
  let s3 := execInstrBr s2 (.LD .x7 .x28 0)
  let s4 := execInstrBr s3 (.LD .x10 .x7 0)
  let s5 := execInstrBr s4 (.LD .x11 .x7 8)
  let s6 := execInstrBr s5 (.LUI .x7 0x80)
  let s7 := execInstrBr s6 (.ADDI .x7 .x7 0x500)
  let s8 := execInstrBr s7 (.SD .x7 .x10 0)
  let s9 := execInstrBr s8 (.SD .x7 .x11 8)
  let s10 := execInstrBr s9 (.LUI .x28 0x81)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 0xf8)
  let s12 := execInstrBr s11 (.LD .x6 .x28 0)
  let s13 := execInstrBr s12 (.LUI .x28 0x81)
  let s14 := execInstrBr s13 (.ADDI .x28 .x28 0x60)
  let s15 := execInstrBr s14 (.LD .x7 .x28 0)
  let s16 := execInstrBr s15 (.SLLI .x7 .x7 4)
  let s17 := execInstrBr s16 (.ADD .x6 .x6 .x7)
  let s18 := execInstrBr s17 (.LUI .x28 0x81)
  let s19 := execInstrBr s18 (.ADDI .x28 .x28 0xf0)
  let s20 := execInstrBr s19 (.SD .x28 .x6 0)
  let s21 := execInstrBr s20 (.ADDI .x6 .x0 0)
  let s22 := execInstrBr s21 (.LUI .x28 0x81)
  let s23 := execInstrBr s22 (.ADDI .x28 .x28 0x100)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23⟩ := post_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 23
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0xc0)) 22
  · have hp : s1.pc = 0x1c38 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x7 .x28 0)) 21
  · have hp : s2.pc = 0x1c3c := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simpa [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      accessValid,rangeValid,MEMORY_BYTES] using (by decide : accessValid (0x810c0 : Word) 8 = true)
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x10 .x7 0)) 20
  · have hp : s3.pc = 0x1c40 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simpa [s1,s2,s3,s4,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      accessValid,rangeValid,MEMORY_BYTES] using valid0
  apply OrdinarySteps.step s4 s5 _ (.base (.LD .x11 .x7 8)) 19
  · have hp : s4.pc = 0x1c44 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · simpa [s1,s2,s3,s4,s5,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      accessValid,rangeValid,MEMORY_BYTES] using valid8
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x7 0x80)) 18
  · have hp : s5.pc = 0x1c48 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x7 .x7 0x500)) 17
  · have hp : s6.pc = 0x1c4c := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x7 .x10 0)) 16
  · have hp : s7.pc = 0x1c50 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · simpa [s1,s2,s3,s4,s5,s6,s7,s8,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      accessValid,rangeValid,MEMORY_BYTES] using (by decide : accessValid (0x80500 : Word) 8 = true)
  apply OrdinarySteps.step s8 s9 _ (.base (.SD .x7 .x11 8)) 15
  · have hp : s8.pc = 0x1c54 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · simpa [s1,s2,s3,s4,s5,s6,s7,s8,s9,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      accessValid,rangeValid,MEMORY_BYTES] using (by decide : accessValid (0x80508 : Word) 8 = true)
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 0x81)) 14
  · have hp : s9.pc = 0x1c58 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 0xf8)) 13
  · have hp : s10.pc = 0x1c5c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.LD .x6 .x28 0)) 12
  · have hp : s11.pc = 0x1c60 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · simpa [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      accessValid,rangeValid,MEMORY_BYTES] using (by decide : accessValid (0x810f8 : Word) 8 = true)
  apply OrdinarySteps.step s12 s13 _ (.base (.LUI .x28 0x81)) 11
  · have hp : s12.pc = 0x1c64 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.ADDI .x28 .x28 0x60)) 10
  · have hp : s13.pc = 0x1c68 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.LD .x7 .x28 0)) 9
  · have hp : s14.pc = 0x1c6c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · simpa [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      accessValid,rangeValid,MEMORY_BYTES] using (by decide : accessValid (0x81060 : Word) 8 = true)
  apply OrdinarySteps.step s15 s16 _ (.base (.SLLI .x7 .x7 4)) 8
  · have hp : s15.pc = 0x1c70 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.ADD .x6 .x6 .x7)) 7
  · have hp : s16.pc = 0x1c74 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.LUI .x28 0x81)) 6
  · have hp : s17.pc = 0x1c78 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.ADDI .x28 .x28 0xf0)) 5
  · have hp : s18.pc = 0x1c7c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · rfl
  apply OrdinarySteps.step s19 s20 _ (.base (.SD .x28 .x6 0)) 4
  · have hp : s19.pc = 0x1c80 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · simpa [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      accessValid,rangeValid,MEMORY_BYTES] using (by decide : accessValid (0x810f0 : Word) 8 = true)
  apply OrdinarySteps.step s20 s21 _ (.base (.ADDI .x6 .x0 0)) 3
  · have hp : s20.pc = 0x1c84 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · rfl
  apply OrdinarySteps.step s21 s22 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s21.pc = 0x1c88 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c21
  · rfl
  apply OrdinarySteps.step s22 s23 _ (.base (.ADDI .x28 .x28 0x100)) 1
  · have hp : s22.pc = 0x1c8c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c22
  · rfl
  apply OrdinarySteps.step s23 (postState s) _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s23.pc = 0x1c90 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c23
  · simpa [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,postState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      accessValid,rangeValid,MEMORY_BYTES] using (by decide : accessValid (0x81100 : Word) 8 = true)
  exact OrdinarySteps.refl _


#print axioms post_pc
#print axioms post_steps
#print axioms post_words
#print axioms post_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperPostRoot67
