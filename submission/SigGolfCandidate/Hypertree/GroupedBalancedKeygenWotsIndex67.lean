import SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstLeaf67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstHashMemory67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsHeader67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsIndex67. -/
section
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsHeader67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
def image : Image := GroupedBalancedKeygenImage67.image
def resetState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 56)
  let s := execInstrBr s (.SD .x28 .x6 0)
  s
private theorem reset_code :
    Keygen.instructionAt image 4568 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 4572 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 4576 = some (.base (.ADDI .x28 .x28 56)) ∧
    Keygen.instructionAt image 4580 = some (.base (.SD .x28 .x6 0)) :=
  by unfold image GroupedBalancedKeygenImage67.image; decide
theorem reset_steps (s : MachineState) (pc : s.pc = 4568) :
    OrdinarySteps image s 4 (resetState s) := by
  obtain ⟨c0,c1,c2,c3⟩ := reset_code
  let s1 := execInstrBr s (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 56)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0)) 3
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s1.pc = 4572 := by
      simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 56)) 1
  · have hp : s2.pc = 4576 := by
      simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 (resetState s) _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s3.pc = 4580 := by
      simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [s1,s2,s3,s4,resetState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem reset_fields (s : MachineState) (pc : s.pc = 0x11d8) :
    (resetState s).pc = 0x11e8 ∧
    (resetState s).getMem 0x81038 = 0 ∧
    (resetState s).getReg .x19 = s.getReg .x19 := by
  simp [resetState,execInstrBr,signExtend12,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq]

theorem reset_mem_other (s : MachineState) (a : Word)
    (hne : a ≠ 0x81038) :
    (resetState s).getMem a = s.getMem a := by
  simp [resetState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  intro same
  exact False.elim (hne same)

def headerState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x10 .x0 2)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SLLI .x11 .x11 8)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 48)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SLLI .x11 .x11 24)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 56)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SLLI .x11 .x11 32)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.SD .x28 .x10 0)
  s
private theorem header_code :
    Keygen.instructionAt image 4584 = some (.base (.ADDI .x10 .x0 2)) ∧
    Keygen.instructionAt image 4588 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 4592 = some (.base (.ADDI .x28 .x28 0)) ∧
    Keygen.instructionAt image 4596 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 4600 = some (.base (.SLLI .x11 .x11 8)) ∧
    Keygen.instructionAt image 4604 = some (.base (.ADD .x10 .x10 .x11)) ∧
    Keygen.instructionAt image 4608 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 4612 = some (.base (.ADDI .x28 .x28 48)) ∧
    Keygen.instructionAt image 4616 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 4620 = some (.base (.SLLI .x11 .x11 24)) ∧
    Keygen.instructionAt image 4624 = some (.base (.ADD .x10 .x10 .x11)) ∧
    Keygen.instructionAt image 4628 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 4632 = some (.base (.ADDI .x28 .x28 56)) ∧
    Keygen.instructionAt image 4636 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 4640 = some (.base (.SLLI .x11 .x11 32)) ∧
    Keygen.instructionAt image 4644 = some (.base (.ADD .x10 .x10 .x11)) ∧
    Keygen.instructionAt image 4648 = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 4652 = some (.base (.ADDI .x28 .x28 0)) ∧
    Keygen.instructionAt image 4656 = some (.base (.SD .x28 .x10 0)) :=
  by unfold image GroupedBalancedKeygenImage67.image; decide
theorem header_steps (s : MachineState) (pc : s.pc = 4584) :
    OrdinarySteps image s 19 (headerState s) := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18⟩ := header_code
  let s1 := execInstrBr s (.ADDI .x10 .x0 2)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0)
  let s4 := execInstrBr s3 (.LD .x11 .x28 0)
  let s5 := execInstrBr s4 (.SLLI .x11 .x11 8)
  let s6 := execInstrBr s5 (.ADD .x10 .x10 .x11)
  let s7 := execInstrBr s6 (.LUI .x28 0x81)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 48)
  let s9 := execInstrBr s8 (.LD .x11 .x28 0)
  let s10 := execInstrBr s9 (.SLLI .x11 .x11 24)
  let s11 := execInstrBr s10 (.ADD .x10 .x10 .x11)
  let s12 := execInstrBr s11 (.LUI .x28 0x81)
  let s13 := execInstrBr s12 (.ADDI .x28 .x28 56)
  let s14 := execInstrBr s13 (.LD .x11 .x28 0)
  let s15 := execInstrBr s14 (.SLLI .x11 .x11 32)
  let s16 := execInstrBr s15 (.ADD .x10 .x10 .x11)
  let s17 := execInstrBr s16 (.LUI .x28 0x80)
  let s18 := execInstrBr s17 (.ADDI .x28 .x28 0)
  let s19 := execInstrBr s18 (.SD .x28 .x10 0)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x10 .x0 2)) 18
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 17
  · have hp : s1.pc = 4588 := by
      simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 16
  · have hp : s2.pc = 4592 := by
      simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x11 .x28 0)) 15
  · have hp : s3.pc = 4596 := by
      simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [s1,s2,s3,s4,headerState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.SLLI .x11 .x11 8)) 14
  · have hp : s4.pc = 4600 := by
      simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADD .x10 .x10 .x11)) 13
  · have hp : s5.pc = 4604 := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x81)) 12
  · have hp : s6.pc = 4608 := by
      simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 48)) 11
  · have hp : s7.pc = 4612 := by
      simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LD .x11 .x28 0)) 10
  · have hp : s8.pc = 4616 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,headerState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.SLLI .x11 .x11 24)) 9
  · have hp : s9.pc = 4620 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADD .x10 .x10 .x11)) 8
  · have hp : s10.pc = 4624 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.LUI .x28 0x81)) 7
  · have hp : s11.pc = 4628 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x28 .x28 56)) 6
  · have hp : s12.pc = 4632 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.LD .x11 .x28 0)) 5
  · have hp : s13.pc = 4636 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,headerState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s14 s15 _ (.base (.SLLI .x11 .x11 32)) 4
  · have hp : s14.pc = 4640 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.ADD .x10 .x10 .x11)) 3
  · have hp : s15.pc = 4644 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.LUI .x28 0x80)) 2
  · have hp : s16.pc = 4648 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.ADDI .x28 .x28 0)) 1
  · have hp : s17.pc = 4652 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · rfl
  apply OrdinarySteps.step s18 (headerState s) _ (.base (.SD .x28 .x10 0)) 0
  · have hp : s18.pc = 4656 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,headerState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _
theorem header_fields (s : MachineState) (pc : s.pc = 0x11e8) :
    (headerState s).pc = 0x1234 ∧
    (headerState s).getMem 0x80000 =
      2 + (s.getMem 0x81000 <<< 8) +
        (s.getMem 0x81030 <<< 24) +
        (s.getMem 0x81038 <<< 32) := by
  simp [headerState,execInstrBr,signExtend12,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem header_mem_other (s : MachineState) (a : Word)
    (hne : a ≠ 0x80000) :
    (headerState s).getMem a = s.getMem a := by
  simp [headerState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  intro same
  exact False.elim (hne same)

#print axioms reset_fields
#print axioms header_fields

#print axioms reset_steps
#print axioms header_steps
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsHeader67

end

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsIndex67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstHash67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
def image : Image := GroupedBalancedKeygenImage67.image
private theorem index0_code :
    Keygen.instructionAt image 4660 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 4664 = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 4668 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 4672 = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 4676 = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 4680 = some (.base (.SD .x28 .x11 0)) :=
  by unfold image GroupedBalancedKeygenImage67.image; decide
theorem index0_steps (s : MachineState) (pc : s.pc = 4660) :
    OrdinarySteps image s 6 (index0State s) := by
  obtain ⟨c0,c1,c2,c3,c4,c5⟩ := index0_code
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 8)
  let s3 := execInstrBr s2 (.LD .x11 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x80)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 8)
  let s6 := execInstrBr s5 (.SD .x28 .x11 0)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 5
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 8)) 4
  · have hp : s1.pc = 4664 := by
      simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x11 .x28 0)) 3
  · have hp : s2.pc = 4668 := by
      simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,index0State,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x80)) 2
  · have hp : s3.pc = 4672 := by
      simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 8)) 1
  · have hp : s4.pc = 4676 := by
      simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 (index0State s) _ (.base (.SD .x28 .x11 0)) 0
  · have hp : s5.pc = 4680 := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · simp [s1,s2,s3,s4,s5,s6,index0State,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _
theorem index0_pc (s : MachineState) (pc : s.pc = 4660) :
    (index0State s).pc = 4684 := by
  simp [index0State,execInstrBr,pc]
private theorem index1_code :
    Keygen.instructionAt image 4684 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 4688 = some (.base (.ADDI .x28 .x28 16)) ∧
    Keygen.instructionAt image 4692 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 4696 = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 4700 = some (.base (.ADDI .x28 .x28 16)) ∧
    Keygen.instructionAt image 4704 = some (.base (.SD .x28 .x11 0)) :=
  by unfold image GroupedBalancedKeygenImage67.image; decide
theorem index1_steps (s : MachineState) (pc : s.pc = 4684) :
    OrdinarySteps image s 6 (index1State s) := by
  obtain ⟨c0,c1,c2,c3,c4,c5⟩ := index1_code
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 16)
  let s3 := execInstrBr s2 (.LD .x11 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x80)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 16)
  let s6 := execInstrBr s5 (.SD .x28 .x11 0)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 5
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 16)) 4
  · have hp : s1.pc = 4688 := by
      simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x11 .x28 0)) 3
  · have hp : s2.pc = 4692 := by
      simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,index1State,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x80)) 2
  · have hp : s3.pc = 4696 := by
      simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 16)) 1
  · have hp : s4.pc = 4700 := by
      simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 (index1State s) _ (.base (.SD .x28 .x11 0)) 0
  · have hp : s5.pc = 4704 := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · simp [s1,s2,s3,s4,s5,s6,index1State,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _
theorem index1_pc (s : MachineState) (pc : s.pc = 4684) :
    (index1State s).pc = 4708 := by
  simp [index1State,execInstrBr,pc]
private theorem index2_code :
    Keygen.instructionAt image 4708 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 4712 = some (.base (.ADDI .x28 .x28 24)) ∧
    Keygen.instructionAt image 4716 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 4720 = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 4724 = some (.base (.ADDI .x28 .x28 24)) ∧
    Keygen.instructionAt image 4728 = some (.base (.SD .x28 .x11 0)) :=
  by unfold image GroupedBalancedKeygenImage67.image; decide
theorem index2_steps (s : MachineState) (pc : s.pc = 4708) :
    OrdinarySteps image s 6 (index2State s) := by
  obtain ⟨c0,c1,c2,c3,c4,c5⟩ := index2_code
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 24)
  let s3 := execInstrBr s2 (.LD .x11 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x80)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 24)
  let s6 := execInstrBr s5 (.SD .x28 .x11 0)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 5
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 24)) 4
  · have hp : s1.pc = 4712 := by
      simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x11 .x28 0)) 3
  · have hp : s2.pc = 4716 := by
      simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,index2State,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x80)) 2
  · have hp : s3.pc = 4720 := by
      simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 24)) 1
  · have hp : s4.pc = 4724 := by
      simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 (index2State s) _ (.base (.SD .x28 .x11 0)) 0
  · have hp : s5.pc = 4728 := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · simp [s1,s2,s3,s4,s5,s6,index2State,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _
theorem index2_pc (s : MachineState) (pc : s.pc = 4708) :
    (index2State s).pc = 4732 := by
  simp [index2State,execInstrBr,pc]
def allState (s : MachineState) : MachineState :=
  index2State (index1State (index0State s))
theorem all_steps (s : MachineState) (pc : s.pc = 0x1234) :
    OrdinarySteps image s 18 (allState s) := by
  have first := index0_steps s pc
  have second := index1_steps (index0State s) (index0_pc s pc)
  have third := index2_steps (index1State (index0State s))
    (index1_pc (index0State s) (index0_pc s pc))
  simpa only [allState,Nat.reduceAdd] using
    Keygen.ordinary_trans image s (index1State (index0State s))
      (allState s) 12 6
      (Keygen.ordinary_trans image s (index0State s)
        (index1State (index0State s)) 6 6 first second) third
#print axioms all_steps
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsIndex67
