import SigGolfCandidate.Hypertree.GroupedBalancedSignImage67Byte
import SigGolfCandidate.Hypertree.KeygenBlocks
import SigGolfCandidate.Hypertree.SignCopy

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperEntryH367; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCopiesH367. -/
section
/-! Extract the low upper-group bits and the rounded group address. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperEntryH367
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67Byte.image

def entryState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x90)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ANDI .x7 .x6 0x7)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xe8)
  let s := execInstrBr s (.SD .x28 .x7 0)
  let s := execInstrBr s (.ANDI .x6 .x6 (-8))
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xa8)
  execInstrBr s (.SD .x28 .x6 0)

private theorem entry_code :
    Keygen.instructionAt image 0x15f4 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x15f8 = some (.base (.ADDI .x28 .x28 0x90)) ∧
    Keygen.instructionAt image 0x15fc = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x1600 = some (.base (.ANDI .x7 .x6 0x7)) ∧
    Keygen.instructionAt image 0x1604 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1608 = some (.base (.ADDI .x28 .x28 0xe8)) ∧
    Keygen.instructionAt image 0x160c = some (.base (.SD .x28 .x7 0)) ∧
    Keygen.instructionAt image 0x1610 = some (.base (.ANDI .x6 .x6 (-8))) ∧
    Keygen.instructionAt image 0x1614 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1618 = some (.base (.ADDI .x28 .x28 0xa8)) ∧
    Keygen.instructionAt image 0x161c = some (.base (.SD .x28 .x6 0)) := by
  decide

theorem entry_steps (s : MachineState) (pc : s.pc = 0x15f4) :
    OrdinarySteps image s 11 (entryState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x90)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ANDI .x7 .x6 0x7)
  let s5 := execInstrBr s4 (.LUI .x28 0x81)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 0xe8)
  let s7 := execInstrBr s6 (.SD .x28 .x7 0)
  let s8 := execInstrBr s7 (.ANDI .x6 .x6 (-8))
  let s9 := execInstrBr s8 (.LUI .x28 0x81)
  let s10 := execInstrBr s9 (.ADDI .x28 .x28 0xa8)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10⟩ := entry_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 10
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x90)) 9
  · have hp : s1.pc = 0x15f8 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 8
  · have hp : s2.pc = 0x15fc := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,entryState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ANDI .x7 .x6 0x7)) 7
  · have hp : s3.pc = 0x1600 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x81)) 6
  · have hp : s4.pc = 0x1604 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 0xe8)) 5
  · have hp : s5.pc = 0x1608 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x7 0)) 4
  · have hp : s6.pc = 0x160c := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · simp [s1,s2,s3,s4,s5,s6,s7,entryState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 s8 _ (.base (.ANDI .x6 .x6 (-8))) 3
  · have hp : s7.pc = 0x1610 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s8.pc = 0x1614 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x28 .x28 0xa8)) 1
  · have hp : s9.pc = 0x1618 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 (entryState s) _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s10.pc = 0x161c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,entryState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem entry_pc (s : MachineState) (pc : s.pc = 0x15f4) :
    (entryState s).pc = 0x1620 := by
  simp [entryState,execInstrBr,pc]

theorem entry_selected (s : MachineState) :
    (entryState s).getMem 0x810e8 =
      (s.getMem 0x81090 &&& 7#64) := by
  simp [entryState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem entry_rounded (s : MachineState) :
    (entryState s).getMem 0x810a8 =
      (s.getMem 0x81090 &&& 18446744073709551608#64) := by
  simp [entryState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem entry_frame (s : MachineState) (a : Word)
    (selected : a ≠ 0x810e8) (rounded : a ≠ 0x810a8) :
    (entryState s).getMem a = s.getMem a := by
  change a ≠ 528616#64 at selected
  change a ≠ 528552#64 at rounded
  simp [entryState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    selected,rounded]

#print axioms entry_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperEntryH367

end

/-! Copy the high selected-index words and the rounded upper-group address. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCopiesH367
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67Byte.image

def upperSetup (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x81)
  let s := execInstrBr s (.ADDI .x6 .x6 0x98)
  let s := execInstrBr s (.LUI .x7 0x81)
  let s := execInstrBr s (.ADDI .x7 .x7 0xb0)
  execInstrBr s (.ADDI .x10 .x0 2)
private theorem upper_setup_code :
    Keygen.instructionAt image 0x1620 = some (.base (.LUI .x6 0x81)) ∧
    Keygen.instructionAt image 0x1624 = some (.base (.ADDI .x6 .x6 0x98)) ∧
    Keygen.instructionAt image 0x1628 = some (.base (.LUI .x7 0x81)) ∧
    Keygen.instructionAt image 0x162c = some (.base (.ADDI .x7 .x7 0xb0)) ∧
    Keygen.instructionAt image 0x1630 = some (.base (.ADDI .x10 .x0 2)) := by
  decide
theorem upper_setup_steps (s : MachineState) (pc : s.pc = 0x1620) :
    OrdinarySteps image s 5 (upperSetup s) := by
  let s1 := execInstrBr s (.LUI .x6 0x81)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x98)
  let s3 := execInstrBr s2 (.LUI .x7 0x81)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0xb0)
  obtain ⟨c0,c1,c2,c3,c4⟩ := upper_setup_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x81)) 4
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x98)) 3
  · have hp : s1.pc = 0x1624 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x81)) 2
  · have hp : s2.pc = 0x1628 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0xb0)) 1
  · have hp : s3.pc = 0x162c := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 (upperSetup s) _ (.base (.ADDI .x10 .x0 2)) 0
  · have hp : s4.pc = 0x1630 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  exact OrdinarySteps.refl _
theorem upper_copy_code : Keygen.CopyCode image 0x1634 := by decide
theorem upper_copy_inv (s : MachineState) (pc : s.pc = 0x1620) :
    Keygen.CopyInvariant 0x1634 0x81098 0x810b0 2 2 (upperSetup s) := by
  unfold Keygen.CopyInvariant upperSetup
  simp [execInstrBr,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,signExtend12,pc]
theorem upper_copy (s : MachineState) (pc : s.pc = 0x1620) :
    ∃ final, OrdinarySteps image s 17 final ∧ final.pc = 0x164c ∧
      (∀ i, i < 2 → final.getMem (Signing.wordAddress 0x810b0 i) =
        s.getMem (Signing.wordAddress 0x81098 i)) ∧
      (∀ a, (∀ i, i < 2 → a ≠ Signing.wordAddress 0x810b0 i) →
        final.getMem a = s.getMem a) := by
  let begun := upperSetup s
  obtain ⟨final,loop,done,words,frame⟩ := Signing.copy_all image
    0x1634 upper_copy_code 0x81098 0x810b0 2 begun
    (upper_copy_inv s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final,?_,done.2.2.1,?_,?_⟩
  · have full := Keygen.ordinary_trans image s begun final 5 12
      (upper_setup_steps s pc) loop
    simpa only [show 12 + 5 = 17 by decide] using full
  · intro i hi
    rw [words i hi]
    simp [begun,upperSetup,execInstrBr]
  · intro a outside
    rw [frame a outside]
    simp [begun,upperSetup,execInstrBr]

def baseSetup (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x81)
  let s := execInstrBr s (.ADDI .x6 .x6 0xa8)
  let s := execInstrBr s (.LUI .x7 0x81)
  let s := execInstrBr s (.ADDI .x7 .x7 0x8)
  execInstrBr s (.ADDI .x10 .x0 3)
private theorem base_setup_code :
    Keygen.instructionAt image 0x164c = some (.base (.LUI .x6 0x81)) ∧
    Keygen.instructionAt image 0x1650 = some (.base (.ADDI .x6 .x6 0xa8)) ∧
    Keygen.instructionAt image 0x1654 = some (.base (.LUI .x7 0x81)) ∧
    Keygen.instructionAt image 0x1658 = some (.base (.ADDI .x7 .x7 0x8)) ∧
    Keygen.instructionAt image 0x165c = some (.base (.ADDI .x10 .x0 3)) := by
  decide
theorem base_setup_steps (s : MachineState) (pc : s.pc = 0x164c) :
    OrdinarySteps image s 5 (baseSetup s) := by
  let s1 := execInstrBr s (.LUI .x6 0x81)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0xa8)
  let s3 := execInstrBr s2 (.LUI .x7 0x81)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0x8)
  obtain ⟨c0,c1,c2,c3,c4⟩ := base_setup_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x81)) 4
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0xa8)) 3
  · have hp : s1.pc = 0x1650 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x81)) 2
  · have hp : s2.pc = 0x1654 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0x8)) 1
  · have hp : s3.pc = 0x1658 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 (baseSetup s) _ (.base (.ADDI .x10 .x0 3)) 0
  · have hp : s4.pc = 0x165c := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  exact OrdinarySteps.refl _
theorem base_copy_code : Keygen.CopyCode image 0x1660 := by decide
theorem base_copy_inv (s : MachineState) (pc : s.pc = 0x164c) :
    Keygen.CopyInvariant 0x1660 0x810a8 0x81008 3 3 (baseSetup s) := by
  unfold Keygen.CopyInvariant baseSetup
  simp [execInstrBr,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,signExtend12,pc]
theorem base_copy (s : MachineState) (pc : s.pc = 0x164c) :
    ∃ final, OrdinarySteps image s 23 final ∧ final.pc = 0x1678 ∧
      (∀ i, i < 3 → final.getMem (Signing.wordAddress 0x81008 i) =
        s.getMem (Signing.wordAddress 0x810a8 i)) ∧
      (∀ a, (∀ i, i < 3 → a ≠ Signing.wordAddress 0x81008 i) →
        final.getMem a = s.getMem a) := by
  let begun := baseSetup s
  obtain ⟨final,loop,done,words,frame⟩ := Signing.copy_all image
    0x1660 base_copy_code 0x810a8 0x81008 3 begun
    (base_copy_inv s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final,?_,done.2.2.1,?_,?_⟩
  · have full := Keygen.ordinary_trans image s begun final 5 18
      (base_setup_steps s pc) loop
    simpa only [show 18 + 5 = 23 by decide] using full
  · intro i hi
    rw [words i hi]
    simp [begun,baseSetup,execInstrBr]
  · intro a outside
    rw [frame a outside]
    simp [begun,baseSetup,execInstrBr]

#print axioms upper_copy
#print axioms base_copy
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCopiesH367
