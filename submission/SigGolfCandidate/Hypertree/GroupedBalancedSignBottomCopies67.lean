import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomH1Query67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomEntry67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomCopies67. -/
section
/-! Extract the low ten bottom bits and the rounded bottom address. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomEntry67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image

def entryState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x90)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ANDI .x7 .x6 0x3ff)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xe8)
  let s := execInstrBr s (.SD .x28 .x7 0)
  let s := execInstrBr s (.ANDI .x6 .x6 (-1024))
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xa8)
  execInstrBr s (.SD .x28 .x6 0)

private theorem entry_code :
    Keygen.instructionAt image 0x11f4 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x11f8 = some (.base (.ADDI .x28 .x28 0x90)) ∧
    Keygen.instructionAt image 0x11fc = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x1200 = some (.base (.ANDI .x7 .x6 0x3ff)) ∧
    Keygen.instructionAt image 0x1204 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1208 = some (.base (.ADDI .x28 .x28 0xe8)) ∧
    Keygen.instructionAt image 0x120c = some (.base (.SD .x28 .x7 0)) ∧
    Keygen.instructionAt image 0x1210 = some (.base (.ANDI .x6 .x6 (-1024))) ∧
    Keygen.instructionAt image 0x1214 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1218 = some (.base (.ADDI .x28 .x28 0xa8)) ∧
    Keygen.instructionAt image 0x121c = some (.base (.SD .x28 .x6 0)) := by
  decide

theorem entry_steps (s : MachineState) (pc : s.pc = 0x11f4) :
    OrdinarySteps image s 11 (entryState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x90)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ANDI .x7 .x6 0x3ff)
  let s5 := execInstrBr s4 (.LUI .x28 0x81)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 0xe8)
  let s7 := execInstrBr s6 (.SD .x28 .x7 0)
  let s8 := execInstrBr s7 (.ANDI .x6 .x6 (-1024))
  let s9 := execInstrBr s8 (.LUI .x28 0x81)
  let s10 := execInstrBr s9 (.ADDI .x28 .x28 0xa8)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10⟩ := entry_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 10
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x90)) 9
  · have hp : s1.pc = 0x11f8 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 8
  · have hp : s2.pc = 0x11fc := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,entryState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ANDI .x7 .x6 0x3ff)) 7
  · have hp : s3.pc = 0x1200 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x81)) 6
  · have hp : s4.pc = 0x1204 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 0xe8)) 5
  · have hp : s5.pc = 0x1208 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x7 0)) 4
  · have hp : s6.pc = 0x120c := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · simp [s1,s2,s3,s4,s5,s6,s7,entryState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 s8 _ (.base (.ANDI .x6 .x6 (-1024))) 3
  · have hp : s7.pc = 0x1210 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s8.pc = 0x1214 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x28 .x28 0xa8)) 1
  · have hp : s9.pc = 0x1218 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 (entryState s) _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s10.pc = 0x121c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,entryState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem entry_pc (s : MachineState) (pc : s.pc = 0x11f4) :
    (entryState s).pc = 0x1220 := by
  simp [entryState,execInstrBr,pc]

theorem entry_selected (s : MachineState) :
    (entryState s).getMem 0x810e8 =
      (s.getMem 0x81090 &&& 1023#64) := by
  simp [entryState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem entry_rounded (s : MachineState) :
    (entryState s).getMem 0x810a8 =
      (s.getMem 0x81090 &&& 18446744073709550592#64) := by
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
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomEntry67

end

/-! Copy the high index words and then the rounded 160-bit bottom address. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomCopies67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image

def upperSetup (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x81)
  let s := execInstrBr s (.ADDI .x6 .x6 0x98)
  let s := execInstrBr s (.LUI .x7 0x81)
  let s := execInstrBr s (.ADDI .x7 .x7 0xb0)
  execInstrBr s (.ADDI .x10 .x0 2)
private theorem upper_setup_code :
    Keygen.instructionAt image 0x1220 = some (.base (.LUI .x6 0x81)) ∧
    Keygen.instructionAt image 0x1224 = some (.base (.ADDI .x6 .x6 0x98)) ∧
    Keygen.instructionAt image 0x1228 = some (.base (.LUI .x7 0x81)) ∧
    Keygen.instructionAt image 0x122c = some (.base (.ADDI .x7 .x7 0xb0)) ∧
    Keygen.instructionAt image 0x1230 = some (.base (.ADDI .x10 .x0 2)) := by
  decide
theorem upper_setup_steps (s : MachineState) (pc : s.pc = 0x1220) :
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
  · have hp : s1.pc = 0x1224 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x81)) 2
  · have hp : s2.pc = 0x1228 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0xb0)) 1
  · have hp : s3.pc = 0x122c := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 (upperSetup s) _ (.base (.ADDI .x10 .x0 2)) 0
  · have hp : s4.pc = 0x1230 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  exact OrdinarySteps.refl _
theorem upper_copy_code : Keygen.CopyCode image 0x1234 := by decide
theorem upper_copy_inv (s : MachineState) (pc : s.pc = 0x1220) :
    Keygen.CopyInvariant 0x1234 0x81098 0x810b0 2 2 (upperSetup s) := by
  unfold Keygen.CopyInvariant upperSetup
  simp [execInstrBr,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,signExtend12,pc]
theorem upper_copy (s : MachineState) (pc : s.pc = 0x1220) :
    ∃ final, OrdinarySteps image s 17 final ∧ final.pc = 0x124c ∧
      (∀ i, i < 2 → final.getMem (Signing.wordAddress 0x810b0 i) =
        s.getMem (Signing.wordAddress 0x81098 i)) ∧
      (∀ a, (∀ i, i < 2 → a ≠ Signing.wordAddress 0x810b0 i) →
        final.getMem a = s.getMem a) := by
  let begun := upperSetup s
  obtain ⟨final,loop,done,words,frame⟩ := Signing.copy_all image
    0x1234 upper_copy_code 0x81098 0x810b0 2 begun
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
    Keygen.instructionAt image 0x124c = some (.base (.LUI .x6 0x81)) ∧
    Keygen.instructionAt image 0x1250 = some (.base (.ADDI .x6 .x6 0xa8)) ∧
    Keygen.instructionAt image 0x1254 = some (.base (.LUI .x7 0x81)) ∧
    Keygen.instructionAt image 0x1258 = some (.base (.ADDI .x7 .x7 0x8)) ∧
    Keygen.instructionAt image 0x125c = some (.base (.ADDI .x10 .x0 3)) := by
  decide
theorem base_setup_steps (s : MachineState) (pc : s.pc = 0x124c) :
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
  · have hp : s1.pc = 0x1250 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x81)) 2
  · have hp : s2.pc = 0x1254 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0x8)) 1
  · have hp : s3.pc = 0x1258 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 (baseSetup s) _ (.base (.ADDI .x10 .x0 3)) 0
  · have hp : s4.pc = 0x125c := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  exact OrdinarySteps.refl _
theorem base_copy_code : Keygen.CopyCode image 0x1260 := by decide
theorem base_copy_inv (s : MachineState) (pc : s.pc = 0x124c) :
    Keygen.CopyInvariant 0x1260 0x810a8 0x81008 3 3 (baseSetup s) := by
  unfold Keygen.CopyInvariant baseSetup
  simp [execInstrBr,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,signExtend12,pc]
theorem base_copy (s : MachineState) (pc : s.pc = 0x124c) :
    ∃ final, OrdinarySteps image s 23 final ∧ final.pc = 0x1278 ∧
      (∀ i, i < 3 → final.getMem (Signing.wordAddress 0x81008 i) =
        s.getMem (Signing.wordAddress 0x810a8 i)) ∧
      (∀ a, (∀ i, i < 3 → a ≠ Signing.wordAddress 0x81008 i) →
        final.getMem a = s.getMem a) := by
  let begun := baseSetup s
  obtain ⟨final,loop,done,words,frame⟩ := Signing.copy_all image
    0x1260 base_copy_code 0x810a8 0x81008 3 begun
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
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomCopies67
