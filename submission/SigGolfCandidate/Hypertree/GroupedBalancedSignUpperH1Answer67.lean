import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1Query67
import SigGolfCandidate.Hypertree.SignCopy
import SigGolfCandidate.Hypertree.KeygenCopyX19
import SigGolfCandidate.Hypertree.KeygenCopyX2X19

/-! Restore the chain index after H1 and retain the whole 256-bit paired
secret in the 0x80d00 scratch buffer. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1Answer67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def restoreState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x30)
  execInstrBr s (.SD .x28 .x19 0)

private theorem restore_code :
    Keygen.instructionAt image 0x184c = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1850 = some (.base (.ADDI .x28 .x28 0x30)) ∧
    Keygen.instructionAt image 0x1854 = some (.base (.SD .x28 .x19 0)) := by decide

theorem restore_steps (s : MachineState) (pc : s.pc = 0x184c) :
    OrdinarySteps image s 3 (restoreState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x30)
  obtain ⟨c0,c1,c2⟩ := restore_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 2
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x30)) 1
  · simpa [Keygen.fetch_at,s1,execInstrBr,pc] using c1
  · rfl
  apply OrdinarySteps.step s2 (restoreState s) _ (.base (.SD .x28 .x19 0)) 0
  · simpa [Keygen.fetch_at,s1,s2,execInstrBr,pc] using c2
  · have haddr : s2.getReg .x28 = 0x81030 := by
      simp [s1,s2,execInstrBr,MachineState.getReg_setReg_eq,signExtend12]
    change (if accessValid (s2.getReg .x28 + signExtend12 (0 : BitVec 12)) 8
      then some (restoreState s) else none) = some (restoreState s)
    simp [haddr,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem restore_pc (s : MachineState) (pc : s.pc = 0x184c) :
    (restoreState s).pc = 0x1858 := by
  simp [restoreState,execInstrBr,pc]

theorem restore_chain (s : MachineState) :
    (restoreState s).getMem 0x81030 = s.getReg .x19 := by
  simp [restoreState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem restore_frame (s : MachineState) (a : Word) (ha : a ≠ 0x81030) :
    (restoreState s).getMem a = s.getMem a := by
  change a ≠ 528432#64 at ha
  simp [restoreState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,ha]

def setupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x80)
  let s := execInstrBr s (.ADDI .x6 .x6 0x300)
  let s := execInstrBr s (.LUI .x7 0x81)
  let s := execInstrBr s (.ADDI .x7 .x7 0xd00)
  execInstrBr s (.ADDI .x10 .x0 4)

private theorem setup_code :
    Keygen.instructionAt image 0x1858 = some (.base (.LUI .x6 0x80)) ∧
    Keygen.instructionAt image 0x185c = some (.base (.ADDI .x6 .x6 0x300)) ∧
    Keygen.instructionAt image 0x1860 = some (.base (.LUI .x7 0x81)) ∧
    Keygen.instructionAt image 0x1864 = some (.base (.ADDI .x7 .x7 0xd00)) ∧
    Keygen.instructionAt image 0x1868 = some (.base (.ADDI .x10 .x0 4)) := by decide

theorem setup_steps (s : MachineState) (pc : s.pc = 0x1858) :
    OrdinarySteps image s 5 (setupState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x80)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x300)
  let s3 := execInstrBr s2 (.LUI .x7 0x81)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0xd00)
  obtain ⟨c0,c1,c2,c3,c4⟩ := setup_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x80)) 4
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x300)) 3
  · simpa [Keygen.fetch_at,s1,execInstrBr,pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x81)) 2
  · simpa [Keygen.fetch_at,s1,s2,execInstrBr,pc] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0xd00)) 1
  · simpa [Keygen.fetch_at,s1,s2,s3,execInstrBr,pc] using c3
  · rfl
  apply OrdinarySteps.step s4 (setupState s) _ (.base (.ADDI .x10 .x0 4)) 0
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,execInstrBr,pc] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem setup_pc (s : MachineState) (pc : s.pc = 0x1858) :
    (setupState s).pc = 0x186c := by
  simp [setupState,execInstrBr,pc]

theorem setup_frame (s : MachineState) (a : Word) :
    (setupState s).getMem a = s.getMem a := by
  simp [setupState,execInstrBr]

theorem copy_code : Keygen.CopyCode image 0x186c := by decide

theorem copy_inv (s : MachineState) (pc : s.pc = 0x1858) :
    Keygen.CopyInvariant 0x186c 0x80300 0x80d00 4 4 (setupState s) := by
  unfold Keygen.CopyInvariant setupState
  simp [execInstrBr,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,signExtend12,pc]

theorem answer_copy (s : MachineState) (pc : s.pc = 0x184c) :
    ∃ final, OrdinarySteps image s 32 final ∧ final.pc = 0x1884 ∧
      final.getReg .x19 = s.getReg .x19 ∧
      final.getReg .x2 = s.getReg .x2 ∧
      final.getMem 0x81030 = s.getReg .x19 ∧
      (∀ i, i < 4 → final.getMem (Signing.wordAddress 0x80d00 i) =
        s.getMem (Signing.wordAddress 0x80300 i)) ∧
      (∀ a, a ≠ 0x81030 →
        (∀ i, i < 4 → a ≠ Signing.wordAddress 0x80d00 i) →
        final.getMem a = s.getMem a) := by
  let restored := restoreState s
  let begun := setupState restored
  obtain ⟨final,loop,done,words,frame,x19,sp⟩ :=
    KeygenCopyX2X19.copy_all_x19_x2 image
    0x186c copy_code 0x80300 0x80d00 4 begun
    (copy_inv restored (restore_pc s pc))
    (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final,?_,done.2.2.1,?_,?_,?_,?_,?_⟩
  · have initial := Keygen.ordinary_trans image s restored begun 3 5
      (restore_steps s pc) (setup_steps restored (restore_pc s pc))
    have full := Keygen.ordinary_trans image s begun final 8 24
      (by simpa only [Nat.reduceAdd] using initial) loop
    simpa only [Nat.reduceAdd] using full
  · rw [x19]
    simp [begun,setupState,restored,restoreState,execInstrBr,
      MachineState.getReg_setReg_ne]
  · rw [sp]
    simp [begun,setupState,restored,restoreState,execInstrBr,
      MachineState.getReg_setReg_ne]
  · have hc := frame 0x81030 (by intro i hi; have : i < 4 := hi; interval_cases i <;> decide)
    rw [hc, setup_frame, restore_chain]
  · intro i hi
    rw [words i hi,setup_frame,restore_frame]
    have : i < 4 := hi
    interval_cases i <;> decide
  · intro a ha outside
    rw [frame a outside,setup_frame,restore_frame s a ha]

#print axioms answer_copy
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1Answer67
