import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedDispatch67
import SigGolfCandidate.Hypertree.SignCopy
import SigGolfCandidate.Hypertree.KeygenCopyX19
import SigGolfCandidate.Hypertree.KeygenCopyX2X19

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedOdd67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def setupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x81)
  let s := execInstrBr s (.ADDI .x6 .x6 0xd10)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x20)
  execInstrBr s (.ADDI .x10 .x0 2)

private theorem setup_code :
    Keygen.instructionAt image 0x188c = some (.base (.LUI .x6 0x81)) ∧
    Keygen.instructionAt image 0x1890 = some (.base (.ADDI .x6 .x6 0xd10)) ∧
    Keygen.instructionAt image 0x1894 = some (.base (.LUI .x7 0x80)) ∧
    Keygen.instructionAt image 0x1898 = some (.base (.ADDI .x7 .x7 0x20)) ∧
    Keygen.instructionAt image 0x189c = some (.base (.ADDI .x10 .x0 2)) := by decide

theorem setup_steps (s : MachineState) (pc : s.pc = 0x188c) :
    OrdinarySteps image s 5 (setupState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x81)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0xd10)
  let s3 := execInstrBr s2 (.LUI .x7 0x80)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0x20)
  obtain ⟨c0,c1,c2,c3,c4⟩ := setup_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x81)) 4
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0xd10)) 3
  · simpa [Keygen.fetch_at,s1,execInstrBr,pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x80)) 2
  · simpa [Keygen.fetch_at,s1,s2,execInstrBr,pc] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0x20)) 1
  · simpa [Keygen.fetch_at,s1,s2,s3,execInstrBr,pc] using c3
  · rfl
  apply OrdinarySteps.step s4 (setupState s) _ (.base (.ADDI .x10 .x0 2)) 0
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,execInstrBr,pc] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem setup_pc (s : MachineState) (pc : s.pc = 0x188c) :
    (setupState s).pc = 0x18a0 := by
  simp [setupState,execInstrBr,pc]

theorem setup_frame (s : MachineState) (a : Word) :
    (setupState s).getMem a = s.getMem a := by
  simp [setupState,execInstrBr]

theorem copy_code : Keygen.CopyCode image 0x18a0 := by decide

theorem copy_inv (s : MachineState) (pc : s.pc = 0x188c) :
    Keygen.CopyInvariant 0x18a0 0x80d10 0x80020 2 2 (setupState s) := by
  unfold Keygen.CopyInvariant setupState
  simp [execInstrBr,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,signExtend12,pc]

theorem seed_copy (s : MachineState) (pc : s.pc = 0x188c) :
    ∃ final, OrdinarySteps image s 17 final ∧ final.pc = 0x18b8 ∧
      final.getReg .x19 = s.getReg .x19 ∧
      final.getReg .x2 = s.getReg .x2 ∧
      (∀ i, i < 2 → final.getMem (Signing.wordAddress 0x80020 i) =
        s.getMem (Signing.wordAddress 0x80d10 i)) ∧
      (∀ a, (∀ i, i < 2 → a ≠ Signing.wordAddress 0x80020 i) →
        final.getMem a = s.getMem a) := by
  let begun := setupState s
  obtain ⟨final,loopTrace,done,words,frame,x19,sp⟩ :=
    KeygenCopyX2X19.copy_all_x19_x2 image
    0x18a0 copy_code 0x80d10 0x80020 2 begun
    (copy_inv s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final,?_,done.2.2.1,?_,?_,?_,?_⟩
  · have full := Keygen.ordinary_trans image s begun final 5 12
      (setup_steps s pc) loopTrace
    simpa only [Nat.reduceAdd] using full
  · rw [x19]
    simp [begun,setupState,execInstrBr,MachineState.getReg_setReg_ne]
  · rw [sp]
    simp [begun,setupState,execInstrBr,MachineState.getReg_setReg_ne]
  · intro i hi
    rw [words i hi,setup_frame]
  · intro a outside
    rw [frame a outside,setup_frame]

#print axioms seed_copy
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedOdd67
