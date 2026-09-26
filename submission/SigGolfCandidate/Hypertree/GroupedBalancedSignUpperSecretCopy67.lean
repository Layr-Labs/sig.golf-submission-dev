import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperChainZero67
import SigGolfCandidate.Hypertree.SignCopy
import SigGolfCandidate.Hypertree.KeygenCopyX2X19


/-! Even WOTS chains derive the shared pair index for their H1 secret. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperPairIndex67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

def pairState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.SRLI .x6 .x19 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x30)
  execInstrBr s (.SD .x28 .x6 0)

private theorem pair_code :
    Keygen.instructionAt image 0x1778 = some (.base (.SRLI .x6 .x19 1)) ∧
    Keygen.instructionAt image 0x177c = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1780 = some (.base (.ADDI .x28 .x28 0x30)) ∧
    Keygen.instructionAt image 0x1784 = some (.base (.SD .x28 .x6 0)) := by decide

theorem pair_steps (s : MachineState) (pc : s.pc = 0x1778) :
    OrdinarySteps image s 4 (pairState s) := by
  let s1 := execInstrBr s (.SRLI .x6 .x19 1)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0x30)
  obtain ⟨c0,c1,c2,c3⟩ := pair_code
  apply OrdinarySteps.step s s1 _ (.base (.SRLI .x6 .x19 1)) 3
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 2
  · simpa [Keygen.fetch_at,s1,execInstrBr,pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0x30)) 1
  · simpa [Keygen.fetch_at,s1,s2,execInstrBr,pc] using c2
  · rfl
  apply OrdinarySteps.step s3 (pairState s) _ (.base (.SD .x28 .x6 0)) 0
  · simpa [Keygen.fetch_at,s1,s2,s3,execInstrBr,pc] using c3
  · have haddr : s3.getReg .x28 = 0x81030 := by
      simp [s1,s2,s3,execInstrBr,MachineState.getReg_setReg_eq,signExtend12]
    change (if accessValid (s3.getReg .x28 + signExtend12 (0 : BitVec 12)) 8
      then some (pairState s) else none) = some (pairState s)
    simp [haddr,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem pair_pc (s : MachineState) (pc : s.pc = 0x1778) :
    (pairState s).pc = 0x1788 := by
  simp [pairState,execInstrBr,pc]

theorem pair_index (s : MachineState) :
    (pairState s).getMem 0x81030 = s.getReg .x19 >>> 1 := by
  simp [pairState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem pair_frame (s : MachineState) (a : Word) (ha : a ≠ 0x81030) :
    (pairState s).getMem a = s.getMem a := by
  simp [pairState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  intro eq
  exact False.elim (ha eq)

#print axioms pair_steps
#print axioms pair_pc
#print axioms pair_index
#print axioms pair_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperPairIndex67


/-! Copy the 32-byte signer secret key into the paired-chain H1 input. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSecretCopy67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def setupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0x20)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x20)
  execInstrBr s (.ADDI .x10 .x0 4)

private theorem setup_code :
    Keygen.instructionAt image 0x1788 = some (.base (.ADDI .x6 .x0 0x20)) ∧
    Keygen.instructionAt image 0x178c = some (.base (.LUI .x7 0x80)) ∧
    Keygen.instructionAt image 0x1790 = some (.base (.ADDI .x7 .x7 0x20)) ∧
    Keygen.instructionAt image 0x1794 = some (.base (.ADDI .x10 .x0 4)) := by decide

theorem setup_steps (s : MachineState) (pc : s.pc = 0x1788) :
    OrdinarySteps image s 4 (setupState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0x20)
  let s2 := execInstrBr s1 (.LUI .x7 0x80)
  let s3 := execInstrBr s2 (.ADDI .x7 .x7 0x20)
  obtain ⟨c0,c1,c2,c3⟩ := setup_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0x20)) 3
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x7 0x80)) 2
  · simpa [Keygen.fetch_at,s1,execInstrBr,pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x7 .x7 0x20)) 1
  · simpa [Keygen.fetch_at,s1,s2,execInstrBr,pc] using c2
  · rfl
  apply OrdinarySteps.step s3 (setupState s) _ (.base (.ADDI .x10 .x0 4)) 0
  · simpa [Keygen.fetch_at,s1,s2,s3,execInstrBr,pc] using c3
  · rfl
  exact OrdinarySteps.refl _

theorem copy_code : Keygen.CopyCode image 0x1798 := by decide

theorem copy_inv (s : MachineState) (pc : s.pc = 0x1788) :
    Keygen.CopyInvariant 0x1798 0x20 0x80020 4 4 (setupState s) := by
  unfold Keygen.CopyInvariant setupState
  simp [execInstrBr,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,signExtend12,pc]

theorem secret_copy (s : MachineState) (pc : s.pc = 0x1788) :
    ∃ final, OrdinarySteps image s 28 final ∧ final.pc = 0x17b0 ∧
      (∀ i, i < 4 → final.getMem (Signing.wordAddress 0x80020 i) =
        s.getMem (Signing.wordAddress 0x20 i)) ∧
      (∀ a, (∀ i, i < 4 → a ≠ Signing.wordAddress 0x80020 i) →
        final.getMem a = s.getMem a) ∧
      final.getReg .x19 = s.getReg .x19 ∧
      final.getReg .x2 = s.getReg .x2 := by
  let begun := setupState s
  obtain ⟨final,loop,done,words,frame,x19,sp⟩ :=
    KeygenCopyX2X19.copy_all_x19_x2 image
    0x1798 copy_code 0x20 0x80020 4 begun
    (copy_inv s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final,?_,done.2.2.1,?_,?_,?_,?_⟩
  · have full := Keygen.ordinary_trans image s begun final 4 24
      (setup_steps s pc) loop
    simpa only [show 24+4=28 by decide] using full
  · intro i hi
    rw [words i hi]
    simp [begun,setupState,execInstrBr]
  · intro a outside
    rw [frame a outside]
    simp [begun,setupState,execInstrBr]
  · rw [x19]
    simp [begun,setupState,execInstrBr,MachineState.getReg_setReg_ne]
  · rw [sp]
    simp [begun,setupState,execInstrBr,MachineState.getReg_setReg_ne]

#print axioms secret_copy
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSecretCopy67
