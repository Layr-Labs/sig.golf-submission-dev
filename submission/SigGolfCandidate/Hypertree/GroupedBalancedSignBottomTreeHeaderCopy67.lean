import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeIndexShift67
import SigGolfCandidate.Hypertree.SignShift
import SigGolfCandidate.Hypertree.SignCopy

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeIndexData67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeHeaderCopy67. -/
section
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeIndexData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67.image
def fullState (s : MachineState) : MachineState :=
  GroupedBalancedSignBottomTreeIndexShift67.shiftState
    (GroupedBalancedSignBottomTreeIndexLoad67.loadState s)
theorem full_steps (s : MachineState) (pc : s.pc = 0x1e04) :
    OrdinarySteps image s 25 (fullState s) := by
  have a := GroupedBalancedSignBottomTreeIndexLoad67.load_steps s pc
  have b := GroupedBalancedSignBottomTreeIndexShift67.shift_steps
    (GroupedBalancedSignBottomTreeIndexLoad67.loadState s)
    (GroupedBalancedSignBottomTreeIndexLoad67.load_pc s pc)
  exact Keygen.ordinary_trans image s
    (GroupedBalancedSignBottomTreeIndexLoad67.loadState s)
    (fullState s) 9 16 a b
theorem full_pc (s : MachineState) (pc : s.pc = 0x1e04) :
    (fullState s).pc = 0x1e68 := by
  exact GroupedBalancedSignBottomTreeIndexShift67.shift_pc
    (GroupedBalancedSignBottomTreeIndexLoad67.loadState s)
    (GroupedBalancedSignBottomTreeIndexLoad67.load_pc s pc)
theorem shifted_low (s : MachineState) :
    (fullState s).getMem 0x810a8 =
      (s.getMem 0x810a8 >>> 1) + (s.getMem 0x810b0 <<< 63) := by
  simp [fullState,GroupedBalancedSignBottomTreeIndexLoad67.loadState,
    GroupedBalancedSignBottomTreeIndexShift67.shiftState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem shifted_mid (s : MachineState) :
    (fullState s).getMem 0x810b0 =
      (s.getMem 0x810b0 >>> 1) + (s.getMem 0x810b8 <<< 63) := by
  simp [fullState,GroupedBalancedSignBottomTreeIndexLoad67.loadState,
    GroupedBalancedSignBottomTreeIndexShift67.shiftState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem shifted_high (s : MachineState) :
    (fullState s).getMem 0x810b8 = s.getMem 0x810b8 >>> 1 := by
  simp [fullState,GroupedBalancedSignBottomTreeIndexLoad67.loadState,
    GroupedBalancedSignBottomTreeIndexShift67.shiftState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem shift_frame (s : MachineState) (a : Word)
    (h0 : a ≠ 0x810a8) (h1 : a ≠ 0x810b0) (h2 : a ≠ 0x810b8) :
    (fullState s).getMem a = s.getMem a := by
  change a ≠ 528552#64 at h0
  change a ≠ 528560#64 at h1
  change a ≠ 528568#64 at h2
  simp [fullState,GroupedBalancedSignBottomTreeIndexLoad67.loadState,
    GroupedBalancedSignBottomTreeIndexShift67.shiftState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1,h2]
theorem shifted_index (s : MachineState) (index : BitVec 192)
    (stored : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x810a8 i.val) =
        index.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 3,
      (fullState s).getMem (Signing.wordAddress 0x810a8 i.val) =
        (index >>> 1).extractLsb' (64*i.val) 64 := by
  have w0 : s.getMem 0x810a8 = index.extractLsb' 0 64 := stored 0
  have w1 : s.getMem 0x810b0 = index.extractLsb' 64 64 := stored 1
  have w2 : s.getMem 0x810b8 = index.extractLsb' 128 64 := stored 2
  intro i
  fin_cases i
  · change (fullState s).getMem 0x810a8 = _
    rw [shifted_low,w0,w1]
    exact Signing.shifted_limb index 0
  · change (fullState s).getMem 0x810b0 = _
    rw [shifted_mid,w1,w2]
    exact Signing.shifted_limb index 1
  · change (fullState s).getMem 0x810b8 = _
    rw [shifted_high,w2]
    exact Signing.shifted_high_limb index
#print axioms full_steps
#print axioms shifted_index
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeIndexData67

end

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeHeaderCopy67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67.image
def setupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x81)
  let s := execInstrBr s (.ADDI .x6 .x6 0xa8)
  let s := execInstrBr s (.LUI .x7 0x81)
  let s := execInstrBr s (.ADDI .x7 .x7 8)
  execInstrBr s (.ADDI .x10 .x0 3)
private theorem setup_code :
    Keygen.instructionAt image 0x1e68 = some (.base (.LUI .x6 0x81)) ∧
    Keygen.instructionAt image 0x1e6c = some (.base (.ADDI .x6 .x6 0xa8)) ∧
    Keygen.instructionAt image 0x1e70 = some (.base (.LUI .x7 0x81)) ∧
    Keygen.instructionAt image 0x1e74 = some (.base (.ADDI .x7 .x7 8)) ∧
    Keygen.instructionAt image 0x1e78 = some (.base (.ADDI .x10 .x0 3)) := by decide
theorem setup_steps (s : MachineState) (pc : s.pc = 0x1e68) :
    OrdinarySteps image s 5 (setupState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x81)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0xa8)
  let s3 := execInstrBr s2 (.LUI .x7 0x81)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 8)
  obtain ⟨c0,c1,c2,c3,c4⟩ := setup_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x81)) 4
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0xa8)) 3
  · have hp : s1.pc = 0x1e6c := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x81)) 2
  · have hp : s2.pc = 0x1e70 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 8)) 1
  · have hp : s3.pc = 0x1e74 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 (setupState s) _ (.base (.ADDI .x10 .x0 3)) 0
  · have hp : s4.pc = 0x1e78 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  exact OrdinarySteps.refl _
theorem copy_code : Keygen.CopyCode image 0x1e7c := by decide
theorem copy_inv (s : MachineState) (pc : s.pc = 0x1e68) :
    Keygen.CopyInvariant 0x1e7c 0x810a8 0x81008 3 3 (setupState s) := by
  unfold Keygen.CopyInvariant setupState
  simp [execInstrBr,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,signExtend12,pc]
theorem header_copy (s : MachineState) (pc : s.pc = 0x1e68) :
    ∃ final, OrdinarySteps image s 23 final ∧ final.pc = 0x1e94 ∧
      (∀ i, i < 3 → final.getMem (Signing.wordAddress 0x81008 i) =
        s.getMem (Signing.wordAddress 0x810a8 i)) ∧
      (∀ a, (∀ i, i < 3 → a ≠ Signing.wordAddress 0x81008 i) →
        final.getMem a = s.getMem a) := by
  let begun := setupState s
  obtain ⟨final,loop,done,words,frame⟩ := Signing.copy_all image
    0x1e7c copy_code 0x810a8 0x81008 3 begun
    (copy_inv s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final,?_,done.2.2.1,?_,?_⟩
  · have full := Keygen.ordinary_trans image s begun final 5 18
      (setup_steps s pc) loop
    simpa only [show 18 + 5 = 23 by decide] using full
  · intro i hi
    rw [words i hi]
    simp [begun,setupState,execInstrBr]
  · intro a outside
    rw [frame a outside]
    simp [begun,setupState,execInstrBr]
#print axioms header_copy
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeHeaderCopy67
