import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeHeaderCopy67
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelPrelude67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67.image
theorem level_prelude (s : MachineState) (index : BitVec 192)
    (pc : s.pc = 0x1e04)
    (indexWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x810a8 i.val) =
        index.extractLsb' (64*i.val) 64) :
    ∃ t : MachineState,
      OrdinarySteps image s 48 t ∧
      t.pc = 0x1e94 ∧
      (∀ i : Fin 3,
        t.getMem (Signing.wordAddress 0x81008 i.val) =
          (index >>> 1).extractLsb' (64*i.val) 64) ∧
      (∀ i : Fin 3,
        t.getMem (Signing.wordAddress 0x810a8 i.val) =
          (index >>> 1).extractLsb' (64*i.val) 64) ∧
      (∀ a : Word,
        a ≠ 0x81008 → a ≠ 0x81010 → a ≠ 0x81018 →
        a ≠ 0x810a8 → a ≠ 0x810b0 → a ≠ 0x810b8 →
        t.getMem a = s.getMem a) := by
  let shifted := GroupedBalancedSignBottomTreeIndexData67.fullState s
  have shiftSteps := GroupedBalancedSignBottomTreeIndexData67.full_steps s pc
  have shiftPc := GroupedBalancedSignBottomTreeIndexData67.full_pc s pc
  obtain ⟨t,copySteps,copyPc,headerWords,headerFrame⟩ :=
    GroupedBalancedSignBottomTreeHeaderCopy67.header_copy shifted shiftPc
  refine ⟨t,?_,copyPc,?_,?_,?_⟩
  · have both := Keygen.ordinary_trans image s shifted t 25 23
      shiftSteps copySteps
    simpa only [show 23 + 25 = 48 by decide] using both
  · intro i
    rw [headerWords i.val i.isLt]
    exact GroupedBalancedSignBottomTreeIndexData67.shifted_index
      s index indexWords i
  · intro i
    rw [headerFrame _ (by
      intro j hj
      interval_cases j <;> fin_cases i <;> decide)]
    exact GroupedBalancedSignBottomTreeIndexData67.shifted_index
      s index indexWords i
  · intro a h0 h1 h2 h3 h4 h5
    rw [headerFrame a (by
      intro j hj
      have cases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases cases with rfl | rfl | rfl
      · simpa [Signing.wordAddress] using h0
      · simpa [Signing.wordAddress] using h1
      · simpa [Signing.wordAddress] using h2)]
    exact GroupedBalancedSignBottomTreeIndexData67.shift_frame
      s a h3 h4 h5
#print axioms level_prelude
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelPrelude67
