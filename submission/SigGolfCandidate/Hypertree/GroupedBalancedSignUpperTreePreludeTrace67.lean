import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelPrelude67

/-! Resource-only upper-tree prelude and control frame. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreePreludeTrace67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

theorem prelude (s : MachineState) (pc : s.pc = 0x1e04) :
    ∃ t : MachineState,
      OrdinarySteps image s 48 t ∧
      t.pc = 0x1e94 ∧
      (∀ a : Word,
        a ≠ 0x81008 → a ≠ 0x81010 → a ≠ 0x81018 →
        a ≠ 0x810a8 → a ≠ 0x810b0 → a ≠ 0x810b8 →
        t.getMem a = s.getMem a) := by
  let shifted := GroupedBalancedSignBottomTreeIndexData67.fullState s
  have shiftSteps := GroupedBalancedSignBottomTreeIndexData67.full_steps s pc
  have shiftPc := GroupedBalancedSignBottomTreeIndexData67.full_pc s pc
  obtain ⟨t,copySteps,copyPc,_,headerFrame⟩ :=
    GroupedBalancedSignBottomTreeHeaderCopy67.header_copy shifted shiftPc
  refine ⟨t,?_,copyPc,?_⟩
  · have both := Keygen.ordinary_trans image s shifted t 25 23
      shiftSteps copySteps
    simpa only [show 23+25=48 by decide] using both
  · intro a h0 h1 h2 h3 h4 h5
    rw [headerFrame a (by
      intro j hj
      have cases : j=0 ∨ j=1 ∨ j=2 := by omega
      rcases cases with rfl | rfl | rfl
      · simpa [Signing.wordAddress] using h0
      · simpa [Signing.wordAddress] using h1
      · simpa [Signing.wordAddress] using h2)]
    exact GroupedBalancedSignBottomTreeIndexData67.shift_frame s a h3 h4 h5

#print axioms prelude
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreePreludeTrace67
