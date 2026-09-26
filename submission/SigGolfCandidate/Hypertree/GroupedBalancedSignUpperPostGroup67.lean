import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperPostRoot67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperGroupTransition67

/-! The completed upper tree updates CURRENT, the selected index, and the layer. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperPostGroup67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67Byte.image

theorem run (hash : Hash) (s : MachineState) (p : Word)
    (index : BitVec 192) (height : Nat)
    (pc : s.pc = 0x1c34)
    (valid0 : accessValid (s.getMem 0x810c0) 8 = true)
    (valid8 : accessValid (s.getMem 0x810c0 + 8) 8 = true)
    (source : s.getMem 0x810c0 = p)
    (hh : height = 3 ∨ height = 4)
    (limit : s.getMem 0x81060 = BitVec.ofNat 64 height)
    (selected : ∀ w : Fin 3,
      s.getMem (Signing.wordAddress 0x81090 w.val) =
        index.extractLsb' (64*w.val) 64) :
    ∃ final : MachineState,
      Trace hash image s
        (24 + 36*height +
          (if s.getMem 0x81058 + 1 = (30 : Word) then 15 else 11))
        (24 + 36*height +
          (if s.getMem 0x81058 + 1 = (30 : Word) then 15 else 11))
        0 0 final ∧
      final.pc =
        (if s.getMem 0x81058 + 1 = (45 : Word) then 0x1d60 else 0x15e0) ∧
      final.getMem 0x80500 = s.getMem p ∧
      final.getMem 0x80508 = s.getMem (p+8) ∧
      final.getMem 0x81058 = s.getMem 0x81058 + 1 ∧
      final.getMem 0x81060 =
        (if s.getMem 0x81058 + 1 = (30 : Word) then 4 else BitVec.ofNat 64 height) ∧
      final.getMem 0x810f0 =
        s.getMem 0x810f8 + (BitVec.ofNat 64 height <<< 4) ∧
      (∀ w : Fin 3,
        final.getMem (Signing.wordAddress 0x81090 w.val) =
          (index >>> height).extractLsb' (64*w.val) 64) := by
  let copied := GroupedBalancedSignUpperPostRoot67.postState s
  have copyTrace : Trace hash image s 24 24 0 0 copied :=
    OrdinarySteps.trace (hash := hash)
      (GroupedBalancedSignUpperPostRoot67.post_steps s pc valid0 valid8)
  have copyPc := GroupedBalancedSignUpperPostRoot67.post_pc s pc
  have copyWords := GroupedBalancedSignUpperPostRoot67.post_words s p source
  have copyLimit : copied.getMem 0x81060 = BitVec.ofNat 64 height := by
    rw [GroupedBalancedSignUpperPostRoot67.post_frame s 0x81060 (by decide) (by decide)
      (by decide) (by decide)]
    exact limit
  have copyIndex : ∀ w : Fin 3,
      copied.getMem (Signing.wordAddress 0x81090 w.val) =
        index.extractLsb' (64*w.val) 64 := by
    intro w
    rw [GroupedBalancedSignUpperPostRoot67.post_frame s _ (by fin_cases w <;> decide)
      (by fin_cases w <;> decide) (by fin_cases w <;> decide)
      (by fin_cases w <;> decide)]
    exact selected w
  have initial : GroupedBalancedSignUpperSelectedFold67.Inv index height 0 copied := by
    have hpos : 0 < height := by rcases hh with rfl | rfl <;> decide
    refine ⟨by omega,by simpa [hpos] using copyPc,?_,copyLimit,?_⟩
    · exact copyWords.2.2.2
    · intro w
      simpa using copyIndex w
  obtain ⟨folded,foldTrace,foldPc,foldCount,foldWords,foldFrame⟩ :=
    GroupedBalancedSignUpperSelectedFold67.run_all index height hh copied initial
  have shiftTrace : Trace hash image copied (36*height) (36*height) 0 0 folded :=
    OrdinarySteps.trace (hash := hash) foldTrace
  have foldedLayer : folded.getMem 0x81058 = s.getMem 0x81058 := by
    rw [foldFrame 0x81058 (by simp [GroupedBalancedSignUpperSelectedFold67.Outside]),
      GroupedBalancedSignUpperPostRoot67.post_frame s 0x81058 (by decide) (by decide)
        (by decide) (by decide)]
  have foldedHeight : folded.getMem 0x81060 = BitVec.ofNat 64 height := by
    rw [foldFrame 0x81060 (by simp [GroupedBalancedSignUpperSelectedFold67.Outside])]
    exact copyLimit
  let final := GroupedBalancedSignUpperGroupTransition67.transitionState folded
  have moveTrace := GroupedBalancedSignUpperGroupTransition67.transition_trace hash folded foldPc
  have root0 : final.getMem 0x80500 = s.getMem p := by
    rw [GroupedBalancedSignUpperGroupTransition67.transition_frame folded 0x80500 (by decide) (by decide),
      foldFrame 0x80500 (by simp [GroupedBalancedSignUpperSelectedFold67.Outside])]
    exact copyWords.1
  have root8 : final.getMem 0x80508 = s.getMem (p+8) := by
    rw [GroupedBalancedSignUpperGroupTransition67.transition_frame folded 0x80508 (by decide) (by decide),
      foldFrame 0x80508 (by simp [GroupedBalancedSignUpperSelectedFold67.Outside])]
    exact copyWords.2.1
  have layer : final.getMem 0x81058 = s.getMem 0x81058 + 1 := by
    rw [GroupedBalancedSignUpperGroupTransition67.transition_count folded,foldedLayer]
  have newHeight : final.getMem 0x81060 =
      (if s.getMem 0x81058 + 1 = (30 : Word) then 4 else BitVec.ofNat 64 height) := by
    rw [GroupedBalancedSignUpperGroupTransition67.transition_height folded,foldedLayer,foldedHeight]
  have pointer : final.getMem 0x810f0 =
      s.getMem 0x810f8 + (BitVec.ofNat 64 height <<< 4) := by
    rw [GroupedBalancedSignUpperGroupTransition67.transition_frame folded 0x810f0 (by decide) (by decide),
      foldFrame 0x810f0 (by simp [GroupedBalancedSignUpperSelectedFold67.Outside])]
    rw [copyWords.2.2.1,limit]
  have words : ∀ w : Fin 3,
      final.getMem (Signing.wordAddress 0x81090 w.val) =
        (index >>> height).extractLsb' (64*w.val) 64 := by
    intro w
    rw [GroupedBalancedSignUpperGroupTransition67.transition_frame folded _ (by fin_cases w <;> decide)
      (by fin_cases w <;> decide)]
    exact foldWords w
  have finalPc : final.pc =
      (if s.getMem 0x81058 + 1 = (45 : Word) then 0x1d60 else 0x15e0) := by
    rw [GroupedBalancedSignUpperGroupTransition67.transition_pc folded foldPc,foldedLayer]
  refine ⟨final,?_,finalPc,root0,root8,layer,newHeight,pointer,words⟩
  have combined := (copyTrace.trans shiftTrace).trans moveTrace
  have exactLayer : folded.getMem (528472#64) = s.getMem (528472#64) := foldedLayer
  simpa [exactLayer,Nat.add_assoc] using combined

#print axioms run
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperPostGroup67
