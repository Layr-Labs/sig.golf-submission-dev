import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperPostGroup67
import SigGolfCandidate.TraceDeterminism

/-! Memory frame for the upper group's post-root path. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperPostFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67Byte.image

def Outside (a : Word) : Prop :=
  a ≠ 0x80500 ∧ a ≠ 0x80508 ∧ a ≠ 0x810f0 ∧ a ≠ 0x81100 ∧
  a ≠ 0x81090 ∧ a ≠ 0x81098 ∧ a ≠ 0x810a0 ∧
  a ≠ 0x81058 ∧ a ≠ 0x81060

theorem run_frame (hash : Hash) (s final : MachineState)
    (index : BitVec 192) (height : Nat)
    (pc : s.pc = 0x1c34)
    (valid0 : accessValid (s.getMem 0x810c0) 8 = true)
    (valid8 : accessValid (s.getMem 0x810c0 + 8) 8 = true)
    (hh : height = 3 ∨ height = 4)
    (limit : s.getMem 0x81060 = BitVec.ofNat 64 height)
    (selected : ∀ w : Fin 3,
      s.getMem (Signing.wordAddress 0x81090 w.val) =
        index.extractLsb' (64*w.val) 64)
    (trace : Trace hash image s
      (24 + 36*height +
        (if s.getMem 0x81058 + 1 = (30 : Word) then 15 else 11))
      (24 + 36*height +
        (if s.getMem 0x81058 + 1 = (30 : Word) then 15 else 11))
      0 0 final)
    (a : Word) (outside : Outside a) :
    final.getMem a = s.getMem a := by
  let copied := GroupedBalancedSignUpperPostRoot67.postState s
  have copyTrace : Trace hash image s 24 24 0 0 copied :=
    OrdinarySteps.trace (hash := hash)
      (GroupedBalancedSignUpperPostRoot67.post_steps s pc valid0 valid8)
  have copyPc := GroupedBalancedSignUpperPostRoot67.post_pc s pc
  have copyLimit : copied.getMem 0x81060 = BitVec.ofNat 64 height := by
    rw [GroupedBalancedSignUpperPostRoot67.post_frame s 0x81060
      (by decide) (by decide) (by decide) (by decide)]
    exact limit
  have copyIndex : ∀ w : Fin 3,
      copied.getMem (Signing.wordAddress 0x81090 w.val) =
        index.extractLsb' (64*w.val) 64 := by
    intro w
    rw [GroupedBalancedSignUpperPostRoot67.post_frame s _
      (by fin_cases w <;> decide) (by fin_cases w <;> decide)
      (by fin_cases w <;> decide) (by fin_cases w <;> decide)]
    exact selected w
  have initial : GroupedBalancedSignUpperSelectedFold67.Inv index height 0 copied := by
    have hpos : 0 < height := by rcases hh with rfl | rfl <;> decide
    refine ⟨by omega,by simpa [hpos] using copyPc,?_,copyLimit,?_⟩
    · exact GroupedBalancedSignUpperPostRoot67.post_words s
        (s.getMem 0x810c0) rfl |>.2.2.2
    · intro w; simpa using copyIndex w
  obtain ⟨folded,foldTrace,foldPc,_,_,foldFrame⟩ :=
    GroupedBalancedSignUpperSelectedFold67.run_all index height hh copied initial
  have shiftTrace : Trace hash image copied (36*height) (36*height) 0 0 folded :=
    OrdinarySteps.trace (hash := hash) foldTrace
  have foldedLayer : folded.getMem 0x81058 = s.getMem 0x81058 := by
    rw [foldFrame 0x81058 (by simp [GroupedBalancedSignUpperSelectedFold67.Outside]),
      GroupedBalancedSignUpperPostRoot67.post_frame s 0x81058
        (by decide) (by decide) (by decide) (by decide)]
  let concreteFinal := GroupedBalancedSignUpperGroupTransition67.transitionState folded
  have moveTrace := GroupedBalancedSignUpperGroupTransition67.transition_trace hash folded foldPc
  have built : Trace hash image s
      (24 + 36*height +
        (if s.getMem 0x81058 + 1 = (30 : Word) then 15 else 11))
      (24 + 36*height +
        (if s.getMem 0x81058 + 1 = (30 : Word) then 15 else 11))
      0 0 concreteFinal := by
    have combined := (copyTrace.trans shiftTrace).trans moveTrace
    have exactLayer : folded.getMem (528472#64) = s.getMem (528472#64) := foldedLayer
    simpa [exactLayer,Nat.add_assoc] using combined
  have same : final = concreteFinal := Trace.deterministic trace built
  subst final
  obtain ⟨ha0,ha8,haf0,ha100,ha90,ha98,haa0,ha58,ha60⟩ := outside
  rw [GroupedBalancedSignUpperGroupTransition67.transition_frame folded a ha58 ha60,
    foldFrame a ⟨ha90,ha98,haa0,ha100⟩,
    GroupedBalancedSignUpperPostRoot67.post_frame s a ha0 ha8 haf0 ha100]

#print axioms run_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperPostFrame67
