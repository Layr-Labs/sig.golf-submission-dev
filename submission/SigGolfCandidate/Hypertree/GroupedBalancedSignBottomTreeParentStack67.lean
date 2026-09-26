import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentProtected67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeTickStack67

/-! Parent-level folds preserve x2 and protected memory. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentStack67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomTreeParentFold67
open GroupedBalancedSignBottomTreeParentLevel67
open GroupedBalancedSignBottomTreeParentProtected67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev F := GroupedBalancedSignBottomTreeInnerTickFrame67.tickState
private abbrev first := GroupedBalancedSignBottomTreeFirstTickData67.tickState

theorem fold_stack (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase n : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (holds : At hash secretKey base height limit source target addressBase n s)
    (nBound : n < limit) :
    ∃ final,
      Trace hash image s (84*(limit-n)) (91*(limit-n))
        (limit-n) (limit-n) final ∧
      Done hash secretKey base height limit source target addressBase final ∧
      (∀ a, Protected a → final.getMem a = s.getMem a) ∧
      final.getReg .x2 = s.getReg .x2 := by
  suffices H : ∀ remaining n (s : MachineState), remaining = limit-n →
      n < limit → At hash secretKey base height limit source target addressBase n s →
      ∃ final,
        Trace hash image s (84*remaining) (91*remaining)
          remaining remaining final ∧
        Done hash secretKey base height limit source target addressBase final ∧
        (∀ a, Protected a → final.getMem a = s.getMem a) ∧
        final.getReg .x2 = s.getReg .x2 by
    exact H (limit-n) n s rfl nBound holds
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
      intro n s remEq nBound holds
      obtain ⟨firstTrace,next,last⟩ :=
        one_tick hash secretKey base height limit source target addressBase n s
          params holds nBound
      by_cases more : n+1 < limit
      · obtain ⟨final,rest,finished,restFrame,restSp⟩ :=
          ih (limit-(n+1)) (by omega) (n+1) (F hash s)
            (by omega) more (next more)
        refine ⟨final,?_,finished,?_,?_⟩
        · convert firstTrace.trans rest using 1 <;> omega
        · intro a ha
          exact (restFrame a ha).trans
            (inner_protected hash secretKey base height limit source target
              addressBase n s params holds nBound a ha)
        · exact restSp.trans
            (GroupedBalancedSignBottomTreeTickStack67.inner_tick_sp hash s)
      · have atEnd : n+1=limit := by omega
        refine ⟨F hash s,?_,last atEnd,?_,?_⟩
        · have one : remaining=1 := by omega
          simpa only [one,Nat.mul_one] using firstTrace
        · intro a ha
          exact inner_protected hash secretKey base height limit source target
            addressBase n s params holds nBound a ha
        · exact GroupedBalancedSignBottomTreeTickStack67.inner_tick_sp hash s

theorem one_level_stack (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (start : Start hash secretKey base height limit source target addressBase s)
    (positive : 0 < limit) :
    ∃ final,
      Trace hash image s (113+84*(limit-1)) (120+91*(limit-1))
        limit limit final ∧
      Done hash secretKey base height limit source target addressBase final ∧
      (∀ a, Protected a → final.getMem a = s.getMem a) ∧
      final.getReg .x2 = s.getReg .x2 := by
  obtain ⟨firstTrace,hcontinue,finish⟩ :=
    first_result hash secretKey base height limit source target addressBase
      s params start positive
  by_cases more : 1 < limit
  · obtain ⟨final,rest,done,restFrame,restSp⟩ :=
      fold_stack hash secretKey base height limit source target
        addressBase 1 (first hash s) params (hcontinue more) more
    refine ⟨final,?_,done,?_,?_⟩
    · convert firstTrace.trans rest using 1 <;> omega
    · intro a ha
      exact (restFrame a ha).trans
        (first_protected hash secretKey base height limit source target
          addressBase s params start a ha)
    · exact restSp.trans
        (GroupedBalancedSignBottomTreeTickStack67.first_tick_sp hash s)
  · have one : limit=1 := by omega
    refine ⟨first hash s,?_,finish one,?_,?_⟩
    · simpa [one] using firstTrace
    · intro a ha
      exact first_protected hash secretKey base height limit source target
        addressBase s params start a ha
    · exact GroupedBalancedSignBottomTreeTickStack67.first_tick_sp hash s

#print axioms one_level_stack
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentStack67
