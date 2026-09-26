import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentLevel67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeProtectedTick67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeFirstTickData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeInnerTickFrame67

/-! The parent fold keeps the saved link and the original index words. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentProtected67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomTreeParentFold67
open GroupedBalancedSignBottomTreeParentLevel67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev F := GroupedBalancedSignBottomTreeInnerTickFrame67.tickState
private abbrev first := GroupedBalancedSignBottomTreeFirstTickData67.tickState

def Protected (a : Word) : Prop :=
  0x90000 ≤ a.toNat ∨
    a = 0x81090 ∨ a = 0x81098 ∨ a = 0x810a0 ∨
    a.toNat < 0x20090

theorem first_protected (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (start : Start hash secretKey base height limit source target addressBase s)
    (a : Word) (safe : Protected a) :
    (first hash s).getMem a = s.getMem a := by
  have targetCase : target = 0x83000 ∨ target = 0x88000 := by
    rcases params.bases with ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  rcases safe with high | rfl | rfl | rfl | low
  · exact GroupedBalancedSignBottomTreeProtectedTick67.first_high hash s
      height target a start.levelWord start.witnessBase params.heightBound
      start.targetPtr targetCase high
  all_goals
    first
    | exact GroupedBalancedSignBottomTreeFirstTickData67.tick_low_frame
        hash s height target a start.levelWord start.witnessBase
        params.heightBound start.targetPtr targetCase low
    | (apply GroupedBalancedSignBottomTreeFirstTickData67.tick_control_frame
        hash s height target _ start.levelWord start.witnessBase
        params.heightBound start.targetPtr targetCase
       all_goals decide)

theorem inner_protected (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase n : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (holds : At hash secretKey base height limit source target addressBase n s)
    (nBound : n < limit) (a : Word) (safe : Protected a) :
    (F hash s).getMem a = s.getMem a := by
  have countBound : n < 512 := by have h := params.limitBound; omega
  have targetCase : target = 0x83000 ∨ target = 0x88000 := by
    rcases params.bases with ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  rcases safe with high | rfl | rfl | rfl | low
  · exact GroupedBalancedSignBottomTreeProtectedTick67.inner_high hash s
      n target a holds.counter holds.targetPtr countBound targetCase high
  all_goals
    first
    | exact GroupedBalancedSignBottomTreeInnerTickFrame67.tick_low_frame
        hash s n target a holds.counter holds.targetPtr countBound targetCase low
    | (apply GroupedBalancedSignBottomTreeInnerTickFrame67.tick_control_frame
        hash s n target _ holds.counter holds.targetPtr countBound targetCase
       all_goals decide)

theorem fold_protected (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase n : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (holds : At hash secretKey base height limit source target addressBase n s)
    (nBound : n < limit) :
    ∃ final,
      Trace hash image s (84*(limit-n)) (91*(limit-n))
        (limit-n) (limit-n) final ∧
      Done hash secretKey base height limit source target addressBase final ∧
      (∀ a, Protected a → final.getMem a = s.getMem a) := by
  suffices H : ∀ remaining n (s : MachineState), remaining = limit-n →
      n < limit → At hash secretKey base height limit source target addressBase n s →
      ∃ final,
        Trace hash image s (84*remaining) (91*remaining)
          remaining remaining final ∧
        Done hash secretKey base height limit source target addressBase final ∧
        (∀ a, Protected a → final.getMem a = s.getMem a) by
    exact H (limit-n) n s rfl nBound holds
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
      intro n s remEq nBound holds
      obtain ⟨firstTrace,next,last⟩ :=
        one_tick hash secretKey base height limit source target addressBase n s
          params holds nBound
      by_cases more : n+1 < limit
      · obtain ⟨final,rest,finished,restFrame⟩ :=
          ih (limit-(n+1)) (by omega) (n+1) (F hash s)
            (by omega) more (next more)
        refine ⟨final,?_,finished,?_⟩
        · convert firstTrace.trans rest using 1 <;> omega
        · intro a ha
          exact (restFrame a ha).trans
            (inner_protected hash secretKey base height limit source target
              addressBase n s params holds nBound a ha)
      · have atEnd : n+1=limit := by omega
        refine ⟨F hash s,?_,last atEnd,?_⟩
        · have one : remaining=1 := by omega
          simpa only [one,Nat.mul_one] using firstTrace
        · intro a ha
          exact inner_protected hash secretKey base height limit source target
            addressBase n s params holds nBound a ha

theorem one_level_protected (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (start : Start hash secretKey base height limit source target addressBase s)
    (positive : 0 < limit) :
    ∃ final,
      Trace hash image s (113+84*(limit-1)) (120+91*(limit-1))
        limit limit final ∧
      Done hash secretKey base height limit source target addressBase final ∧
      (∀ a, Protected a → final.getMem a = s.getMem a) := by
  obtain ⟨firstTrace,hcontinue,finish⟩ :=
    first_result hash secretKey base height limit source target addressBase
      s params start positive
  by_cases more : 1 < limit
  · obtain ⟨final,rest,done,restFrame⟩ :=
      fold_protected hash secretKey base height limit source target
        addressBase 1 (first hash s) params (hcontinue more) more
    refine ⟨final,?_,done,?_⟩
    · convert firstTrace.trans rest using 1 <;> omega
    · intro a ha
      exact (restFrame a ha).trans
        (first_protected hash secretKey base height limit source target
          addressBase s params start a ha)
  · have one : limit=1 := by omega
    refine ⟨first hash s,?_,finish one,?_⟩
    · simpa [one] using firstTrace
    · intro a ha
      exact first_protected hash secretKey base height limit source target
        addressBase s params start a ha

#print axioms one_level_protected
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentProtected67
