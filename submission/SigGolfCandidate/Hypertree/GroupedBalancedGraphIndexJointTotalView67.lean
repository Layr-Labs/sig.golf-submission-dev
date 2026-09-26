import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointViewBudget67

/-! A total-query cutoff counts both public hash calls and honest private
randomizer/index calls. Disclosures and private coins do not spend this budget. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointTotalView67
open SigGolf OracleSpec Reference
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJointViewBudget67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

def TotalBudget {α : Type} : Nat → View α → Prop
  | _, .done _ => True
  | remaining, .hash _ next =>
      0 < remaining ∧ ∀ answer, TotalBudget (remaining - 1) (next answer)
  | remaining, .privateHash _ _ next =>
      0 < remaining ∧ ∀ answer, TotalBudget (remaining - 1) (next answer)
  | remaining, .sign _ next =>
      ∀ answer, TotalBudget remaining (next answer)
  | remaining, .coin _ next =>
      ∀ answer, TotalBudget remaining (next answer)

noncomputable def totalLimited {α : Type} :
    View α → Nat → View (Option α × Nat)
  | .done value, remaining => .done (some value, remaining)
  | .coin n next, remaining =>
      .coin n (fun answer => totalLimited (next answer) remaining)
  | .sign index next, remaining =>
      .sign index (fun answer => totalLimited (next answer) remaining)
  | .hash input next, 0 => .done (none, 0)
  | .hash input next, remaining + 1 =>
      .hash input (fun answer => totalLimited (next answer) remaining)
  | .privateHash input outside next, 0 => .done (none, 0)
  | .privateHash input outside next, remaining + 1 =>
      .privateHash input outside
        (fun answer => totalLimited (next answer) remaining)

theorem total_limited_budget {α : Type} (view : View α)
    (remaining : Nat) :
    TotalBudget remaining (totalLimited view remaining) := by
  induction view generalizing remaining with
  | done value => trivial
  | coin n next ih => exact fun answer => ih answer remaining
  | sign index next ih => exact fun answer => ih answer remaining
  | hash input next ih =>
      cases remaining with
      | zero => trivial
      | succ remaining => exact ⟨by omega, fun answer => ih answer remaining⟩
  | privateHash input outside next ih =>
      cases remaining with
      | zero => trivial
      | succ remaining => exact ⟨by omega, fun answer => ih answer remaining⟩

theorem total_limited_private_budget {α : Type} (view : View α)
    (remaining privateRemaining : Nat)
    (budget : PrivateBudget privateRemaining view) :
    PrivateBudget privateRemaining (totalLimited view remaining) := by
  induction view generalizing remaining privateRemaining with
  | done value => trivial
  | coin n next ih =>
      change ∀ answer, PrivateBudget privateRemaining (next answer) at budget
      exact fun answer => ih answer remaining privateRemaining (budget answer)
  | sign index next ih =>
      change ∀ answer, PrivateBudget privateRemaining (next answer) at budget
      exact fun answer => ih answer remaining privateRemaining (budget answer)
  | hash input next ih =>
      cases remaining with
      | zero => trivial
      | succ remaining =>
          change ∀ answer, PrivateBudget privateRemaining (next answer) at budget
          exact fun answer => ih answer remaining privateRemaining (budget answer)
  | privateHash input outside next ih =>
      cases remaining with
      | zero => trivial
      | succ remaining =>
          change 0 < privateRemaining ∧ ∀ answer,
            PrivateBudget (privateRemaining - 1) (next answer) at budget
          exact ⟨budget.1, fun answer =>
            ih answer remaining (privateRemaining - 1) (budget.2 answer)⟩

#print axioms total_limited_budget
#print axioms total_limited_private_budget

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointTotalView67
