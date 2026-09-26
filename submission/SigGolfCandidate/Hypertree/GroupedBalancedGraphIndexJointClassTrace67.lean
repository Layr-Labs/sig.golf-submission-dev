import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointTotalCost67
import SigGolfCandidate.Hypertree.GroupedBalancedQueryClasses67

/-! Count legacy secret-key-class public queries in the same joint graph/H5 run. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTrace67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedGraphIndexJointGlobal67
open GroupedBalancedGraphIndexJointTotalView67
open GroupedBalancedGraphIndexJointSumCredit67
open GroupedBalancedGraphIndexKeep67
open GroupedBalancedGraphIndexLift67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

noncomputable def secretCharge (input : Query) : Nat :=
  if SecuritySeparation.SecretKeyEligible input then 1 else 0

noncomputable def annotate {α : Type} : View α → Nat → View (α × Nat)
  | .done value, secret => .done (value, secret)
  | .coin n next, secret => .coin n (fun answer => annotate (next answer) secret)
  | .sign index next, secret => .sign index (fun answer => annotate (next answer) secret)
  | .privateHash input outside next, secret =>
      .privateHash input outside (fun answer => annotate (next answer) secret)
  | .hash input next, secret =>
      .hash input (fun answer => annotate (next answer) (secret + secretCharge input))

theorem annotate_budget {α : Type} (view : View α)
    (remaining secret : Nat) (budget : TotalBudget remaining view) :
    TotalBudget remaining (annotate view secret) := by
  induction view generalizing remaining secret with
  | done value => trivial
  | coin n next ih =>
      exact fun answer => ih answer remaining secret (budget answer)
  | sign index next ih =>
      exact fun answer => ih answer remaining secret (budget answer)
  | privateHash input outside next ih =>
      exact ⟨budget.1, fun answer => ih answer (remaining-1) secret (budget.2 answer)⟩
  | hash input next ih =>
      exact ⟨budget.1, fun answer =>
        ih answer (remaining-1) (secret+secretCharge input) (budget.2 answer)⟩

def secretCount {α : Type} (result : JointOutcome (α × Nat)) : Nat :=
  (result.value.value.map Prod.snd).getD 0

def score {α : Type} (result : JointOutcome (α × Nat)) : Nat :=
  result.value.graphCalls + secretCount result

theorem done_score {α : Type} (value : α) (secret calls remaining : Nat)
    (state : State) (bad : Bool) (tests : Nat) :
    score (⟨⟨some (value, secret), remaining, state, calls⟩, bad, tests⟩ :
      JointOutcome (α × Nat)) = calls + secret := rfl

theorem cutoff_score {α : Type} (calls : Nat) (state : State)
    (bad : Bool) (tests : Nat) :
    score (⟨⟨none, 0, state, calls⟩, bad, tests⟩ :
      JointOutcome (α × Nat)) = calls := rfl

#print axioms annotate_budget
#print axioms done_score

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTrace67
