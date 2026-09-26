import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTraceCostSmall67
import SigGolfCandidate.Hypertree.SecuritySharedBudget

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTrace67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedGraphIndexJointGlobal67
open GroupedBalancedGraphIndexJointTotalView67
open SecuritySharedBudget
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def jointCounts {α : Type}
    (result : JointOutcome (α × Nat) × List SecurityIndexTrace.Entry) : Counts :=
  { secretKey := secretCount result.1
    graph := result.1.value.graphCalls
    index := result.2.length }

theorem global_counts {α : Type}
    (view : QueryCache PointSpec → View α) (budget : Nat)
    (total : ∀ cache, TotalBudget budget (view cache)) :
    ∀ result ∈ support
      (SecurityIndexProgram.execute
        (global (fun cache => annotate (view cache) 0) budget)),
      (jointCounts result).total ≤ budget := by
  intro result member
  have h := global_class_cost view budget total result member
  dsimp only [jointCounts, Counts.total]
  omega

theorem expected_joint_weight_le {α : Type}
    (view : QueryCache PointSpec → View α) (budget : Nat)
    (total : ∀ cache, TotalBudget budget (view cache)) :
    expectedValue
      (SecurityIndexProgram.execute
        (global (fun cache => annotate (view cache) 0) budget))
      (fun result => weight (jointCounts result)) ≤
      (budget : ENNReal) / 2 ^ 127 :=
  expected_weight_le _ jointCounts budget (global_counts view budget total)

#print axioms global_counts
#print axioms expected_joint_weight_le

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTrace67
