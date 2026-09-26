import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointObserve67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMeteredBound67

/-! Sample the point table once, then run the joint graph/H5 monitor. Erasing
the H5 trace gives exactly the class-metered passive graph experiment. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointGlobal67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedGraphIndexObserve67
open GroupedBalancedGraphIndexLift67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

noncomputable def global {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    SecurityIndexProgram.Program (JointOutcome α) :=
  unmarked ($ᵗ PointTable) (fun table => start table view remaining)

theorem execute_global {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    SecurityIndexProgram.execute (global view remaining) =
      ($ᵗ PointTable) >>= fun table =>
        SecurityIndexProgram.execute (start table view remaining) := by
  exact execute_unmarked _ _

theorem observe_start {α : Type} (table : PointTable)
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    observe (start table view remaining) =
      run table (GroupedBalancedGraphMonitorSetup67.cache table)
        (GroupedBalancedGraphMetered67.limited
          (view (GroupedBalancedGraphMonitorSetup67.cache table))
          remaining
          (GroupedBalancedGraphMonitorSignBound67.initial
            (GroupedBalancedGraphMonitorSetup67.cache table)) 0) := by
  unfold start
  rw [GroupedBalancedGraphIndexJointObserve67.observe_compile]
  have identity :
      (accumulate false 0 :
        JointOutcome α → JointOutcome α) = id := by
    funext result
    cases result
    simp [accumulate]
  rw [identity, id_map]
  rfl

theorem observe_global {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    observe (global view remaining) =
      ($ᵗ PointTable) >>= fun table =>
        run table (GroupedBalancedGraphMonitorSetup67.cache table)
          (GroupedBalancedGraphMetered67.limited
            (view (GroupedBalancedGraphMonitorSetup67.cache table))
            remaining
            (GroupedBalancedGraphMonitorSignBound67.initial
              (GroupedBalancedGraphMonitorSetup67.cache table)) 0) := by
  unfold global
  rw [observe_unmarked]
  exact bind_congr (fun table => observe_start table view remaining)

theorem graph_projection {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    Prod.fst <$> SecurityIndexProgram.execute (global view remaining) =
      GroupedBalancedGraphMonitorProgram67.experiment
        (GroupedBalancedGraphMeteredBound67.monitored view remaining) ∅ := by
  change observe (global view remaining) = _
  rw [observe_global]
  unfold GroupedBalancedGraphMonitorProgram67.experiment
    GroupedBalancedGraphMeteredBound67.monitored
  apply bind_congr
  intro table
  have emptyComplete :
      complete (∅ : QueryCache PointSpec) table = table := by
    funext point
    simp [complete]
  rw [emptyComplete, GroupedBalancedGraphMonitorSetup67.run_setup]

#print axioms graph_projection

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointGlobal67
