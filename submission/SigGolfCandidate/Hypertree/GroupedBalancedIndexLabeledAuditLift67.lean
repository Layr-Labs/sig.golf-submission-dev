import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAudit67

/-! The ghost audit passes through ordinary randomness and public graph
operations without changing their result distribution. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAuditLift67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedIndexLabeledAudit67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem run_unmarked {α β : Type} (program : ProbComp α)
    (next : α → GroupedBalancedIndexLabeledProgram67.Program β)
    (audit : Audit) :
    run (GroupedBalancedIndexLabeledLift67.unmarked program next) audit =
      program >>= fun value => run (next value) audit := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind n resume ih =>
      change (ProbComp.uniformFin n >>= fun answer =>
        run (GroupedBalancedIndexLabeledLift67.unmarked
          (resume answer) next) audit) = _
      simp only [bind_assoc]
      exact bind_congr ih

theorem run_ofGraphKeep {α β : Type}
    (table : PointTable) (cache : QueryCache PointSpec)
    (program : Program α)
    (next : Outcome α →
      GroupedBalancedIndexLabeledProgram67.Program β)
    (audit : Audit) :
    run (GroupedBalancedIndexLabeledLift67.ofGraphKeep
      table cache program next) audit =
      GroupedBalancedGraphMonitorProgram67.run table cache program >>=
        fun result => run (next result) audit := by
  induction program generalizing cache next with
  | done value => rfl
  | reveal point resume ih => exact ih (table point) _ _
  | guess point value resume ih =>
      simp only [GroupedBalancedIndexLabeledLift67.ofGraphKeep,
        GroupedBalancedGraphMonitorProgram67.run,
        map_eq_pure_bind, bind_assoc, pure_bind]
      exact ih cache _
  | coin n resume ih =>
      simp only [GroupedBalancedIndexLabeledLift67.ofGraphKeep,
        GroupedBalancedIndexLabeledAudit67.run,
        GroupedBalancedGraphMonitorProgram67.run, bind_assoc]
      exact bind_congr fun answer => ih answer cache next
  | bits resume ih =>
      rw [GroupedBalancedIndexLabeledLift67.ofGraphKeep, run_unmarked]
      simp only [GroupedBalancedGraphMonitorProgram67.run, bind_assoc]
      exact bind_congr fun answer => ih answer cache next
  | collision target resume ih =>
      rw [GroupedBalancedIndexLabeledLift67.ofGraphKeep, run_unmarked]
      simp only [GroupedBalancedGraphMonitorProgram67.run,
        map_eq_pure_bind, bind_assoc, pure_bind]
      exact bind_congr fun answer => ih answer cache _

#print axioms run_unmarked
#print axioms run_ofGraphKeep

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAuditLift67
