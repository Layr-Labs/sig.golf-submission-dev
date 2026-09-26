import SigGolfCandidate.Hypertree.GroupedBalancedGraphMetered67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSetup67

/-! The graph contact risk is charged to the exact number of executed public
queries that locate a grouped-graph address in the same passive experiment. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMeteredBound67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorCredit67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphMetered67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

noncomputable def monitored {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    Program (Result α) :=
  GroupedBalancedGraphMonitorSetup67.setup (fun exposed =>
    limited (view exposed) remaining
      (GroupedBalancedGraphMonitorSignBound67.initial exposed) 0)

theorem monitored_credit {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    Credit (fun result : Result α => 2 * result.graphCalls) 0
      (monitored view remaining) := by
  unfold monitored GroupedBalancedGraphMonitorSetup67.setup
  apply disclose_credit
  intro metadata
  apply disclose_credit
  intro exposed
  exact limited_credit (view exposed) remaining
    (GroupedBalancedGraphMonitorSignBound67.initial exposed) 0 0
    (by omega)

theorem experiment_tests_le {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat)
    (outcome : Outcome (Result α))
    (member : outcome ∈ support (GroupedBalancedGraphMonitorProgram67.experiment
      (monitored view remaining) ∅)) :
    outcome.tests ≤ 2 * outcome.value.graphCalls := by
  unfold GroupedBalancedGraphMonitorProgram67.experiment at member
  rw [mem_support_bind_iff] at member
  obtain ⟨table, _, member⟩ := member
  have bound := run_credit
    (fun result : Result α => 2 * result.graphCalls)
    (monitored view remaining) 0 (monitored_credit view remaining)
    (complete (∅ : QueryCache PointSpec) table) ∅ outcome member
  simpa only [Nat.zero_add] using bound

theorem bad_le_expected_graph_calls {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    Pr[fun result => result.bad = true |
      GroupedBalancedGraphMonitorProgram67.experiment
        (monitored view remaining) ∅] ≤
    expectedValue (GroupedBalancedGraphMonitorProgram67.experiment
      (monitored view remaining) ∅)
      (fun result => (2 * result.value.graphCalls : ENNReal)) /
        (2 : ENNReal) ^ 128 := by
  have bound := prob_bad_le_expected (monitored view remaining) ∅
  apply bound.trans
  apply ENNReal.div_le_div _ le_rfl
  apply expectedValue_mono_of_support
  intro result member
  exact_mod_cast experiment_tests_le view remaining result member

#print axioms bad_le_expected_graph_calls

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMeteredBound67
