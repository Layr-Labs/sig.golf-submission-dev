import SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerAnnotated67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointBound67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointSharpLifetime67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTraceBudget67

/-! Sharp graph/H5 risk on the annotated eager ideal simulation. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerJointRisk67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJointClassTrace67
open GroupedBalancedGraphIndexJointIndexBudget67
open GroupedBalancedPlantedEagerAnnotated67
open GroupedBalancedPlantedEagerGraphProjection67
open GroupedBalancedGraphInteraction67 SecurityGraphIdeal
open SecuritySharedBudget
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem annotate_index_budget {α : Type} (view : View α)
    (secret remaining : Nat) (budget : IndexBudget remaining view) :
    IndexBudget remaining (annotate view secret) := by
  induction budget generalizing secret with
  | done remaining value => exact .done remaining (value, secret)
  | hash remaining input next child ih =>
      exact .hash remaining input _
        (fun answer => ih answer (secret + secretCharge input))
  | privateOutside remaining input outside parsed next child ih =>
      exact .privateOutside remaining input outside parsed _
        (fun answer => ih answer secret)
  | privateIndex remaining input outside pair parsed positive next child ih =>
      exact .privateIndex remaining input outside pair parsed positive _
        (fun answer => ih answer secret)
  | sign remaining index next child ih =>
      exact .sign remaining index _ (fun answer => ih answer secret)
  | coin remaining n next child ih =>
      exact .coin remaining n _ (fun answer => ih answer secret)

theorem annotated_bad_le_expected_graph_index {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat)
    (indexBudget : ∀ answers cache,
      IndexBudget LIFETIME (viewOf answers interaction budget cache)) :
    Pr[fun result => result.1.bad = true ∨
      SecurityIndexTrace.Conflict result.2 |
      annotatedJointGlobal interaction budget] ≤
    expectedValue (annotatedJointGlobal interaction budget)
      (fun result =>
        ((2 * result.1.value.graphCalls : ENNReal) +
          result.2.length : ENNReal) / (2 : ENNReal) ^ 128) := by
  unfold annotatedJointGlobal
  conv_lhs => rw [probEvent_bind_eq_tsum]
  conv_rhs => rw [expectedValue_bind]
  apply ENNReal.tsum_le_tsum
  intro answers
  apply mul_le_mul' le_rfl
  let view := fun cache => annotate (viewOf answers interaction budget cache) 0
  have marks :=
    GroupedBalancedGraphIndexJointSharpLifetime67.global_marks_le_lifetime
      view budget
      (fun cache => annotate_index_budget
        (viewOf answers interaction budget cache) 0 LIFETIME
        (indexBudget answers cache))
  have eventLe :
      Pr[fun result => result.1.bad = true ∨
        SecurityIndexTrace.Conflict result.2 |
        SecurityIndexProgram.execute
          (GroupedBalancedGraphIndexJointGlobal67.global view budget)] ≤
      Pr[fun result => result.1.bad = true ∨
        (SecurityIndexTrace.Conflict result.2 ∧
          SecurityIndexTrace.marks result.2 ≤ LIFETIME) |
        SecurityIndexProgram.execute
          (GroupedBalancedGraphIndexJointGlobal67.global view budget)] := by
    apply probEvent_mono
    intro result member event
    rcases event with graph | index
    · exact Or.inl graph
    · exact Or.inr ⟨index, marks result member⟩
  simpa only [div_eq_mul_inv, expectedValue_mul_const] using
    eventLe.trans
      (GroupedBalancedGraphIndexJointBound67.joint_bad_le_expected_calls
        view budget)

theorem annotated_counts {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    ∀ result ∈ support (annotatedJointGlobal interaction budget),
      (jointCounts result).total ≤ budget := by
  intro result member
  unfold annotatedJointGlobal at member
  rw [mem_support_bind_iff] at member
  obtain ⟨answers, _, inner⟩ := member
  exact global_counts (viewOf answers interaction budget) budget
    (fun cache =>
      GroupedBalancedIdealEagerCutoffBudget67.eager_cutoff_total
        answers cache (interaction cache) budget)
    result inner

theorem annotated_expected_weight_le {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    expectedValue (annotatedJointGlobal interaction budget)
      (fun result => weight (jointCounts result)) ≤
      (budget : ENNReal) / (2 : ENNReal) ^ 127 :=
  SecuritySharedBudget.expected_weight_le _ jointCounts budget
    (annotated_counts interaction budget)

theorem graph_secret_weight (graph secret index : Nat) :
    (((2 * graph : ENNReal) + index) / (2 : ENNReal) ^ 128) +
      (secret : ENNReal) / (2 : ENNReal) ^ 128 ≤
    SecuritySharedBudget.weight
      ⟨secret, graph, index⟩ := by
  let a := (secret : ENNReal) / (2 : ENNReal) ^ 128
  let b := (2 * graph : ENNReal) / (2 : ENNReal) ^ 128
  let c := (index : ENNReal) / (2 : ENNReal) ^ 128
  let d := (index : ENNReal) / (2 : ENNReal) ^ 256
  have core : (b + c) + a ≤ a + b + d + c := by
    calc
      (b + c) + a = (a + b) + c := by ac_rfl
      _ ≤ ((a + b) + d) + c :=
        add_le_add (le_add_right le_rfl) le_rfl
      _ = a + b + d + c := by ac_rfl
  simpa only [SecuritySharedBudget.weight, ENNReal.add_div,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    a, b, c, d] using core

theorem annotated_graph_secret_le_weight {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    expectedValue (annotatedJointGlobal interaction budget)
      (fun result =>
        ((2 * result.1.value.graphCalls : ENNReal) +
          result.2.length : ENNReal) / (2 : ENNReal) ^ 128) +
    expectedValue (annotatedJointGlobal interaction budget)
      (fun result =>
        (secretCount result.1 : ENNReal) / (2 : ENNReal) ^ 128) ≤
    expectedValue (annotatedJointGlobal interaction budget)
      (fun result => weight (jointCounts result)) := by
  rw [← expectedValue_add]
  apply expectedValue_mono_of_support
  intro result _
  exact graph_secret_weight result.1.value.graphCalls
    (secretCount result.1) result.2.length

theorem annotated_combined_risk_le_budget {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat)
    (indexBudget : ∀ answers cache,
      IndexBudget LIFETIME (viewOf answers interaction budget cache)) :
    Pr[fun result => result.1.bad = true ∨
      SecurityIndexTrace.Conflict result.2 |
      annotatedJointGlobal interaction budget] +
    expectedValue (annotatedJointGlobal interaction budget)
      (fun result =>
        (secretCount result.1 : ENNReal) / (2 : ENNReal) ^ 128) ≤
      (budget : ENNReal) / (2 : ENNReal) ^ 127 := by
  calc
    _ ≤ expectedValue (annotatedJointGlobal interaction budget)
          (fun result =>
            ((2 * result.1.value.graphCalls : ENNReal) +
              result.2.length : ENNReal) / (2 : ENNReal) ^ 128) +
        expectedValue (annotatedJointGlobal interaction budget)
          (fun result =>
            (secretCount result.1 : ENNReal) / (2 : ENNReal) ^ 128) :=
      add_le_add (annotated_bad_le_expected_graph_index
        interaction budget indexBudget) le_rfl
    _ ≤ expectedValue (annotatedJointGlobal interaction budget)
          (fun result => weight (jointCounts result)) :=
      annotated_graph_secret_le_weight interaction budget
    _ ≤ _ := annotated_expected_weight_le interaction budget

#print axioms annotate_index_budget
#print axioms annotated_bad_le_expected_graph_index
#print axioms annotated_expected_weight_le
#print axioms annotated_combined_risk_le_budget

end SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerJointRisk67
