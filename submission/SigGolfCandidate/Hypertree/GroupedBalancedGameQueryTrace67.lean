import SigGolfCandidate.Hypertree.GroupedBalancedQueryClasses67
import SigGolfCandidate.Hypertree.SecurityBudget

/-! A generic GameWorld hash-query log records public and typed private calls.
The old secret-key probes, direct67 graph inputs, and H5 inputs partition its
public query classes; typed private derivations still consume total budget. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGameQueryTrace67
open SigGolf SigGolfCandidate.Hypertree OracleComp OracleComp.EvalDist OracleSpec
open SecurityGameHop SecuritySharedBudget
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

inductive Action where
  | publicHash (input : Query)
  | privateHash

noncomputable def Action.charge : Action → Counts
  | .publicHash input => GroupedBalancedQueryClasses67.charge input
  | .privateHash => ⟨0, 0, 0⟩

theorem Action.charge_total_le_one (action : Action) :
    action.charge.total ≤ 1 := by
  cases action with
  | publicHash input =>
      exact GroupedBalancedQueryClasses67.charge_total_le_one input
  | privateHash => simp [Action.charge, Counts.total]

noncomputable def counts : List Action → Counts
  | [] => ⟨0, 0, 0⟩
  | action :: rest =>
      let head := action.charge
      let tail := counts rest
      ⟨head.secretKey + tail.secretKey,
        head.graph + tail.graph,
        head.index + tail.index⟩

theorem counts_total_le_length (trace : List Action) :
    (counts trace).total ≤ trace.length := by
  induction trace with
  | nil => simp [counts, Counts.total]
  | cons action rest ih =>
      have one := Action.charge_total_le_one action
      simp only [counts, Counts.total, List.length_cons] at ih one ⊢
      omega

def prepend (query : GameWorld.Domain) (trace : List Action) :
    List Action :=
  match query with
  | .inl _ => trace
  | .inr (.inl _) => .privateHash :: trace
  | .inr (.inr input) => .publicHash input :: trace

theorem prepend_length (query : GameWorld.Domain)
    (trace : List Action) :
    (prepend query trace).length =
      trace.length + SecurityBudget.charge query := by
  cases query with
  | inl _ => simp [prepend, SecurityBudget.charge]
  | inr query =>
      cases query <;> simp [prepend, SecurityBudget.charge]

def logged {α : Type} (program : OracleComp GameWorld α) :
    OracleComp GameWorld (α × List Action) :=
  OracleComp.construct (fun value => pure (value, []))
    (fun query _ next => do
      let answer ← liftM (GameWorld.query query)
      let result ← next answer
      pure (result.1, prepend query result.2)) program

@[simp] theorem logged_pure {α : Type} (value : α) :
    logged (pure value : OracleComp GameWorld α) =
      pure (value, []) := rfl

theorem logged_query_bind {α : Type} (query : GameWorld.Domain)
    (next : GameWorld.Range query → OracleComp GameWorld α) :
    logged (liftM (GameWorld.query query) >>= next) = (do
      let answer ← liftM (GameWorld.query query)
      let result ← logged (next answer)
      pure (result.1, prepend query result.2)) := rfl

theorem counted_eq_logged_length {α : Type}
    (program : OracleComp GameWorld α) :
    SecurityBudget.counted program =
      (fun result => (result.1, result.2.length)) <$> logged program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      rw [SecurityBudget.counted_query_bind, logged_query_bind]
      simp only [map_bind]
      apply bind_congr
      intro answer
      rw [ih answer]
      simp only [map_eq_pure_bind, bind_assoc, pure_bind,
        prepend_length]

noncomputable def secretInputs : List Action → List Query
  | [] => []
  | .privateHash :: rest => secretInputs rest
  | .publicHash input :: rest =>
      if SecuritySeparation.SecretKeyEligible input then
        input :: secretInputs rest else secretInputs rest

theorem secretInputs_prepend (query : GameWorld.Domain)
    (trace : List Action) :
    secretInputs (prepend query trace) =
      SecurityGameHop.prependPublic query (secretInputs trace) := by
  cases query with
  | inl _ => rfl
  | inr query =>
      cases query with
      | inl _ => rfl
      | inr input =>
          by_cases eligible : SecuritySeparation.SecretKeyEligible input <;>
            simp [secretInputs, prepend, SecurityGameHop.prependPublic,
              eligible]

/-- The older secret-key monitor's eligible-query log is exactly the
secret-key projection of this shared full hash-query log. -/
theorem tracePublic_eq_logged_secretInputs {α : Type}
    (program : OracleComp GameWorld α) :
    SecurityGameHop.tracePublic program =
      (fun result => (result.1, secretInputs result.2)) <$>
        logged program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      rw [SecurityGameHop.tracePublic_query_bind,
        logged_query_bind]
      simp only [map_bind]
      apply bind_congr
      intro answer
      rw [ih answer]
      simp only [map_eq_pure_bind, bind_assoc, pure_bind,
        secretInputs_prepend]

theorem secretInputs_length_eq_count (trace : List Action) :
    (secretInputs trace).length = (counts trace).secretKey := by
  induction trace with
  | nil => rfl
  | cons action rest ih =>
      cases action with
      | privateHash =>
          simpa [secretInputs, counts, Action.charge] using ih
      | publicHash input =>
          by_cases eligible : SecuritySeparation.SecretKeyEligible input <;>
            simp [secretInputs, counts, Action.charge,
              GroupedBalancedQueryClasses67.charge, eligible, ih] <;> omega

/-- The sharp legacy secret-key penalty is exactly the secret-key class count
in the same full ideal GameWorld hash-query log. -/
theorem expectedSecretKeyQueries_eq_class {α : Type}
    (program : OracleComp GameWorld α)
    (cache : SecuritySeparation.SplitCache) :
    SecurityGameHop.expectedSecretKeyQueries program cache =
    expectedValue
      ((simulateQ idealGameOracle (logged program)).run' cache)
      (fun result => ((counts result.2).secretKey : ENNReal)) := by
  change expectedValue
    ((simulateQ idealGameOracle
      (SecurityGameHop.tracePublic program)).run' cache)
      (fun result => (result.2.length : ENNReal)) = _
  rw [tracePublic_eq_logged_secretInputs]
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map, expectedValue_map, Function.comp_def,
    secretInputs_length_eq_count]

#print axioms counts_total_le_length
#print axioms counted_eq_logged_length
#print axioms tracePublic_eq_logged_secretInputs
#print axioms expectedSecretKeyQueries_eq_class

end SigGolfCandidate.Hypertree.GroupedBalancedGameQueryTrace67
