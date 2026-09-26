import SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerAnnotated67
import SigGolfCandidate.Hypertree.SecuritySecretKeyStoppedTrace

/-! A planted-cache real-to-ideal union hop.  The secret-key event is kept as
an event on the ideal public-query trace, so later graph stopping can absorb
any probes that would have occurred after first graph contact. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPlantedSecretKeyUnion67
open SigGolf SigGolfCandidate.Hypertree OracleComp OracleComp.EvalDist OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedPlantedCache67
open GroupedBalancedGameQueryTrace67
open SecurityGameHop SecuritySecretKeyStoppedTrace SecuritySecretKey
open GroupedBalancedGraphInteraction67 GroupedBalancedGameWorld67
open GroupedBalancedPlantedEagerHop67
open GroupedBalancedIdealEagerCutoff67
open SecurityGraphIdeal SecurityGraphHidden
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem planted_real_le_ideal_union {α : Type} (table : PointTable)
    (secretKey : SecretKey) (program : OracleComp GameWorld α)
    (event : α → Prop) :
    Pr[event | (simulateQ (realGameOracle secretKey) program).run'
      (planted table)] ≤
    Pr[fun result => event result.1 ∨
      SecretKeyHitTrace result.2 secretKey |
      (simulateQ idealGameOracle (tracePublic program)).run'
        (∅, planted table)] := by
  let lifted : Option α → Prop := fun value =>
    match value with
    | none => True
    | some value => event value
  have same :
      𝒮[keep secretKey <$>
        (simulateQ (realGameOracle secretKey)
          (tracePublic program)).run' (planted table)] =
      𝒮[keep secretKey <$>
        (simulateQ idealGameOracle
          (tracePublic program)).run' (∅, planted table)] := by
    rw [← stopped_eq_trace, ← stopped_eq_trace,
      SecurityGameHop.stopped_separation secretKey program
        (planted table) (∅, planted table)
        (planted_related table secretKey)]
  have events := probEvent_congr'
    (p := lifted) (q := lifted) (fun _ _ => Iff.rfl) same
  rw [probEvent_map, probEvent_map] at events
  have keep_event (result : α × List Query) :
      lifted (keep secretKey result) ↔
        event result.1 ∨ SecretKeyHitTrace result.2 secretKey := by
    simp only [keep]
    split <;> simp_all [lifted]
  simp_rw [Function.comp_def, keep_event] at events
  rw [← events,
    ← run_trace_output (realGameOracle secretKey) program (planted table),
    probEvent_map]
  exact probEvent_mono (fun _ _ h => Or.inl h)

theorem ideal_logged_eq_eager {α : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (interaction : Interaction α)
    (budget : Nat) :
    𝒮[(simulateQ idealGameOracle
      (logged (SecurityBudget.cutoff
        (gameView table cache interaction) budget))).run'
        (∅, planted table)] =
    𝒮[eagerSimulation table cache interaction budget] := by
  calc
    _ = 𝒮[do
      let answers ← $ᵗ PrivateTable
      observe
        (fixPrivate answers
          (logged (SecurityBudget.cutoff
            (gameView table cache interaction) budget)))
        (planted table)] := by
      have emptyExt (answers : PrivateTable) :
          extendPrivate ∅ answers = answers := by
        funext slot
        simp [extendPrivate]
      simpa only [idealObserve, emptyExt] using
        SecurityGraphIdeal.ideal_private_table
          (logged (SecurityBudget.cutoff
            (gameView table cache interaction) budget))
          ∅ (planted table)
    _ = _ := by
      simp_rw [fixPrivate_logged_cutoff]
      rfl

theorem ideal_trace_eq_eager {α : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (interaction : Interaction α)
    (budget : Nat) :
    𝒮[(simulateQ idealGameOracle
      (tracePublic (SecurityBudget.cutoff
        (gameView table cache interaction) budget))).run'
        (∅, planted table)] =
    𝒮[(fun result => (result.1, secretInputs result.2)) <$>
      eagerSimulation table cache interaction budget] := by
  have projection :
      (simulateQ idealGameOracle
        (tracePublic (SecurityBudget.cutoff
          (gameView table cache interaction) budget))).run'
          (∅, planted table) =
      (fun result => (result.1, secretInputs result.2)) <$>
        (simulateQ idealGameOracle
          (logged (SecurityBudget.cutoff
            (gameView table cache interaction) budget))).run'
              (∅, planted table) := by
    rw [tracePublic_eq_logged_secretInputs]
    simp only [simulateQ_map, StateT.run'_eq, StateT.run_map,
      Functor.map_map, Function.comp_def]
  rw [projection, evalSPMF_map,
    ideal_logged_eq_eager table cache interaction budget,
    ← evalSPMF_map]

theorem planted_real_le_eager_union {α : Type} (table : PointTable)
    (secretKey : SecretKey) (cache : QueryCache PointSpec)
    (interaction : Interaction α) (budget : Nat)
    (event : Option α → Prop) :
    Pr[event |
      (simulateQ (realGameOracle secretKey)
        (SecurityBudget.cutoff (gameView table cache interaction)
          budget)).run' (planted table)] ≤
    Pr[fun result => event result.1 ∨
      SecretKeyHitTrace (secretInputs result.2) secretKey |
      eagerSimulation table cache interaction budget] := by
  have bound := planted_real_le_ideal_union table secretKey
    (SecurityBudget.cutoff (gameView table cache interaction) budget)
    event
  have same := ideal_trace_eq_eager table cache interaction budget
  have events := probEvent_congr'
    (p := fun result => event result.1 ∨
      SecretKeyHitTrace result.2 secretKey)
    (q := fun result => event result.1 ∨
      SecretKeyHitTrace result.2 secretKey)
    (fun _ _ => Iff.rfl) same
  rw [events, probEvent_map] at bound
  simpa only [Function.comp_def] using bound

#print axioms planted_real_le_ideal_union
#print axioms ideal_trace_eq_eager
#print axioms planted_real_le_eager_union

end SigGolfCandidate.Hypertree.GroupedBalancedPlantedSecretKeyUnion67
