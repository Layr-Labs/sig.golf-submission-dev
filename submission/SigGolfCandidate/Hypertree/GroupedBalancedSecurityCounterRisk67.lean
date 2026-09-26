import SigGolfCandidate.Hypertree.GroupedBalancedSecurityCounterPaired67
import SigGolfCandidate.Hypertree.GroupedBalancedSecurityVerifyAvoids67
import SigGolfCandidate.Hypertree.GroupedBalancedPlantedSecretKeyUnion67
import SigGolfCandidate.Hypertree.GroupedBalancedPlantedRealJointUnion67
import SigGolfCandidate.Hypertree.GroupedBalancedOrganizerFinalRisk67

/-! The real and ideal planted graph games have the same first-secret-hit
union event on their public query traces. This is the exact stopped-separation
boundary used before the graph monitor's quantitative risk accounting. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityCounterRisk67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedPlantedCache67
open GroupedBalancedPlantedSecretKeyUnion67
open GroupedBalancedPlantedRealUnion67
open GroupedBalancedPlantedRealJointUnion67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedSecurityOfficialHybrid67
open SecurityGameHop SecuritySecretKeyStoppedTrace SecuritySecretKey
open scoped Classical

set_option maxRecDepth 8192

theorem planted_real_trace_union_eq_ideal {α : Type}
    (table : PointTable) (secretKey : SecretKey)
    (program : OracleComp GameWorld α) (event : α → Prop) :
    Pr[fun result : α × List Query =>
      event result.1 ∨ SecretKeyHitTrace result.2 secretKey |
      (simulateQ (realGameOracle secretKey)
        (tracePublic program)).run' (planted table)] =
    Pr[fun result : α × List Query =>
      event result.1 ∨ SecretKeyHitTrace result.2 secretKey |
      (simulateQ idealGameOracle
        (tracePublic program)).run' (∅, planted table)] := by
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
    (p := StoppedRisk event) (q := StoppedRisk event)
    (fun _ _ => Iff.rfl) same
  simp only [probEvent_map, Function.comp_def] at events
  have keep_event (result : α × List Query) :
      StoppedRisk event (keep secretKey result) ↔
        event result.1 ∨ SecretKeyHitTrace result.2 secretKey := by
    simp only [keep]
    split <;> simp_all [StoppedRisk]
  simpa only [keep_event] using events

#print axioms planted_real_trace_union_eq_ideal

theorem planted_real_trace_union_eq_eager {α : Type}
    (table : PointTable) (secretKey : SecretKey)
    (cache : QueryCache PointSpec)
    (interaction : GroupedBalancedGraphInteraction67.Interaction α)
    (budget : Nat) (event : Option α → Prop) :
    Pr[fun result : Option α × List Query =>
      event result.1 ∨ SecretKeyHitTrace result.2 secretKey |
      (simulateQ (realGameOracle secretKey)
        (tracePublic (SecurityBudget.cutoff
          (GroupedBalancedGameWorld67.gameView table cache interaction)
          budget))).run' (planted table)] =
    Pr[fun result : Option α ×
        List GroupedBalancedGameQueryTrace67.Action =>
      event result.1 ∨
        SecretKeyHitTrace
          (GroupedBalancedGameQueryTrace67.secretInputs result.2)
          secretKey |
      GroupedBalancedPlantedEagerHop67.eagerSimulation table cache
        interaction budget] := by
  rw [planted_real_trace_union_eq_ideal]
  have same := ideal_trace_eq_eager table cache interaction budget
  have events := probEvent_congr'
    (p := fun result : Option α × List Query =>
      event result.1 ∨ SecretKeyHitTrace result.2 secretKey)
    (q := fun result : Option α × List Query =>
      event result.1 ∨ SecretKeyHitTrace result.2 secretKey)
    (fun _ _ => Iff.rfl) same
  rw [events, probEvent_map]
  rfl

#print axioms planted_real_trace_union_eq_eager

noncomputable def realTraceGlobal {α : Type}
    (interaction : QueryCache PointSpec →
      GroupedBalancedGraphInteraction67.Interaction α)
    (budget : Nat) : ProbComp
      (SecretKey × (Option α × List Query)) := do
  let table ← $ᵗ PointTable
  let secretKey ← sampleSecretKey
  let result ← (simulateQ (realGameOracle secretKey)
    (tracePublic (SecurityBudget.cutoff
      (GroupedBalancedGameWorld67.gameView table
        (GroupedBalancedGraphMonitorSetup67.cache table)
        (interaction (GroupedBalancedGraphMonitorSetup67.cache table)))
      budget))).run' (planted table)
  pure (secretKey, result)

theorem real_trace_le_annotated_raw {α : Type}
    (interaction : QueryCache PointSpec →
      GroupedBalancedGraphInteraction67.Interaction α)
    (budget : Nat) (event : Option α → Prop) :
    Pr[fun result : SecretKey × (Option α × List Query) =>
      event result.2.1 ∨ SecretKeyHitTrace result.2.2 result.1 |
      realTraceGlobal interaction budget] ≤
    Pr[fun result =>
      let plain := GroupedBalancedGraphIndexJointClassTrace67.eraseRun result.2
      plain.1.bad = true ∨
        GroupedBalancedPlantedEagerUnion67.optionEvent
          (fun value : Option α × List Action =>
            event value.1 ∨
              SecretKeyHitTrace (secretInputs value.2) result.1)
          plain.1.value.value |
      annotatedSecretGlobal interaction budget] := by
  have first :
      Pr[fun result : SecretKey × (Option α × List Query) =>
        event result.2.1 ∨ SecretKeyHitTrace result.2.2 result.1 |
        realTraceGlobal interaction budget] =
      Pr[fun result : SecretKey × (Option α × List Action) =>
        event result.2.1 ∨
          SecretKeyHitTrace (secretInputs result.2.2) result.1 |
        eagerSecretGlobal interaction budget] := by
    unfold realTraceGlobal eagerSecretGlobal
    conv_lhs => rw [probEvent_bind_eq_tsum]
    conv_rhs => rw [probEvent_bind_eq_tsum]
    apply tsum_congr
    intro table
    congr 1
    conv_lhs => rw [probEvent_bind_eq_tsum]
    conv_rhs => rw [probEvent_bind_eq_tsum]
    apply tsum_congr
    intro secretKey
    congr 1
    simpa only [bind_pure_comp, probEvent_map, Function.comp_def] using
      (planted_real_trace_union_eq_eager table secretKey
        (GroupedBalancedGraphMonitorSetup67.cache table)
        (interaction (GroupedBalancedGraphMonitorSetup67.cache table))
        budget event)
  have swapped := eagerSecretGlobal_swap interaction budget
  have events := probEvent_congr'
    (p := fun result : SecretKey × (Option α × List Action) =>
      event result.2.1 ∨
        SecretKeyHitTrace (secretInputs result.2.2) result.1)
    (q := fun result : SecretKey × (Option α × List Action) =>
      event result.2.1 ∨
        SecretKeyHitTrace (secretInputs result.2.2) result.1)
    (fun _ _ => Iff.rfl) swapped
  rw [events] at first
  apply first.le.trans
  unfold annotatedSecretGlobal
  conv_lhs => rw [probEvent_bind_eq_tsum]
  conv_rhs => rw [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro secretKey
  apply mul_le_mul' le_rfl
  simpa only [bind_pure_comp, probEvent_map, Function.comp_def] using
    (GroupedBalancedPlantedEagerAnnotated67.eager_global_le_annotated_union
      interaction budget
      (fun value => event value.1 ∨
        SecretKeyHitTrace (secretInputs value.2) secretKey))

#print axioms real_trace_le_annotated_raw

theorem real_trace_le_annotated {α : Type}
    (interaction : QueryCache PointSpec →
      GroupedBalancedGraphInteraction67.Interaction α)
    (budget : Nat) (event : Option α → Prop) :
    Pr[fun result : SecretKey × (Option α × List Query) =>
      event result.2.1 ∨ SecretKeyHitTrace result.2.2 result.1 |
      realTraceGlobal interaction budget] ≤
    Pr[fun result =>
      let plain := GroupedBalancedGraphIndexJointClassTrace67.eraseRun result.2
      plain.1.bad = true ∨
        GroupedBalancedPlantedEagerUnion67.optionEvent
          (fun value : Option α × List Action => event value.1)
          plain.1.value.value ∨
        SecretKeyHitTrace
          (GroupedBalancedEagerSecretHit67.stoppedInputs plain)
          result.1 |
      annotatedSecretGlobal interaction budget] := by
  apply (real_trace_le_annotated_raw interaction budget event).trans_eq
  apply probEvent_congr' _ rfl
  intro result _
  let plain := GroupedBalancedGraphIndexJointClassTrace67.eraseRun result.2
  have hit :=
    (GroupedBalancedEagerSecretHit67.stopped_hit_iff_option plain result.1)
  change (plain.1.bad = true ∨
      GroupedBalancedPlantedEagerUnion67.optionEvent
        (fun value : Option α × List Action =>
          event value.1 ∨
            SecretKeyHitTrace (secretInputs value.2) result.1)
        plain.1.value.value) ↔
      (plain.1.bad = true ∨
        GroupedBalancedPlantedEagerUnion67.optionEvent
          (fun value : Option α × List Action => event value.1)
          plain.1.value.value ∨
        SecretKeyHitTrace
          (GroupedBalancedEagerSecretHit67.stoppedInputs plain)
          result.1)
  rw [hit]
  cases h : plain.1.value.value with
  | none => simp [GroupedBalancedPlantedEagerUnion67.optionEvent, h]
  | some pair => simp [GroupedBalancedPlantedEagerUnion67.optionEvent, h,
      or_assoc]

#print axioms real_trace_le_annotated

private abbrev sizes := GroupedBalancedOrganizerWinningExtraction67.sizes
private abbrev OrganizerResult :=
  GroupedBalancedGraphOrganizerView67.Result sizes

theorem real_trace_winner_hit_le_budget
    (adversary : Adversary sizes) (rounds budget : Nat) :
    Pr[fun result : SecretKey × (Option OrganizerResult × List Query) =>
      (∃ outcome : OrganizerResult,
        result.2.1 = some outcome ∧ outcome.won = true) ∨
        SecretKeyHitTrace result.2.2 result.1 |
      realTraceGlobal
        (GroupedBalancedPlantedEagerOrganizerRisk67.organizerInteraction
          sizes GroupedBalancedWire67.wire GroupedBalancedWire67.decode
          GroupedBalancedWire67.decode adversary (0 : Cache) rounds)
        budget] ≤
      (budget : ENNReal) / (2 : ENNReal)^127 := by
  let interaction :=
    GroupedBalancedPlantedEagerOrganizerRisk67.organizerInteraction
      sizes GroupedBalancedWire67.wire GroupedBalancedWire67.decode
      GroupedBalancedWire67.decode adversary (0 : Cache) rounds
  have first := real_trace_le_annotated interaction budget
    (fun value : Option OrganizerResult =>
      ∃ outcome : OrganizerResult,
        value = some outcome ∧ outcome.won = true)
  have second :=
    GroupedBalancedOrganizerFinalRisk67.annotated_risk_probability_le_budget
      adversary (0 : Cache) rounds budget
  exact first.trans second

#print axioms real_trace_winner_hit_le_budget

theorem joint_graph_cutoff_winner_le_budget
    (adversary : Adversary sizes) (rounds budget : Nat) :
    let interaction :=
      GroupedBalancedPlantedEagerOrganizerRisk67.organizerInteraction
        sizes GroupedBalancedWire67.wire GroupedBalancedWire67.decode
        GroupedBalancedWire67.decode adversary (0 : Cache) rounds
    Pr[fun value : Option OrganizerResult =>
      ∃ outcome : OrganizerResult,
        value = some outcome ∧ outcome.won = true |
      GroupedBalancedSecurityVerifyAvoids67.jointProgram
        (fun secretKey table =>
          GroupedBalancedGameWorld67.resolve secretKey
            (SecurityBudget.cutoff
              (GroupedBalancedGameWorld67.gameView table
                (GroupedBalancedGraphMonitorSetup67.cache table)
                (interaction (GroupedBalancedGraphMonitorSetup67.cache table)))
              budget))] ≤
      (budget : ENNReal) / (2 : ENNReal)^127 := by
  let interaction :=
    GroupedBalancedPlantedEagerOrganizerRisk67.organizerInteraction
      sizes GroupedBalancedWire67.wire GroupedBalancedWire67.decode
      GroupedBalancedWire67.decode adversary (0 : Cache) rounds
  have first :=
    GroupedBalancedSecurityVerifyAvoids67.joint_graph_cutoff_le_planted_trace
      interaction budget
      (fun value : Option OrganizerResult =>
        ∃ outcome : OrganizerResult,
          value = some outcome ∧ outcome.won = true)
  have second := real_trace_winner_hit_le_budget adversary rounds budget
  exact first.trans (by
    simpa only [GroupedBalancedSecurityVerifyAvoids67.plantedRealTraceProgram,
      realTraceGlobal, interaction] using second)

#print axioms joint_graph_cutoff_winner_le_budget

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityCounterRisk67
