import SigGolfCandidate.Hypertree.SecuritySecretKeyHonestSign

/-! Inlined from SigGolfCandidate.Hypertree.SecuritySecretKeyViewStop; its only importer was SigGolfCandidate.Hypertree.SecuritySecretKeyStoppedTrace. -/
section
namespace SigGolfCandidate.Hypertree.SecuritySecretKeyViewStop
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecuritySeparation SecurityGameHop
  SecurityMonitorView SecurityBudget
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

/-- The secret key monitor sees only public probes. Honest signing, private coins and
all adversary outputs retain their original continuation and responses. -/
noncomputable def secretKeyStopView {α : Type} (secretKey : SecretKey) : View α → View (Option α)
  | .done value => .done (some value)
  | .hash input next =>
      if publicSecretKeyHit secretKey (.inr input) then .done none
      else .hash input (fun answer => secretKeyStopView secretKey (next answer))
  | .sign message next => .sign message (fun response => secretKeyStopView secretKey (next response))
  | .coin n next => .coin n (fun answer => secretKeyStopView secretKey (next answer))

/-- Exact semantic boundary: the real oracle's secret key stop is the same stop in
the shared adversary view, including every internal honest signing query. -/
theorem realize_secretKeyStopView {α : Type} (secretKey : SecretKey) (view : View α) :
    stop secretKey (realize view) = realize (secretKeyStopView secretKey view) := by
  induction view with
  | done value => rfl
  | hash input next ih =>
    rw [realize, stop_query_bind, secretKeyStopView]
    change (if publicSecretKeyHit secretKey (.inr input) then pure none else _) = _
    split
    · rfl
    · simp only [realize]
      exact bind_congr ih
  | sign message next ih =>
    rw [realize, SecuritySecretKeyHonest.stop_signWire_bind]
    change (_ >>= _) = (_ >>= _)
    exact bind_congr ih
  | coin n next ih =>
    rw [realize, stop_query_bind]
    simp only [isBad, if_false, secretKeyStopView, realize]
    exact bind_congr ih

/-- The full reference experiment admits the same stopped view after its honest
key-generation prefix; no secret key hit can occur inside that prefix. -/
theorem stop_program (secretKey : SecretKey) (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds : Nat) :
    stop secretKey (SecurityExperiment.program publicCache adversary rounds) = (do
      let pk ← SecurityIdealKeygen.keygen.liftComp GameWorld
      realize (secretKeyStopView secretKey (ofInteract adversary pk rounds (adversary.initial pk publicCache) {}))) := by
  rw [SecurityMonitorView.program_eq, (SecuritySecretKeyHonest.keygen.lift secretKey).stop_bind]
  exact bind_congr (fun _ => realize_secretKeyStopView secretKey _)

/-- The budget stop and secret key stop can be interchanged once either abort is
represented by the same `none`. This retains every completed output exactly. -/
theorem cutoff_stop_join {α : Type} (secretKey : SecretKey) (program : OracleComp GameWorld α) (budget : Nat) :
    Option.join <$> stop secretKey (cutoff program budget) =
      Option.join <$> cutoff (stop secretKey program) budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => simp
  | query_bind input next ih =>
    rw [cutoff_query_bind]
    by_cases enough : charge input ≤ budget
    · rw [if_pos enough, stop_query_bind, stop_query_bind]
      by_cases hit : isBad secretKey input
      · simp only [if_pos hit, cutoff_pure, map_pure, Option.join_none, Option.join_some]
      · rw [if_neg hit, if_neg hit, cutoff_query_bind, if_pos enough]
        simp only [map_bind]
        exact bind_congr (fun answer => ih answer (budget - charge input))
    · rw [if_neg enough, stop_pure, stop_query_bind]
      by_cases hit : isBad secretKey input
      · simp only [if_pos hit, cutoff_pure, map_pure, Option.join_none, Option.join_some]
      · rw [if_neg hit, cutoff_query_bind, if_neg enough]
        rfl

/-- Fixed-cutoff real-to-independent-private coupling at the shared view boundary.
This is an exact distribution, before any secret key or graph probability bound. -/
theorem real_view_stopped {α : Type} (secretKey : SecretKey) (view : View α) (budget : Nat) :
    Option.join <$> (simulateQ (realGameOracle secretKey) (stop secretKey (cutoff (realize view) budget))).run' ∅ =
      Option.join <$> (simulateQ idealGameOracle
        (cutoff (realize (secretKeyStopView secretKey view)) budget)).run' (∅, ∅) := by
  rw [SecurityGameHop.stopped_separation secretKey _ ∅ (∅, ∅) (by constructor <;> intros <;> rfl)]
  rw [←realize_secretKeyStopView]
  have same := congrArg (fun program : OracleComp GameWorld (Option α) =>
    (simulateQ idealGameOracle program).run' (∅, ∅)) (cutoff_stop_join secretKey (realize view) budget)
  simpa only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map] using same

/-- The actual experiment has the identical cutoff/secret key-stop coupling, with the
shared stopped view reached after the actual honest keygen program. -/
theorem real_program_stopped (secretKey : SecretKey) (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) :
    Option.join <$> (simulateQ (realGameOracle secretKey)
      (stop secretKey (cutoff (SecurityExperiment.program publicCache adversary rounds) budget))).run' ∅ =
      Option.join <$> (simulateQ idealGameOracle (cutoff (do
        let pk ← SecurityIdealKeygen.keygen.liftComp GameWorld
        realize (secretKeyStopView secretKey (ofInteract adversary pk rounds (adversary.initial pk publicCache) {}))) budget)).run' (∅, ∅) := by
  rw [SecurityGameHop.stopped_separation secretKey _ ∅ (∅, ∅) (by constructor <;> intros <;> rfl)]
  rw [←stop_program]
  have same := congrArg (fun program : OracleComp GameWorld (Option SecurityExperiment.Result) =>
    (simulateQ idealGameOracle program).run' (∅, ∅))
    (cutoff_stop_join secretKey (SecurityExperiment.program publicCache adversary rounds) budget)
  simpa only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map] using same

/-- info: 'SigGolfCandidate.Hypertree.SecuritySecretKeyViewStop.real_program_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms real_program_stopped
end SigGolfCandidate.Hypertree.SecuritySecretKeyViewStop

end

namespace SigGolfCandidate.Hypertree.SecuritySecretKeyStoppedTrace
open SigGolf OracleComp OracleComp.EvalDist OracleSpec SecuritySecretKey SecurityDerivation
  SecuritySeparation SecurityGameHop SecurityBudget
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

noncomputable def keep {α : Type} (secretKey : SecretKey) (result : α × List Query) : Option α :=
  if SecretKeyHitTrace result.2 secretKey then none else some result.1

private theorem run_query {σ α : Type} (implementation : QueryImpl GameWorld (StateT σ ProbComp))
    (input : GameWorld.Domain) (next : GameWorld.Range input → OracleComp GameWorld α) (cache : σ) :
    (simulateQ implementation (liftM (GameWorld.query input) >>= next)).run' cache =
      ((implementation input).run cache >>= fun result =>
        (simulateQ implementation (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, StateT.run'_eq, StateT.run_bind, map_bind]

private theorem run_map {σ α β : Type} (implementation : QueryImpl GameWorld (StateT σ ProbComp))
    (program : OracleComp GameWorld α) (f : α → β) (cache : σ) :
    (simulateQ implementation (f <$> program)).run' cache =
      f <$> (simulateQ implementation program).run' cache := by
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]

private theorem map_const {α β : Type} (program : ProbComp α) (value : β) :
    𝒮[(fun _ => value) <$> program] = 𝒮[(pure value : ProbComp β)] := by
  classical
  let : DecidableEq β := Classical.decEq β
  apply evalSPMF_ext
  intro output
  simp only [map_eq_pure_bind, probOutput_bind_const]
  simp

/-- Stopping before a secret key guess is exactly forgetting secret key-hit outcomes of the
full passive trace. The retained output can contain all other counters/results. -/
theorem stopped_eq_trace {σ α : Type} (implementation : QueryImpl GameWorld (StateT σ ProbComp))
    (secretKey : SecretKey) (program : OracleComp GameWorld α) (cache : σ) :
    𝒮[(simulateQ implementation (stop secretKey program)).run' cache] =
      𝒮[keep secretKey <$> (simulateQ implementation (tracePublic program)).run' cache] := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value => simp [keep, SecretKeyHitTrace]
  | query_bind input next ih =>
    rw [stop_query_bind, tracePublic_query_bind]
    by_cases hit : isBad secretKey input
    · rw [if_pos hit, run_query]
      simp only [bind_pure_comp, run_map, map_bind, Functor.map_map]
      have constant : (fun result : α × List Query => keep secretKey (result.1, prependPublic input result.2)) =
          fun _ => (none : Option α) := by
        funext result
        simp only [keep, hit_prepend, hit, true_or, if_true]
      rw [constant]
      simpa only [map_bind, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure] using (map_const
        ((implementation input).run cache >>= fun result =>
          (simulateQ implementation (tracePublic (next result.1))).run' result.2)
        (none : Option α)).symm
    · rw [if_neg hit, run_query, run_query]
      simp only [bind_pure_comp, run_map, map_bind, Functor.map_map]
      apply evalSPMF_bind_congr
      intro result _
      rw [ih result.1 result.2]
      congr 1
      congr 1
      funext tail
      simp only [keep, hit_prepend, hit, false_or]

/-- Logging secret key-eligible public inputs leaves the actual output unchanged. -/
theorem trace_output {α : Type} (program : OracleComp GameWorld α) :
    Prod.fst <$> tracePublic program = program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
    rw [tracePublic_query_bind]
    simp only [map_bind, bind_pure_comp, Functor.map_map]
    exact bind_congr ih

theorem run_trace_output {σ α : Type} (implementation : QueryImpl GameWorld (StateT σ ProbComp))
    (program : OracleComp GameWorld α) (cache : σ) :
    Prod.fst <$> (simulateQ implementation (tracePublic program)).run' cache =
      (simulateQ implementation program).run' cache := by
  rw [←run_map, trace_output]

/-- A successful real run is included in a single ideal-world union event:
the same result succeeds, or its passive secret key trace hits. No expected cost is
transferred between games and no separate additive secret key penalty is introduced. -/
theorem real_le_ideal_union {α : Type} (secretKey : SecretKey) (program : OracleComp GameWorld α) (event : α → Prop) :
    Pr[event | (simulateQ (realGameOracle secretKey) program).run' ∅] ≤
      Pr[fun result => event result.1 ∨ SecretKeyHitTrace result.2 secretKey |
        (simulateQ idealGameOracle (tracePublic program)).run' (∅, ∅)] := by
  let lifted : Option α → Prop := fun value => match value with | none => True | some value => event value
  have same : 𝒮[keep secretKey <$> (simulateQ (realGameOracle secretKey) (tracePublic program)).run' ∅] =
      𝒮[keep secretKey <$> (simulateQ idealGameOracle (tracePublic program)).run' (∅, ∅)] := by
    rw [←stopped_eq_trace, ←stopped_eq_trace,
      SecurityGameHop.stopped_separation secretKey program ∅ (∅, ∅) (by constructor <;> intros <;> rfl)]
  have events := probEvent_congr' (p := lifted) (q := lifted) (fun _ _ => Iff.rfl) same
  rw [probEvent_map, probEvent_map] at events
  have keep_event (result : α × List Query) : lifted (keep secretKey result) ↔ event result.1 ∨ SecretKeyHitTrace result.2 secretKey := by
    simp only [keep]
    split <;> simp_all [lifted]
  simp_rw [Function.comp_def, keep_event] at events
  rw [←events, ←run_trace_output (realGameOracle secretKey) program ∅, probEvent_map]
  exact probEvent_mono (fun _ _ h => Or.inl h)

/-- The union coupling applies directly to the organizer's total-call cutoff,
including executions which exhaust the budget during an honest block. -/
theorem real_cutoff_le_ideal_union {α : Type} (secretKey : SecretKey) (program : OracleComp GameWorld α)
    (budget : Nat) (event : Option α → Prop) :
    Pr[event | (simulateQ (realGameOracle secretKey) (cutoff program budget)).run' ∅] ≤
      Pr[fun result => event result.1 ∨ SecretKeyHitTrace result.2 secretKey |
        (simulateQ idealGameOracle (tracePublic (cutoff program budget))).run' (∅, ∅)] :=
  real_le_ideal_union secretKey (cutoff program budget) event

/-- info: 'SigGolfCandidate.Hypertree.SecuritySecretKeyStoppedTrace.real_cutoff_le_ideal_union' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms real_cutoff_le_ideal_union
end SigGolfCandidate.Hypertree.SecuritySecretKeyStoppedTrace
