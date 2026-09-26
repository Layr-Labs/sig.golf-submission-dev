import SigGolfCandidate.Hypertree.SecurityMonitorVerifyBudget
import SigGolfCandidate.Hypertree.SecurityMonitorWinInteraction

/-! Inlined from SigGolfCandidate.Hypertree.SecurityMonitorResidual; its only importer was SigGolfCandidate.Hypertree.SecurityMonitorWin. -/
section
namespace SigGolfCandidate.Hypertree.SecurityMonitorResidual
open SigGolf OracleComp OracleSpec Reference SecurityGraphFactor SecurityGraphPassive
  SecurityGraphMonitorProgram SecurityGraphMonitorCompose SecurityGraphMonitorNoContact
  SecurityGraphMonitorChainState SecurityGraphMonitorInvariant SecurityGraphMonitorPublicState
  SecurityGraphMonitorVerify SecurityGraphQuery SecurityGraphReference
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- A clean residual cache also agrees with the public programmed oracle. -/
theorem agrees_public (factors : Factors) (cache : QueryCache HashSpec)
    (safe : ResidualSafe factors cache) (base : Hash) (agree : cache.AgreesWithFn base) :
    cache.AgreesWithFn (programmed (privateTable factors) (labels factors) base) := by
  intro query answer present
  rw [locate_programmed]
  cases located : locate query with
  | none => exact agree present
  | some position =>
    dsimp only
    rw [if_neg (safe query answer present position located).1]
    exact agree present

/-- Sampling a residual query never changes an already cached answer. -/
theorem random_preserves (query : Query) (cache : QueryCache HashSpec)
    (result : BitVec 256 × QueryCache HashSpec)
    (member : result ∈ support ((randomOracle (spec := HashSpec) query).run cache))
    (old : Query) (value : BitVec 256) (present : cache old = some value) : result.2 old = some value := by
  cases found : cache query with
  | some answer =>
    simp only [randomOracle.run_eq, found, support_pure, Set.mem_singleton_iff] at member
    subst result
    exact present
  | none =>
    simp only [randomOracle.run_eq, found, bind_pure_comp, support_map, Set.mem_image] at member
    obtain ⟨answer, _, same⟩ := member
    cases same
    have different : old ≠ query := by intro equal; subst old; rw [found] at present; cases present
    simpa only [QueryCache.cacheQuery_of_ne _ _ different] using present

theorem random_present (query : Query) (cache : QueryCache HashSpec)
    (result : BitVec 256 × QueryCache HashSpec)
    (member : result ∈ support ((randomOracle (spec := HashSpec) query).run cache)) :
    result.2 query = some result.1 := by
  cases found : cache query with
  | some answer =>
    simp only [randomOracle.run_eq, found, support_pure, Set.mem_singleton_iff] at member
    subst result
    exact found
  | none =>
    simp only [randomOracle.run_eq, found, bind_pure_comp, support_map, Set.mem_image] at member
    obtain ⟨answer, _, same⟩ := member
    cases same
    exact QueryCache.cacheQuery_self ..

theorem query_preserves (factors : Factors) (query : Query) (cache : QueryCache HashSpec)
    (result : BitVec 256 × QueryCache HashSpec)
    (member : result ∈ support ((SecurityGraphOracle.publicOracle (privateTable factors) (labels factors) query).run cache))
    (old : Query) (value : BitVec 256) (present : cache old = some value) : result.2 old = some value := by
  cases canonical : SecurityGraphOracle.canonical (privateTable factors) (labels factors) query with
  | some answer =>
    simp only [SecurityGraphOracle.publicOracle, canonical, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst result
    exact present
  | none =>
    simp only [SecurityGraphOracle.publicOracle, canonical] at member
    exact random_preserves query cache result member old value present

/-- Every completed raw verifier preserves all earlier residual answers. -/
theorem completed_preserves {α : Type} (factors : Factors) (signed : Finset (BitVec 160))
    (program : OracleComp HashSpec α) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (initial : Safe factors signed exposed cache) (result : SecurityGraphMonitorVerify.Result α)
    (member : some result ∈ support (stopped factors.1 exposed (compile factors.2.2 program exposed cache)))
    (old : Query) (value : BitVec 256) (present : cache old = some value) : result.2.2 old = some value := by
  induction program using OracleComp.inductionOn generalizing exposed cache with
  | pure answer =>
    simp only [compile_pure, stopped, support_pure, Set.mem_singleton_iff, Option.some.injEq] at member
    subst result
    exact present
  | query_bind query next ih =>
    rw [compile_query, stopped_public_bind factors signed exposed cache initial, mem_support_bind_iff] at member
    obtain ⟨read, queried, tail⟩ := member
    cases read with
    | none => simp only [continueWith, support_pure, Set.mem_singleton_iff, Option.some_ne_none] at tail
    | some answer =>
      have spec := read_spec factors signed exposed cache initial query answer queried
      exact ih answer.1 answer.2.1 answer.2.2 (public_read_safe factors signed exposed cache initial query answer queried)
        tail (query_preserves factors query cache (answer.1,answer.2.2) spec.2.2.2 old value present)

/-- The first noncanonical query is present after any normally completed run. -/
theorem first_present {α : Type} (factors : Factors) (signed : Finset (BitVec 160))
    (query : Query) (next : BitVec 256 → OracleComp HashSpec α)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (initial : Safe factors signed exposed cache)
    (result : SecurityGraphMonitorVerify.Result α)
    (member : some result ∈ support (stopped factors.1 exposed
      (compile factors.2.2 (liftM (HashSpec.query query) >>= next) exposed cache)))
    (noncanonical : SecurityGraphOracle.canonical (privateTable factors) (labels factors) query = none) :
    result.2.2 query ≠ none := by
  rw [compile_query, stopped_public_bind factors signed exposed cache initial, mem_support_bind_iff] at member
  obtain ⟨read, queried, tail⟩ := member
  cases read with
  | none => simp only [continueWith, support_pure, Set.mem_singleton_iff, Option.some_ne_none] at tail
  | some answer =>
    have spec := read_spec factors signed exposed cache initial query answer queried
    have sampled := spec.2.2.2
    simp only [SecurityGraphOracle.publicOracle, noncanonical] at sampled
    have present := completed_preserves factors signed (next answer.1) answer.2.1 answer.2.2
      (public_read_safe factors signed exposed cache initial query answer queried) result tail query answer.1
      (random_present query cache _ sampled)
    rw [present]
    exact Option.some_ne_none _

/-- The actual verifier's H5 input remains cached for the extraction argument. -/
theorem verifier_index_present (factors : Factors) (signed : Finset (BitVec 160))
    (pk : PublicKey) (message : Message) (signature : SignatureEncoding.Compact)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (initial : Safe factors signed exposed cache)
    (result : SecurityGraphMonitorVerify.Result Bool)
    (member : some result ∈ support (stopped factors.1 exposed
      (compile factors.2.2 (SecurityVerify.verifyCompact pk message signature) exposed cache))) :
    result.2.2 (SecurityRandomOracle.indexInput message signature.randomizer) ≠ none := by
  exact first_present factors signed (SecurityRandomOracle.indexInput message signature.randomizer) _
    exposed cache initial result member (SecurityGraphState.canonical_index _ _ message signature.randomizer)

#print axioms verifier_index_present
end SigGolfCandidate.Hypertree.SecurityMonitorResidual

end

namespace SigGolfCandidate.Hypertree.SecurityMonitorWin
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference SecurityGraphFactor SecurityGraphPassive
  SecurityGraphMonitorProgram SecurityGraphMonitorSign SecurityGraphMonitorPublicCoupling
  SecurityMonitorView SecurityMonitorIndexState SecurityMonitorGraphView SecurityMonitorGraphState
  SecurityMonitorGraphStoppedView SecurityMonitorIndexContact SecurityGraphExtraction SecurityMonitorTranscript
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

 theorem checker_bad (factors : Factors) (transcript : Transcript submission.sizes)
    (forgery : Forgery submission.sizes) (remaining : Nat) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (history : History)
    (ready : Ready factors history exposed cache) (coherent : Coherent factors cache history transcript)
    (tracked : Tracked factors.2.1 cache history)
    (result : Result SecurityExperiment.Result) (outcome : SecurityExperiment.Result)
    (output : result.value = some outcome) (won : outcome.won = true)
    (member : some result ∈ support (execute factors
      (ofCheck (publicKey factors) transcript forgery) remaining exposed cache history)) :
    SecurityIndexTrace.Conflict result.history.indexTrace ∨ NonceHit factors.2.1 result.history := by
  let base := completion result.residual
  have agree := completion_agrees result.residual
  obtain ⟨reuse, honest, messages, raw⟩ := check_reuse factors transcript forgery remaining exposed cache history
    ready coherent result outcome output won member base agree
  have replay := SecurityGraphMonitorVerify.completed factors history.signedIndices _ exposed cache ready.1
    (true,result.exposed,result.residual) raw base agree
  have publicAgree := SecurityMonitorResidual.agrees_public factors result.residual replay.2.2.1.2.2 base agree
  have present := SecurityMonitorResidual.verifier_index_present factors history.signedIndices (publicKey factors)
    (candidate forgery).1 (candidate forgery).2 exposed cache ready.1
    (true,result.exposed,result.residual) raw
  have finalTracked := execute_tracked factors _
    remaining exposed cache history tracked result member
  obtain ⟨draws, provenance⟩ := finalTracked.2.2
  exact extraction_contact factors base (responses transcript) result.history result.residual draws
    provenance honest messages publicAgree (candidate forgery).1 (candidate forgery).2 present reuse

/-- All state and transcript premises are propagated through the actual finite
adversary interaction before applying the final checker extraction. -/
theorem interaction_bad (factors : Factors) (adversary : Adversary submission.sizes)
    (rounds : Nat) (state : adversary.State) (transcript : Transcript submission.sizes)
    (remaining : Nat) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (history : History)
    (ready : Ready factors history exposed cache) (coherent : Coherent factors cache history transcript)
    (tracked : Tracked factors.2.1 cache history)
    (result : Result SecurityExperiment.Result) (outcome : SecurityExperiment.Result)
    (output : result.value = some outcome) (won : outcome.won = true)
    (member : some result ∈ support (execute factors
      (ofInteract adversary (publicKey factors) rounds state transcript) remaining exposed cache history)) :
    SecurityIndexTrace.Conflict result.history.indexTrace ∨ NonceHit factors.2.1 result.history := by
  obtain ⟨transcript, forgery, remaining, exposed, cache, history, ready, coherent, tracked, member⟩ :=
    interact_atChecker factors adversary rounds state transcript remaining exposed cache history ready coherent tracked
      result outcome output won member
  exact checker_bad factors transcript forgery remaining exposed cache history ready coherent tracked
    result outcome output won member

/-- Concrete deterministic winning-outcome bridge for the common passive
simulation. Setup, all honest responses, and final verification are actual code.
Only the already-recorded index conflict or prereveal nonce hit can remain once
the actual graph-contact flag is false. -/
theorem run_winning_bad (factors : Factors) (publicCache : Cache)
    (adversary : Adversary submission.sizes) (rounds budget : Nat)
    (result : Outcome (Result SecurityExperiment.Result)) (outcome : SecurityExperiment.Result)
    (member : result ∈ support (run factors.1 ∅
      (start factors.2.1 factors.2.2
        (ofInteract adversary (publicKey factors) rounds (adversary.initial (publicKey factors) publicCache) {}) budget)))
    (clean : result.bad = false) (output : result.value.value = some outcome) (won : outcome.won = true) :
    SecurityIndexTrace.Conflict result.value.history.indexTrace ∨ NonceHit factors.2.1 result.value.history := by
  have stoppedMember : some result.value ∈ support (stopped factors.1 ∅
      (start factors.2.1 factors.2.2
        (ofInteract adversary (publicKey factors) rounds (adversary.initial (publicKey factors) publicCache) {}) budget)) := by
    apply (mem_support_iff_of_evalSPMF_eq (stopped_eq factors.1 ∅ _) (some result.value)).mpr
    rw [support_map]
    exact ⟨result, member, by simp only [keep, clean, Bool.false_eq_true, if_false]⟩
  rw [start] at stoppedMember
  by_cases enough : 739 ≤ budget
  · rw [if_pos enough, SecurityGraphMonitorSetup.setup, SecurityGraphMonitorMetadata.stopped_disclose] at stoppedMember
    have executed := (mem_support_iff_of_evalSPMF_eq
      (stopped_compile factors _ (budget - 739) _ ∅ _ (setup_ready factors))
      (some result.value)).mp stoppedMember
    exact interaction_bad factors adversary rounds _ {} (budget - 739) _ ∅ _ (setup_ready factors)
      (coherent_empty factors) (tracked_empty factors.2.1).keygen
      result.value outcome output won executed
  · simp only [if_neg enough, stopped, support_pure, Set.mem_singleton_iff, Option.some.injEq] at stoppedMember
    rw [stoppedMember] at output
    cases output

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorWin.run_winning_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_winning_bad
end SigGolfCandidate.Hypertree.SecurityMonitorWin
