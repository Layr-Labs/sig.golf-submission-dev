import SigGolfCandidate.Hypertree.GroupedBalancedSecurityJointTable67
import SigGolfCandidate.Hypertree.GroupedBalancedPlantedCache67
import SigGolfCandidate.Hypertree.GroupedBalancedPrivateLegacyEligible67

/-! Erasing the source-only private cache changes an adaptive continuation only
if it publicly queries a bottom or upper H1 input. Honest randomizer inputs
remain lazy on both sides. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecuritySourceHybrid67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference SecurityCache
open GroupedBalancedPrivateDerivation67 GroupedBalancedPrivateFactors67
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphSampling67
open GroupedBalancedGraphOrder67 GroupedBalancedSecurityJointPresample67
open GroupedBalancedSecurityJointTable67
open scoped Classical

def SourceHit (secretKey : SecretKey) (query : Query) : Prop :=
  ∃ slot : Slot, IsSource slot ∧ input secretKey slot = query

theorem source_cache_agree_empty (secretKey : SecretKey)
    (answers : PrivateTable) :
    AgreeOutside (SourceHit secretKey)
      (sourceCache secretKey answers) ∅ := by
  intro query noHit
  rw [source_cache_other secretKey answers query]
  · rfl
  · intro slot source same
    exact noHit ⟨slot, source, same.symm⟩

/-- Every source-cache discrepancy is in the secret-key query class already
charged by the organizer's shared query meter. -/
theorem source_hit_legacy_eligible (secretKey : SecretKey)
    (query : Query) (hit : SourceHit secretKey query) :
    SecuritySeparation.SecretKeyEligible query := by
  obtain ⟨slot, _, same⟩ := hit
  rw [← same]
  exact GroupedBalancedPrivateLegacyEligible67.eligible_of_direct
    secretKey slot

theorem source_hit_public_secretKey (secretKey : SecretKey)
    (query : Query) (hit : SourceHit secretKey query) :
    SecuritySeparation.publicSecretKeyHit secretKey (.inr query) := by
  obtain ⟨slot, source, same⟩ := hit
  apply (SecuritySeparation.publicSecretKeyHit_iff secretKey query).mpr
  cases slot with
  | bottom index =>
      refine ⟨.chain ⟨0, BitVec.ofNat 192 index.toNat, false, 0⟩, ?_⟩
      exact (GroupedBalancedPrivateLegacyEligible67.bottom_legacy_input
        secretKey index).symm.trans same
  | upper base leaf pair =>
      refine ⟨.chain ⟨GroupedBalancedPrivateDerivation67.baseLevel base,
        BitVec.ofNat 192 leaf.toNat, false,
        ⟨pair.val, by have := pair.isLt; omega⟩⟩, ?_⟩
      exact (GroupedBalancedPrivateLegacyEligible67.upper_legacy_input
        secretKey base leaf pair).symm.trans same
  | randomizer _ => cases source

theorem source_hit_secretKeyAt (secretKey : SecretKey)
    (query : Query) (hit : SourceHit secretKey query) :
    SecuritySecretKey.SecretKeyAt query secretKey :=
  (source_hit_public_secretKey secretKey query hit).2

theorem source_hit_in_trace (secretKey : SecretKey)
    (inputs : List Query) (query : Query)
    (member : query ∈ inputs) (hit : SourceHit secretKey query) :
    SecuritySecretKey.SecretKeyHitTrace inputs secretKey :=
  ⟨query,member,source_hit_secretKeyAt secretKey query hit⟩

theorem graph_cache_agree (bad : Query → Prop)
    (privateAnswers : GroupedBalancedGraphPayload67.PrivateAnswers)
    (positions : List Position) (labels : Labels)
    (left right : QueryCache HashSpec)
    (agree : AgreeOutside bad left right) :
    AgreeOutside bad
      (graphCache privateAnswers positions labels left)
      (graphCache privateAnswers positions labels right) := by
  induction positions generalizing left right with
  | nil => exact agree
  | cons position rest ih =>
      simp only [graphCache]
      exact ih _ _ (agree.cacheQuery _ _)

noncomputable def jointCache (secretKey : SecretKey)
    (answers : PrivateTable) (labels : Labels) : QueryCache HashSpec :=
  graphCache (privateOfAnswers answers) positions labels
    (sourceCache secretKey answers)

theorem joint_source_lookup (secretKey : SecretKey)
    (answers : PrivateTable) (labels : Labels)
    (slot : Slot) (source : IsSource slot) :
    jointCache secretKey answers labels (input secretKey slot) =
      some (answers slot) := by
  unfold jointCache
  rw [GroupedBalancedGraphQuery67.graphCache_outside]
  · exact source_cache_lookup secretKey answers slot source
  · intro position _
    exact GroupedBalancedPrivateGraphDisjoint67.input_ne_public_graph
      secretKey slot position _

noncomputable def plantedCache (answers : PrivateTable)
    (labels : Labels) (ghosts : GroupedBalancedGlobalPaired67.GhostTable) :
    QueryCache HashSpec :=
  GroupedBalancedPlantedCache67.planted (tableOf answers labels ghosts)

theorem joint_planted_agree (secretKey : SecretKey)
    (answers : PrivateTable) (labels : Labels)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable) :
    AgreeOutside (SourceHit secretKey)
      (jointCache secretKey answers labels)
      (plantedCache answers labels ghosts) := by
  unfold jointCache plantedCache GroupedBalancedPlantedCache67.planted
    GroupedBalancedGraphOracle67.embed
  rw [labelsOf_tableOf, ← graph_cache_tableOf]
  exact graph_cache_agree (SourceHit secretKey)
    (privateOfAnswers answers) positions labels
    (sourceCache secretKey answers) ∅
    (source_cache_agree_empty secretKey answers)

/-- Exact source-cache replacement inequality for an arbitrary adaptive World
program. Any counter stored in its output is preserved. The only additive
event is its first public H1-source input query. -/
theorem source_hybrid {α : Type} (secretKey : SecretKey)
    (answers : PrivateTable) (labels : Labels)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable)
    (program : OracleComp World α) (event : α → Prop) :
    Pr[event | SecurityGraphHidden.observe program
      (jointCache secretKey answers labels)] ≤
    Pr[event | SecurityGraphHidden.observe program
      (plantedCache answers labels ghosts)] +
    Pr[= none | SecurityGraphHidden.observe
      (stopBefore (SourceHit secretKey) program)
      (plantedCache answers labels ghosts)] := by
  exact SecurityCache.prob_cache_change_le (SourceHit secretKey) program
    (jointCache secretKey answers labels)
    (plantedCache answers labels ghosts)
    (joint_planted_agree secretKey answers labels ghosts) event

#print axioms joint_planted_agree
#print axioms source_hybrid
#print axioms source_hit_public_secretKey
#print axioms source_hit_in_trace
#print axioms joint_source_lookup

end SigGolfCandidate.Hypertree.GroupedBalancedSecuritySourceHybrid67
