import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledOrganizerTranscript67
import SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerOrganizerRisk67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPairedGlobal67
import SigGolfCandidate.Hypertree.GroupedBalancedOrganizerCoherentChecker67
import SigGolfCandidate.Hypertree.GroupedBalancedResidualCompletion67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphProgrammedTree67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPairedProvenance67
import SigGolfCandidate.Hypertree.GroupedBalancedPairedStoppedFresh67
import SigGolfCandidate.Hypertree.GroupedBalancedStoppedStateSafe67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedCompletionChecker67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedOrganizerWinningExtraction67. -/
section
/-! Specialize the checker extraction to the total hash completed from the
actual final cache and sampled private answers. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedCompletionChecker67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorStop67
open GroupedBalancedGraphMonitorInvariant67
open GroupedBalancedGraphMonitorTable67
open GroupedBalancedGraphProgrammedReference67
open GroupedBalancedResidualCompletion67
open GroupedBalancedVerifierCache67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem completed_forgery_index_risk
    (table : PointTable)
    (answers : SecurityGraphIdeal.PrivateTable)
    (secretKey : SecretKey)
    (signedBottom : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (initial : Safe table signedBottom exposed cache)
    (responses : GroupedBalancedStrongExtraction67.History)
    (pk : PublicKey) (message : Message)
    (signature : GroupedBalancedScheme67.Signature)
    (result : Result Bool)
    (member : some result ∈ support
      (stopped table exposed
        (compile (GroupedBalancedVerifyOracle67.verify
          pk message signature) exposed cache)))
    (privateFresh : ∀ slot : GroupedBalancedPrivateDerivation67.Slot,
      result.2.2
        (GroupedBalancedPrivateDerivation67.input secretKey slot) = none)
    (honest : GroupedBalancedStrongExtraction67.HonestHistory
      (programmedGrouped
        (completion table answers secretKey result.2.2)
        secretKey (labelsOf table)) secretKey responses)
    (indicesExact : ∀ index,
      index ∈ signedBottom ↔
        ∃ entry ∈ responses,
          Reference.indexOf
            (programmedGrouped
              (completion table answers secretKey result.2.2)
              secretKey (labelsOf table))
            entry.1 entry.2.randomizer = index)
    (h5history : SecurityMonitorIndexState.History)
    (draws : List SecurityMonitorIndexContact.Draw)
    (tracked : SecurityMonitorIndexContact.Provenance
      (fun m => answers (.randomizer m))
      result.2.2 h5history draws)
    (signedMessages : ∀ entry ∈ responses,
      entry.1 ∈ h5history.signedMessages)
    (pkEq : pk = truncate
      ((labelsOf table)
        (GroupedBalancedSecurityGraph67.upperNode ⟨149, by decide⟩ 0)))
    (won : result.1 = true)
    (fresh : (message, signature) ∉ responses) :
    SecurityIndexTrace.Conflict h5history.indexTrace ∨
      SecurityMonitorIndexContact.NonceHit
        (fun m => answers (.randomizer m)) h5history := by
  let base := completion table answers secretKey result.2.2
  let hash := programmedGrouped base secretKey (labelsOf table)
  have nonceEq :
      (fun m => Reference.randomizer hash secretKey m) =
        (fun m => answers (.randomizer m)) := by
    funext m
    change Reference.randomizer
      (programmedGrouped base secretKey (labelsOf table))
      secretKey m = answers (.randomizer m)
    rw [programmed_randomizer]
    exact completion_randomizer table answers secretKey result.2.2 m
  have key : pk = GroupedBalancedScheme67.keygen hash secretKey := by
    rw [pkEq]
    exact (GroupedBalancedGraphProgrammedTree67.programmed_keygen
      base secretKey (labelsOf table)).symm
  have trackedHash : SecurityMonitorIndexContact.Provenance
      (fun m => Reference.randomizer hash secretKey m)
      result.2.2 h5history draws := by
    rw [nonceEq]
    exact tracked
  have risk := GroupedBalancedVerifierForgeryElim67.completed_forgery_index_risk
    table base secretKey (labelsOf table) rfl
    (completion_bottom table answers secretKey result.2.2)
    (completion_upper table answers secretKey result.2.2)
    signedBottom exposed cache initial responses honest indicesExact
    h5history draws pk message signature result member
    (completion_agrees table answers secretKey result.2.2 privateFresh)
    trackedHash
    signedMessages key won fresh
  rw [nonceEq] at risk
  exact risk

#print axioms completed_forgery_index_risk

end SigGolfCandidate.Hypertree.GroupedBalancedCompletionChecker67
end

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledOrganizerGlobalCoverage67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedOrganizerWinningExtraction67. -/
section
/-! The actual paired organizer experiment retains every signed response
message in the same audit used by the H5 nonce and provenance bounds. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledOrganizerGlobalCoverage67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledJoint67
open GroupedBalancedIndexLabeledOrganizerTranscript67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false

theorem paired_organizer_covers (sizes : Sizes)
    (encode : GroupedBalancedScheme67.Signature → Bytes sizes.signature)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (adversary : SigGolf.Adversary sizes)
    (publicCache : Cache) (rounds budget : Nat)
    (result : SecurityGraphIdeal.PrivateTable ×
      ((GroupedBalancedGraphIndexJoint67.JointOutcome
        ((Option (GroupedBalancedGraphOrganizerView67.Result sizes) ×
          List Action) × Nat) × List Draw) × Audit))
    (member : result ∈ support
      (GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
        (GroupedBalancedPlantedEagerOrganizerRisk67.organizerInteraction
          sizes encode decodeWitness decodeSignature adversary publicCache
          rounds) budget))
    (outcome : GroupedBalancedGraphOrganizerView67.Result sizes)
    (trace : List Action) (secretOut : Nat)
    (returned : result.2.1.1.value.value =
      some ((some outcome, trace), secretOut)) :
    Covers sizes outcome.transcript result.2.2 := by
  unfold GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
    at member
  simp only [mem_support_bind_iff] at member
  obtain ⟨answers, _, member⟩ := member
  obtain ⟨auditResult, auditMember, same⟩ := member
  simp only [support_pure, Set.mem_singleton_iff] at same
  subst result
  rw [GroupedBalancedIndexLabeledGlobal67.global,
    GroupedBalancedIndexLabeledAuditLift67.run_unmarked,
    mem_support_bind_iff] at auditMember
  obtain ⟨table, _, child⟩ := auditMember
  let cache := GroupedBalancedGraphMonitorSetup67.cache table
  let pk := GroupedBalancedGraphMonitorSetupBound67.rootFrom cache
  have child' : auditResult ∈ support (run
      (compile table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          (GroupedBalancedIdealEagerCutoff67.eagerCutoffView
            answers cache
            (GroupedBalancedGraphOrganizerView67.ofInteract sizes
              encode decodeWitness decodeSignature adversary pk rounds
              (adversary.initial pk publicCache) {}) budget) 0)
        budget
        (GroupedBalancedGraphMonitorSignBound67.initial cache)
        0 ∅ false 0) {}) := by
    simpa only [GroupedBalancedIndexLabeledJoint67.start,
      GroupedBalancedPlantedEagerGraphProjection67.viewOf,
      GroupedBalancedPlantedEagerOrganizerRisk67.organizerInteraction,
      cache, pk] using child
  exact completed_covers sizes encode decodeWitness decodeSignature
    answers cache table pk adversary rounds
    (adversary.initial pk publicCache) {} budget 0 budget
    (GroupedBalancedGraphMonitorSignBound67.initial cache) 0 ∅ false 0
    {} (Covers.empty sizes {}) auditResult outcome trace secretOut
    child' returned

#print axioms paired_organizer_covers

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledOrganizerGlobalCoverage67

end

/-! A completed clean organizer win is an H5 index conflict or an earlier
guess of the honest signer randomizer. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedOrganizerWinningExtraction67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphMonitorSignCoupling67
open GroupedBalancedGraphMonitorInvariant67
open GroupedBalancedGraphOrganizerView67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedIdealEagerCutoff67
open GroupedBalancedIndexLabeledOrganizerTranscript67
open GroupedBalancedIndexLabeledHistory67
open GroupedBalancedResidualCompletion67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

abbrev sizes : Sizes := GroupedBalancedWireTranscript67.sizes

theorem completed_winning_risk
    (answers : SecurityGraphIdeal.PrivateTable)
    (table : PointTable) (secretKey : SecretKey)
    (adversary : SigGolf.Adversary sizes)
    (publicCache : Cache) (rounds budget : Nat)
    (outcome : Result sizes) (trace : List Action)
    (left : Nat) (final : State)
    (audit : GroupedBalancedIndexLabeledAudit67.Audit)
    (draws : List GroupedBalancedIndexLabeledProgram67.Draw)
    (member : some (some (some outcome, trace), left, final) ∈ support
      (execute table
        (eagerCutoffView answers (GroupedBalancedGraphMonitorSetup67.cache table)
          (ofInteract sizes GroupedBalancedWire67.wire
            GroupedBalancedWire67.decode GroupedBalancedWire67.decode
            adversary
            (GroupedBalancedGraphMonitorSetupBound67.rootFrom
              (GroupedBalancedGraphMonitorSetup67.cache table))
            rounds
            (adversary.initial
              (GroupedBalancedGraphMonitorSetupBound67.rootFrom
                (GroupedBalancedGraphMonitorSetup67.cache table))
              publicCache) {}) budget)
        budget
        (GroupedBalancedGraphMonitorSignBound67.initial
          (GroupedBalancedGraphMonitorSetup67.cache table))))
    (safe : Safe table final.signedBottom final.exposed final.residual)
    (privateFresh : ∀ slot : GroupedBalancedPrivateDerivation67.Slot,
      final.residual
        (GroupedBalancedPrivateDerivation67.input secretKey slot) = none)
    (tracked : SecurityMonitorIndexContact.Provenance
      (fun m => answers (.randomizer m)) final.residual
      (history audit draws) draws)
    (covered : Covers sizes outcome.transcript audit)
    (won : outcome.won = true) :
    SecurityIndexTrace.Conflict (draws.map Prod.snd) ∨
      SecurityMonitorIndexContact.NonceHit
        (fun m => answers (.randomizer m)) (history audit draws) := by
  let cache := GroupedBalancedGraphMonitorSetup67.cache table
  let pk := GroupedBalancedGraphMonitorSetupBound67.rootFrom cache
  let base := completion table answers secretKey final.residual
  let hash := GroupedBalancedGraphProgrammedReference67.programmedGrouped
    base secretKey (GroupedBalancedGraphMonitorTable67.labelsOf table)
  have initialSafe : Safe table
      (GroupedBalancedGraphMonitorSignBound67.initial cache).signedBottom
      (GroupedBalancedGraphMonitorSignBound67.initial cache).exposed
      (GroupedBalancedGraphMonitorSignBound67.initial cache).residual := by
    simpa only [cache, GroupedBalancedGraphMonitorSignBound67.initial] using
      (GroupedBalancedGraphMonitorSetup67.cache_safe table)
  have hashEq : hash = GroupedBalancedVerifierReplay67.programmed table base :=
    GroupedBalancedVerifierProgrammedBridge67.programmed_eq table base
      secretKey (GroupedBalancedGraphMonitorTable67.labelsOf table) rfl
      (completion_bottom table answers secretKey final.residual)
      (completion_upper table answers secretKey final.residual)
  have finalAgree : final.residual.AgreesWithFn hash := by
    rw [hashEq]
    exact GroupedBalancedVerifierProgrammedBridge67.cache_agrees_programmed
      table final.residual base safe.2.2
      (completion_agrees table answers secretKey final.residual privateFresh)
  have signLaw : GroupedBalancedOrganizerCoherence67.SignLaw
      hash secretKey answers table cache :=
    GroupedBalancedOrganizerCoherence67.completion_signLaw
      table answers secretKey final.residual
  have coherent : GroupedBalancedOrganizerCoherence67.Coherent
      hash secretKey (GroupedBalancedGraphMonitorSignBound67.initial cache)
      {} := by
    exact GroupedBalancedOrganizerCoherence67.empty hash secretKey _ rfl
  obtain ⟨signedTranscript, forgery, checkBudget, checkRemaining,
      checkState, prefixLog, checkTrace, traceEq, checkSafe,
      checkCoherent, checkMember⟩ :=
    GroupedBalancedOrganizerCoherentChecker67.winning_at_checker
      hash secretKey answers table cache pk adversary rounds
      (adversary.initial pk publicCache) {} budget budget
      (GroupedBalancedGraphMonitorSignBound67.initial cache) final
      initialSafe coherent finalAgree signLaw outcome trace left member won
  obtain ⟨message, signature, candidateEq, transcriptEq, fresh,
      checked, signedEq⟩ :=
    GroupedBalancedOrganizerCheckBridge67.completed_winning_check
      answers table cache pk signedTranscript forgery checkBudget
      checkRemaining checkState final checkSafe outcome checkTrace left
      checkMember won
  have signedMessages : ∀ entry ∈
      GroupedBalancedWireTranscript67.responses signedTranscript,
      entry.1 ∈ (history audit draws).signedMessages := by
    intro entry present
    obtain ⟨wireEntry, wireMember, entryEq⟩ := List.mem_map.mp present
    have coveredEntry : wireEntry.1 ∈ audit.signedMessages := by
      apply covered wireEntry
      rw [transcriptEq]
      exact wireMember
    simpa only [history, ← entryEq] using coveredEntry
  have indicesExact : ∀ index,
      index ∈ final.signedBottom ↔
        ∃ entry ∈ GroupedBalancedWireTranscript67.responses signedTranscript,
          Reference.indexOf hash entry.1 entry.2.randomizer = index := by
    intro index
    rw [signedEq, checkCoherent.2]
    exact GroupedBalancedTranscriptInvariant67.mem_indices hash _ index
  have key : pk = truncate
      ((GroupedBalancedGraphMonitorTable67.labelsOf table)
        (GroupedBalancedSecurityGraph67.upperNode ⟨149, by decide⟩ 0)) := by
    simp only [pk, cache,
      GroupedBalancedGraphMonitorSetupBound67.rootFrom_cache,
      GroupedBalancedGraphMonitorSetupBound67.rootPublic,
      GroupedBalancedGraphMonitorSetupBound67.rootPoint,
      GroupedBalancedGraphMonitorTable67.labelsOf]
  have finalSignedSafe : Safe table final.signedBottom
      checkState.exposed checkState.residual := by
    rw [signedEq]
    exact checkSafe
  have risk := GroupedBalancedCompletionChecker67.completed_forgery_index_risk
    table answers secretKey final.signedBottom
    checkState.exposed checkState.residual finalSignedSafe
    (GroupedBalancedWireTranscript67.responses signedTranscript)
    pk message signature
    (true, final.exposed, final.residual) checked
    privateFresh checkCoherent.1 indicesExact
    (history audit draws) draws tracked signedMessages key rfl fresh
  simpa only [history] using risk

#print axioms completed_winning_risk

theorem paired_winning_risk
    (adversary : SigGolf.Adversary sizes)
    (publicCache : Cache) (rounds budget : Nat)
    (secretKey : SecretKey)
    (result : GroupedBalancedPairedStoppedFresh67.PairedResult
      (Result sizes))
    (member : result ∈ support
      (GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
        (GroupedBalancedPlantedEagerOrganizerRisk67.organizerInteraction
          sizes GroupedBalancedWire67.wire
          GroupedBalancedWire67.decode GroupedBalancedWire67.decode
          adversary publicCache rounds) budget))
    (clean : result.2.1.1.bad = false)
    (outcome : Result sizes) (trace : List Action) (count : Nat)
    (completed : result.2.1.1.value.value =
      some ((some outcome, trace), count))
    (won : outcome.won = true)
    (noHit : ¬SecuritySecretKey.SecretKeyHitTrace
      (secretInputs trace) secretKey) :
    SecurityIndexTrace.Conflict (result.2.1.2.map Prod.snd) ∨
      SecurityMonitorIndexContact.NonceHit
        (fun m => result.1 (.randomizer m))
        (history result.2.2 result.2.1.2) := by
  let interaction :=
    GroupedBalancedPlantedEagerOrganizerRisk67.organizerInteraction
      sizes GroupedBalancedWire67.wire
      GroupedBalancedWire67.decode GroupedBalancedWire67.decode
      adversary publicCache rounds
  obtain ⟨table, stopped⟩ :=
    GroupedBalancedPairedStoppedFresh67.paired_clean_execute
      interaction budget result member clean
  let cache := GroupedBalancedGraphMonitorSetup67.cache table
  have annotated : some (some ((some outcome, trace), count),
      result.2.1.1.value.remaining,
      result.2.1.1.value.state) ∈ support
      (execute table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          (eagerCutoffView result.1 cache
            (interaction cache) budget) 0)
        budget (GroupedBalancedGraphMonitorSignBound67.initial cache)) := by
    rw [completed] at stopped
    simpa only [GroupedBalancedPlantedEagerGraphProjection67.viewOf,
      cache] using stopped
  have eager : some (some (some outcome, trace),
      result.2.1.1.value.remaining,
      result.2.1.1.value.state) ∈ support
      (execute table
        (eagerCutoffView result.1 cache (interaction cache) budget)
        budget (GroupedBalancedGraphMonitorSignBound67.initial cache)) :=
    GroupedBalancedPairedStoppedFresh67.annotated_completed_eager
      result.1 table cache (interaction cache) budget budget
      (GroupedBalancedGraphMonitorSignBound67.initial cache)
      result.2.1.1.value.state (some outcome) trace count
      result.2.1.1.value.remaining annotated
  have initialSafe : Safe table
      (GroupedBalancedGraphMonitorSignBound67.initial cache).signedBottom
      (GroupedBalancedGraphMonitorSignBound67.initial cache).exposed
      (GroupedBalancedGraphMonitorSignBound67.initial cache).residual := by
    simpa only [cache, GroupedBalancedGraphMonitorSignBound67.initial] using
      (GroupedBalancedGraphMonitorSetup67.cache_safe table)
  have safe : Safe table
      result.2.1.1.value.state.signedBottom
      result.2.1.1.value.state.exposed
      result.2.1.1.value.state.residual :=
    GroupedBalancedStoppedStateSafe67.execute_safe table
      (eagerCutoffView result.1 cache (interaction cache) budget)
      budget (GroupedBalancedGraphMonitorSignBound67.initial cache)
      initialSafe _ eager _ _ _ rfl
  have privateFresh :=
    GroupedBalancedPairedStoppedFresh67.paired_clean_private_fresh
      secretKey interaction budget result (some outcome) trace count
      member clean completed noHit
  have tracked :=
    GroupedBalancedIndexLabeledPairedProvenance67.paired_provenance
      interaction budget result member
  have covered :=
    GroupedBalancedIndexLabeledOrganizerGlobalCoverage67.paired_organizer_covers
      sizes GroupedBalancedWire67.wire
      GroupedBalancedWire67.decode GroupedBalancedWire67.decode
      adversary publicCache rounds budget result member outcome trace count
      completed
  apply completed_winning_risk result.1 table secretKey adversary
    publicCache rounds budget outcome trace result.2.1.1.value.remaining
    result.2.1.1.value.state result.2.2 result.2.1.2
  · simpa only [interaction,
      GroupedBalancedPlantedEagerOrganizerRisk67.organizerInteraction,
      cache] using eager
  · exact safe
  · exact privateFresh
  · exact tracked
  · exact covered
  · exact won

#print axioms paired_winning_risk

end SigGolfCandidate.Hypertree.GroupedBalancedOrganizerWinningExtraction67
