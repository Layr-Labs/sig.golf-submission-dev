import SigGolfCandidate.Hypertree.GroupedBalancedVerifierExposure67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorPairedOracle67
import SigGolfCandidate.Hypertree.GroupedBalancedForgeryIndexContact67


/-! Identify the verifier monitor's programmed public graph with the actual
direct67 scheme hash when its bottom and paired upper sources match the table. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifierProgrammedBridge67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorInvariant67
open GroupedBalancedGraphMonitorTable67
open GroupedBalancedGraphProgrammedReference67
open GroupedBalancedVerifierReplay67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem programmed_eq (table : PointTable)
    (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (labelsMatch : labels = labelsOf table)
    (bottomMatch : ∀ index,
      (GroupedBalancedGraphReference67.sourceAnswers residual secretKey).bottom index =
        (privateOf table).bottom index)
    (sourceMatch : ∀ base leaf chain,
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        base leaf chain =
      GroupedBalancedGraphPayload67.chainSource
        (privateOf table) base leaf chain) :
    programmedGrouped residual secretKey labels =
      programmed table residual := by
  funext query
  rw [GroupedBalancedGraphMonitorPairedOracle67.programmedGrouped_lookup
    residual secretKey labels table labelsMatch bottomMatch sourceMatch query,
    programmed, GroupedBalancedGraphOracle67.programmed_hash]
  rfl

theorem cache_agrees_programmed (table : PointTable)
    (cache : QueryCache HashSpec) (residual : Hash)
    (safe : ResidualSafe table cache)
    (agree : cache.AgreesWithFn residual) :
    cache.AgreesWithFn (programmed table residual) := by
  intro query answer present
  rw [programmed, GroupedBalancedGraphOracle67.programmed_hash]
  cases located : GroupedBalancedGraphQuery67.locate query with
  | none =>
      simp only [GroupedBalancedGraphOracle67.canonical, located]
      exact agree present
  | some position =>
      have different := (safe query answer present position located).1
      simp only [GroupedBalancedGraphOracle67.canonical, located,
        if_neg different]
      exact agree present

#print axioms programmed_eq
#print axioms cache_agrees_programmed

end SigGolfCandidate.Hypertree.GroupedBalancedVerifierProgrammedBridge67


/-! A completed, contact-free direct67 checker eliminates both graph forgery
alternatives. A fresh accepted signature therefore forces an H5 index conflict
or an earlier public guess of the honest signer's randomizer. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifierForgeryElim67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorStop67
open GroupedBalancedGraphMonitorInvariant67
open GroupedBalancedGraphMonitorTable67
open GroupedBalancedGraphProgrammedReference67
open GroupedBalancedVerifierCache67
open GroupedBalancedVerifierReplay67
open GroupedBalancedVerifierExposure67
open GroupedBalancedVerifierProgrammedBridge67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem completed_forgery_index_risk
    (table : PointTable) (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (labelsMatch : labels = labelsOf table)
    (bottomMatch : ∀ index,
      (GroupedBalancedGraphReference67.sourceAnswers residual secretKey).bottom index =
        (privateOf table).bottom index)
    (sourceMatch : ∀ base leaf chain,
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        base leaf chain =
      GroupedBalancedGraphPayload67.chainSource
        (privateOf table) base leaf chain)
    (signedBottom : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (initial : Safe table signedBottom exposed cache)
    (responses : GroupedBalancedStrongExtraction67.History)
    (honest : GroupedBalancedStrongExtraction67.HonestHistory
      (programmedGrouped residual secretKey labels) secretKey responses)
    (indicesExact : ∀ index,
      index ∈ signedBottom ↔
        ∃ entry ∈ responses,
          Reference.indexOf (programmedGrouped residual secretKey labels)
            entry.1 entry.2.randomizer = index)
    (h5history : SecurityMonitorIndexState.History)
    (draws : List SecurityMonitorIndexContact.Draw)
    (pk : PublicKey) (message : Message)
    (signature : GroupedBalancedScheme67.Signature)
    (result : Result Bool)
    (member : some result ∈ support
      (stopped table exposed
        (compile (GroupedBalancedVerifyOracle67.verify
          pk message signature) exposed cache)))
    (agree : result.2.2.AgreesWithFn residual)
    (tracked : SecurityMonitorIndexContact.Provenance
      (fun m => Reference.randomizer
        (programmedGrouped residual secretKey labels) secretKey m)
      result.2.2 h5history draws)
    (signedMessages : ∀ entry ∈ responses,
      entry.1 ∈ h5history.signedMessages)
    (key : pk = GroupedBalancedScheme67.keygen
      (programmedGrouped residual secretKey labels) secretKey)
    (won : result.1 = true)
    (fresh : (message, signature) ∉ responses) :
    SecurityIndexTrace.Conflict h5history.indexTrace ∨
      SecurityMonitorIndexContact.NonceHit
        (fun m => Reference.randomizer
          (programmedGrouped residual secretKey labels) secretKey m)
        h5history := by
  let hash := programmedGrouped residual secretKey labels
  have sameHash : hash = programmed table residual :=
    programmed_eq table residual secretKey labels
      labelsMatch bottomMatch sourceMatch
  have replay := completed_eval table signedBottom
    (GroupedBalancedVerifyOracle67.verify pk message signature)
    exposed cache initial result member residual agree
  have finalSafe := replay.2.2
  have accepted : GroupedBalancedScheme67.verify hash
      (GroupedBalancedScheme67.keygen hash secretKey)
      message signature := by
    have acceptedOracle :
        GroupedBalancedScheme67.verify (programmed table residual)
          pk message signature := by
      apply (GroupedBalancedVerifyOracle67.eval_verify_iff
        (programmed table residual) pk message signature).mp
      exact replay.2.1.trans won
    rw [← sameHash] at acceptedOracle
    rw [← key]
    exact acceptedOracle
  have finalAgree : result.2.2.AgreesWithFn hash := by
    rw [sameHash]
    exact cache_agrees_programmed table result.2.2 residual
      finalSafe.2.2 agree
  have present : result.2.2
      (SecurityRandomOracle.indexInput message signature.randomizer) ≠ none :=
    verifier_index_present table signedBottom pk message signature
      exposed cache initial result member
  rcases GroupedBalancedForgeryIndexContact67.accepted_fresh_contact_or_index_event
      table residual secretKey labels labelsMatch bottomMatch sourceMatch
      signedBottom result.2.1 finalSafe.2.1 responses honest indicesExact
      result.2.2 h5history draws tracked finalAgree signedMessages
      pk message signature accepted fresh present with
    ⟨query, hit, queryMember⟩ |
    ⟨query, hit, queryMember⟩ | conflict | nonce
  · have clean := completed_no_contacts table signedBottom
      (GroupedBalancedVerifyOracle67.verify pk message signature)
      exposed cache initial result member residual agree
    have absent := (clean query (by simpa only [← sameHash] using queryMember)).2
    exact False.elim (absent (by simpa only [← sameHash] using hit))
  · have clean := completed_no_contacts table signedBottom
      (GroupedBalancedVerifyOracle67.verify pk message signature)
      exposed cache initial result member residual agree
    have absent := (clean query (by simpa only [← sameHash] using queryMember)).1
    exact False.elim (absent hit)
  · exact Or.inl conflict
  · exact Or.inr nonce

#print axioms completed_forgery_index_risk

end SigGolfCandidate.Hypertree.GroupedBalancedVerifierForgeryElim67
