import SigGolfCandidate.Hypertree.GroupedBalancedStrongExtraction67
import SigGolfCandidate.Hypertree.SecurityMonitorIndexContact
import SigGolfCandidate.Hypertree.GroupedBalancedForgeryLogged67


/-! Distinct H5 input pairs that reuse a signed index trigger the input-labelled
index monitor or reveal the signer randomizer before its first disclosure. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPairReuseContact67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open SecurityRandomOracle SecurityMonitorIndexState SecurityMonitorIndexContact
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem pair_reuse_contact (hash : Hash) (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (history : History)
    (draws : List SecurityMonitorIndexContact.Draw)
    (tracked : SecurityMonitorIndexContact.Provenance
      (fun m => Reference.randomizer hash secretKey m) cache history draws)
    (agree : cache.AgreesWithFn hash)
    (responses : GroupedBalancedStrongExtraction67.History)
    (honest : GroupedBalancedStrongExtraction67.HonestHistory
      hash secretKey responses)
    (signed : ∀ entry ∈ responses, entry.1 ∈ history.signedMessages)
    (message : Message) (signature : GroupedBalancedScheme67.Signature)
    (present : cache (indexInput message signature.randomizer) ≠ none)
    (reuse : GroupedBalancedStrongExtraction67.PairReuse
      hash responses message signature) :
    SecurityIndexTrace.Conflict history.indexTrace ∨
      SecurityMonitorIndexContact.NonceHit
        (fun m => Reference.randomizer hash secretKey m) history := by
  obtain ⟨entry, member, different, sameIndex⟩ := reuse
  have nonce : entry.2.randomizer =
      Reference.randomizer hash secretKey entry.1 := by
    have honestSignature := honest entry member
    exact congrArg GroupedBalancedScheme67.Signature.randomizer honestSignature
  have distinct :
      indexInput entry.1 (Reference.randomizer hash secretKey entry.1) ≠
        indexInput message signature.randomizer := by
    intro equal
    have equalPairs :
        (entry.1, Reference.randomizer hash secretKey entry.1) =
          (message, signature.randomizer) :=
      SecurityForgery.indexInput_pair_injective equal
    exact different (by simpa only [nonce] using equalPairs)
  have same :
      (hash (indexInput entry.1
        (Reference.randomizer hash secretKey entry.1))).extractLsb' 0 160 =
      (hash (indexInput message signature.randomizer)).extractLsb' 0 160 := by
    simpa only [Reference.indexOf, SecurityRandomOracle.query_eq,
      SecurityRandomOracle.indexInput, nonce] using sameIndex
  exact SecurityMonitorIndexContact.index_reuse_contact tracked hash agree
    entry.1 message signature.randomizer (signed entry member) present
    distinct same

#print axioms pair_reuse_contact

end SigGolfCandidate.Hypertree.GroupedBalancedPairReuseContact67


/-! The direct67 accepted-forgery split with the strong-EUF H5 reuse case
discharged by input-labelled index provenance. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedForgeryIndexContact67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedGraphProgrammedReference67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem accepted_fresh_contact_or_index_event
    (table : GroupedBalancedGraphPassive67.PointTable)
    (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (labelsMatch : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
    (bottomMatch : ∀ index,
      (GroupedBalancedGraphReference67.sourceAnswers residual secretKey).bottom index =
        (GroupedBalancedGraphMonitorTable67.privateOf table).bottom index)
    (sourceMatch : ∀ base leaf chain,
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        base leaf chain =
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        base leaf chain)
    (signedBottom : Finset (BitVec 160))
    (exposed : QueryCache GroupedBalancedGraphPassive67.PointSpec)
    (safe : GroupedBalancedGraphMonitorInvariant67.ExposedSafe
      (GroupedBalancedGraphMonitorTable67.labelsOf table)
      signedBottom exposed)
    (responses : GroupedBalancedStrongExtraction67.History)
    (honest : GroupedBalancedStrongExtraction67.HonestHistory
      (programmedGrouped residual secretKey labels) secretKey responses)
    (indicesExact : ∀ index,
      index ∈ signedBottom ↔
        ∃ entry ∈ responses,
          Reference.indexOf (programmedGrouped residual secretKey labels)
            entry.1 entry.2.randomizer = index)
    (h5cache : QueryCache HashSpec)
    (h5history : SecurityMonitorIndexState.History)
    (draws : List SecurityMonitorIndexContact.Draw)
    (tracked : SecurityMonitorIndexContact.Provenance
      (fun m => Reference.randomizer
        (programmedGrouped residual secretKey labels) secretKey m)
      h5cache h5history draws)
    (cacheAgrees : h5cache.AgreesWithFn
      (programmedGrouped residual secretKey labels))
    (signedMessages : ∀ entry ∈ responses,
      entry.1 ∈ h5history.signedMessages)
    (pk : PublicKey) (message : Message)
    (signature : GroupedBalancedScheme67.Signature)
    (accepted : GroupedBalancedScheme67.verify
      (programmedGrouped residual secretKey labels)
      (GroupedBalancedScheme67.keygen
        (programmedGrouped residual secretKey labels) secretKey)
      message signature)
    (fresh : (message, signature) ∉ responses)
    (present : h5cache
      (SecurityRandomOracle.indexInput message signature.randomizer) ≠ none) :
    (∃ query,
      GroupedBalancedGraphMonitorPublicCoupling67.outputHit table query
        ((programmedGrouped residual secretKey labels) query) ∧
      query ∈ SecurityVerifyTrace.queries
        (programmedGrouped residual secretKey labels)
        (GroupedBalancedVerifyOracle67.verify pk message signature)) ∨
    (∃ query,
      GroupedBalancedGraphMonitorPublicCoupling67.inputHit table exposed query ∧
      query ∈ SecurityVerifyTrace.queries
        (programmedGrouped residual secretKey labels)
        (GroupedBalancedVerifyOracle67.verify pk message signature)) ∨
    SecurityIndexTrace.Conflict h5history.indexTrace ∨
    SecurityMonitorIndexContact.NonceHit
      (fun m => Reference.randomizer
        (programmedGrouped residual secretKey labels) secretKey m)
      h5history := by
  rcases GroupedBalancedForgeryLogged67.accepted_fresh_logged_or_reuse
    table residual secretKey labels labelsMatch bottomMatch sourceMatch
    signedBottom exposed safe responses honest indicesExact pk message
    signature accepted fresh with output | input | reuse
  · exact Or.inl output
  · exact Or.inr (Or.inl input)
  · rcases GroupedBalancedPairReuseContact67.pair_reuse_contact
      (programmedGrouped residual secretKey labels) secretKey
      h5cache h5history draws tracked cacheAgrees responses honest
      signedMessages message signature present reuse with conflict | nonce
    · exact Or.inr (Or.inr (Or.inl conflict))
    · exact Or.inr (Or.inr (Or.inr nonce))

#print axioms accepted_fresh_contact_or_index_event

end SigGolfCandidate.Hypertree.GroupedBalancedForgeryIndexContact67
