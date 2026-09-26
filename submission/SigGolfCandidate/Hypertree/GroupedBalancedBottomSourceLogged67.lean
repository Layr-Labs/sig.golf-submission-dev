import SigGolfCandidate.Hypertree.GroupedBalancedGraphAcceptedExtraction67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTrace67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphBottomSourceInputHit67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedBottomSourceLogged67. -/
section
/-! A forged bottom seed at an unsigned index is the hidden canonical input
to the verifier's tag-two bottom-leaf query. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphBottomSourceInputHit67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedSecurityGraph67
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorAuthorization67
open GroupedBalancedGraphMonitorPredecessor67
open GroupedBalancedGraphMonitorPublicCoupling67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem predecessor_bottom (index : BitVec 160) :
    predecessor (bottomLeaf index).val = some (.inr (.inl index)) := by
  simp [predecessor, bottomLeaf]
  have treeBound := GroupedBottomIndex.index_fits_tree_field index
  norm_num at treeBound
  simp [Nat.mod_eq_of_lt treeBound]

theorem bottom_source_inputHit
    (table : PointTable) (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (bottomMatch : ∀ index,
      (GroupedBalancedGraphReference67.sourceAnswers residual secretKey).bottom index =
        (GroupedBalancedGraphMonitorTable67.privateOf table).bottom index)
    (signedBottom : Finset (BitVec 160))
    (exposed : QueryCache PointSpec)
    (safe : GroupedBalancedGraphMonitorInvariant67.ExposedSafe
      (GroupedBalancedGraphMonitorTable67.labelsOf table)
      signedBottom exposed)
    (index : BitVec 160) (unsigned : index ∉ signedBottom)
    (seed : Reference.Digest)
    (seedEq : seed = GroupedBottomTree.secret
      (GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels) secretKey index.toNat) :
    ∃ query, inputHit table exposed query := by
  let position := bottomLeaf index
  let point : Point := .inr (.inl index)
  have previous : predecessor position.val = some point :=
    predecessor_bottom index
  have unauthorized : ¬Authorized
      (GroupedBalancedGraphMonitorTable67.labelsOf table)
      signedBottom point := unsigned
  have hidden : exposed point = none :=
    safe.hidden _ _ exposed point unauthorized
  have sourceEq : GroupedBottomTree.secret
      (GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels) secretKey index.toNat =
      GroupedBottomTree.secret residual secretKey index.toNat :=
    GroupedBalancedGraphProgrammedReference67.programmed_bottom_secret
      residual secretKey labels index
  have seedTable : seed = truncate (table point) := by
    rw [seedEq, sourceEq]
    rw [← GroupedBalancedGraphReference67.bottom_source_value]
    rw [bottomMatch index]
    rfl
  let query := position.input (bytes seed)
  have canonical : query =
      GroupedBalancedGraphCausality67.graphInput
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        (GroupedBalancedGraphMonitorTable67.labelsOf table) position := by
    have chainPayload :=
      GroupedBalancedGraphMonitorPredecessor67.chain_payload_eq table position.val
    rw [previous] at chainPayload
    dsimp only [query]
    rw [seedTable]
    simp only [GroupedBalancedGraphCausality67.graphInput]
    have tagTwo : position.val.tag.val = 2 := by rfl
    rw [GroupedBalancedGraphPayload67.payload, if_pos tagTwo]
    exact congrArg position.input chainPayload.symm
  refine ⟨query, ?_⟩
  have located : GroupedBalancedGraphQuery67.locate query = some position :=
    GroupedBalancedGraphQuery67.locate_address position _
  have tagTwo : position.val.tag.val = 2 := by rfl
  simp only [inputHit, located, tagTwo, if_pos, previous]
  exact ⟨hidden, canonical⟩

end SigGolfCandidate.Hypertree.GroupedBalancedGraphBottomSourceInputHit67

end

/-! The unsigned bottom-source exposure is the exact tag-two verifier read.
Its monitor input contact is attached to a query in the deterministic final
verification trace, rather than an arbitrary existential query. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedBottomSourceLogged67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedSecurityGraph67
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorAuthorization67
open GroupedBalancedGraphMonitorPredecessor67
open GroupedBalancedGraphMonitorPublicCoupling67
open GroupedBalancedGraphProgrammedReference67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem bottom_source_logged
    (table : PointTable) (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (bottomMatch : ∀ index,
      (GroupedBalancedGraphReference67.sourceAnswers residual secretKey).bottom index =
        (GroupedBalancedGraphMonitorTable67.privateOf table).bottom index)
    (signedBottom : Finset (BitVec 160))
    (exposed : QueryCache PointSpec)
    (safe : GroupedBalancedGraphMonitorInvariant67.ExposedSafe
      (GroupedBalancedGraphMonitorTable67.labelsOf table)
      signedBottom exposed)
    (pk : PublicKey) (message : Message)
    (signature : GroupedBalancedScheme67.Signature)
    (index : BitVec 160)
    (indexEq : Reference.indexOf
      (programmedGrouped residual secretKey labels)
      message signature.randomizer = index)
    (unsigned : index ∉ signedBottom)
    (seedEq : signature.bottom.seedValue = GroupedBottomTree.secret
      (programmedGrouped residual secretKey labels)
      secretKey index.toNat) :
    ∃ query,
      inputHit table exposed query ∧
      query ∈ SecurityVerifyTrace.queries
        (programmedGrouped residual secretKey labels)
        (GroupedBalancedVerifyOracle67.verify pk message signature) := by
  let hash := programmedGrouped residual secretKey labels
  let position := bottomLeaf index
  let point : Point := .inr (.inl index)
  let query := position.input (bytes signature.bottom.seedValue)
  have previous : predecessor position.val = some point :=
    GroupedBalancedGraphBottomSourceInputHit67.predecessor_bottom index
  have hidden : exposed point = none :=
    safe.hidden _ _ exposed point unsigned
  have sourceEq : GroupedBottomTree.secret hash secretKey index.toNat =
      GroupedBottomTree.secret residual secretKey index.toNat :=
    GroupedBalancedGraphProgrammedReference67.programmed_bottom_secret
      residual secretKey labels index
  have seedTable : signature.bottom.seedValue = truncate (table point) := by
    rw [seedEq, sourceEq]
    rw [← GroupedBalancedGraphReference67.bottom_source_value]
    rw [bottomMatch index]
    rfl
  have canonical : query =
      GroupedBalancedGraphCausality67.graphInput
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        (GroupedBalancedGraphMonitorTable67.labelsOf table) position := by
    have chainPayload :=
      GroupedBalancedGraphMonitorPredecessor67.chain_payload_eq table position.val
    rw [previous] at chainPayload
    dsimp only [query]
    rw [seedTable]
    simp only [GroupedBalancedGraphCausality67.graphInput]
    have tagTwo : position.val.tag.val = 2 := rfl
    rw [GroupedBalancedGraphPayload67.payload, if_pos tagTwo]
    exact congrArg position.input chainPayload.symm
  have located : GroupedBalancedGraphQuery67.locate query = some position :=
    GroupedBalancedGraphQuery67.locate_address position _
  have hit : inputHit table exposed query := by
    have tagTwo : position.val.tag.val = 2 := rfl
    simp only [inputHit, located, tagTwo, if_pos, previous]
    exact ⟨hidden, canonical⟩
  have leafMember :=
    GroupedBalancedVerifyTrace67.mem_recoverBottom_leaf hash 10
      (GroupedMixedIndex.bottomTree index) index.toNat signature.bottom
  have selected : GroupedBottomTree.selectedLeafAddress 10
      (GroupedMixedIndex.bottomTree index) index.toNat = index.toNat := by
    simpa only [GroupedMixedIndex.bottomTree] using
      GroupedBottomTree.selectedLeafAddress_index 10 index.toNat
  have bottomMember : query ∈ SecurityVerifyTrace.queries hash
      (GroupedBalancedVerifyOracle67.recoverBottom 10
        (GroupedMixedIndex.bottomTree index) index.toNat signature.bottom) := by
    simpa only [query, position, selected,
      GroupedBalancedSecurityGraph67.bottom_leaf_input] using leafMember
  refine ⟨query, hit, ?_⟩
  have indexEq' : Reference.indexOf hash message signature.randomizer =
      index := indexEq
  have verified := GroupedBalancedVerifyTrace67.mem_verify_bottom hash pk
    message signature query (by simpa only [indexEq'] using bottomMember)
  exact verified

end SigGolfCandidate.Hypertree.GroupedBalancedBottomSourceLogged67
