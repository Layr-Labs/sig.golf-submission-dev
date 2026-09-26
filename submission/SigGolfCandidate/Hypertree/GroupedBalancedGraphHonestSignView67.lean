import SigGolfCandidate.Hypertree.GroupedBalancedGraphBottomWitnessCache67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSignBound67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphSignerFromCache67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphHonestSignView67. -/
section
/-! Exact signer reconstruction from the setup cache, one freshly disclosed
bottom source, and the residual nonce/index oracle. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphSignerFromCache67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorAuthorization67
open GroupedBalancedGraphUpperLayersCache67
open GroupedBalancedGraphBottomWitnessCache67
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
open scoped Classical

theorem programmed_index (residual : Hash) (secretKey : SecretKey)
    (labels : Labels) (message : Message) (randomizer : Bytes 32) :
    Reference.indexOf
      (GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels) message randomizer =
      Reference.indexOf residual message randomizer := by
  let input := SecurityRandomOracle.addressedInput 5 0 0 0 0 0
    (bytes (0 : Bytes 16) ++ bytes message ++ bytes randomizer)
  have outside : ∀ position : Position,
      input ≠ position.input
        (GroupedBalancedGraphPayload67.payload
          (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
          labels position) := by
    intro position same
    have addressEq : (⟨5, 0, 0, 0, 0, 0⟩ : SecurityGraph.Address) =
        position.val := SecurityGraph.Address.eq_of_input_eq same
    have tags := congrArg
      (fun address : SecurityGraph.Address => address.tag.val) addressEq
    change (5 : Nat) = position.val.tag.val at tags
    rcases position.property with chain | leaf | node <;> omega
  change (GroupedBalancedGraphProgrammedReference67.programmedGrouped
    residual secretKey labels input).extractLsb' 0 160 =
    (residual input).extractLsb' 0 160
  unfold GroupedBalancedGraphProgrammedReference67.programmedGrouped
    GroupedBalancedGraphProgramming67.programmed
    GroupedGraphProgramming.programmed
  split
  next found =>
    obtain ⟨position, same⟩ := found
    exact False.elim (outside position same.symm)
  next absent => rfl

def labelsFrom (cache : QueryCache PointSpec) : Labels :=
  fun position => (cache (.inl position)).getD 0

theorem canonical_from_cache (table : PointTable)
    (base : Fin 150) (leaf : BitVec 160) :
    canonicalMessage
      (labelsFrom (GroupedBalancedGraphMonitorSetup67.cache table)) base leaf =
    canonicalMessage (GroupedBalancedGraphMonitorTable67.labelsOf table)
      base leaf := by
  unfold canonicalMessage
  split_ifs with zero
  · have covered := GroupedBalancedGraphMonitorSetup67.cache_covers table
      (.inl (bottomNode ⟨9, by decide⟩ leaf))
      (GroupedBalancedGraphMonitorSetup67.node_authorized
        (GroupedBalancedGraphMonitorTable67.labelsOf table) ∅
        (bottomNode ⟨9, by decide⟩ leaf) rfl)
    simp only [labelsFrom, GroupedBalancedGraphMonitorTable67.labelsOf,
      covered, Option.getD_some]
  · have covered := GroupedBalancedGraphMonitorSetup67.cache_covers table
      (.inl (upperNode ⟨base.val - 1, by omega⟩ leaf))
      (GroupedBalancedGraphMonitorSetup67.node_authorized
        (GroupedBalancedGraphMonitorTable67.labelsOf table) ∅
        (upperNode ⟨base.val - 1, by omega⟩ leaf) rfl)
    simp only [labelsFrom, GroupedBalancedGraphMonitorTable67.labelsOf,
      covered, Option.getD_some]

theorem cached_layers_labels (table : PointTable) (heights : List Nat)
    (base index : Nat) :
    cachedLayers (GroupedBalancedGraphMonitorSetup67.cache table)
      (labelsFrom (GroupedBalancedGraphMonitorSetup67.cache table))
      heights base index =
    cachedLayers (GroupedBalancedGraphMonitorSetup67.cache table)
      (GroupedBalancedGraphMonitorTable67.labelsOf table)
      heights base index := by
  induction heights generalizing base index with
  | nil => rfl
  | cons height rest ih =>
      simp only [cachedLayers]
      rw [canonical_from_cache]
      exact congrArg (GroupedBalancedScheme67.UpperWitnesses.cons
        (GroupedBalancedGraphUpperWitnessCache67.witnessFromCache
          (GroupedBalancedGraphMonitorSetup67.cache table)
          (Fin.ofNat 150 (base - 10))
          (canonicalMessage (GroupedBalancedGraphMonitorTable67.labelsOf table)
            (Fin.ofNat 150 (base - 10)) (BitVec.ofNat 160 index))
          height (index / 2 ^ height) index))
        (ih (base + height) (index / 2 ^ height))

def signatureFromCache (residual : Hash) (secretKey : SecretKey)
    (message : Message) (cache : QueryCache PointSpec)
    (bottomAnswer : BitVec 256) : GroupedBalancedScheme67.Signature :=
  let randomizer := Reference.randomizer residual secretKey message
  let index := Reference.indexOf residual message randomizer
  ⟨randomizer,
    GroupedBalancedGraphBottomWitnessCache67.witnessFromCache cache
      index bottomAnswer 10 (GroupedMixedIndex.bottomTree index),
    cachedLayers cache (labelsFrom cache)
      GroupedBalancedScheme67.Heights 10 (GroupedMixedIndex.bottomTree index)⟩

theorem programmed_sign_from_cache
    (residual : Hash) (secretKey : SecretKey) (labels : Labels)
    (table : PointTable)
    (labelsMatch : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
    (bottomMatch : ∀ index : BitVec 160,
      (GroupedBalancedGraphReference67.sourceAnswers residual secretKey).bottom index =
        (GroupedBalancedGraphMonitorTable67.privateOf table).bottom index)
    (sourceMatch : ∀ base leaf chain,
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        base leaf chain =
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        base leaf chain)
    (message : Message) :
    let hash := GroupedBalancedGraphProgrammedReference67.programmedGrouped
      residual secretKey labels
    let randomizer := Reference.randomizer residual secretKey message
    let index := Reference.indexOf residual message randomizer
    GroupedBalancedScheme67.sign hash secretKey message =
      signatureFromCache residual secretKey message
        (GroupedBalancedGraphMonitorSetup67.cache table)
        (table (.inr (.inl index))) := by
  let hash := GroupedBalancedGraphProgrammedReference67.programmedGrouped
    residual secretKey labels
  let randomizer := Reference.randomizer residual secretKey message
  let index := Reference.indexOf residual message randomizer
  have randomizerEq : Reference.randomizer hash secretKey message = randomizer :=
    GroupedBalancedGraphProgrammedReference67.programmed_randomizer
      residual secretKey labels message
  have indexEq : Reference.indexOf hash message randomizer = index :=
    programmed_index residual secretKey labels message randomizer
  have bottomEq := build_ten_witness_from_cache residual secretKey labels
    table labelsMatch bottomMatch index
  have upperEq := sign_upper_from_cache_for_index residual secretKey labels
    table labelsMatch sourceMatch index
  have labelsEq := cached_layers_labels table GroupedBalancedScheme67.Heights
    10 (GroupedMixedIndex.bottomTree index)
  simp only [GroupedBalancedScheme67.sign, signatureFromCache,
    GroupedBalancedGraphProgrammedReference67.programmed_randomizer,
    programmed_index]
  rw [bottomEq, upperEq, labelsEq]
  rw [labelsMatch]

end SigGolfCandidate.Hypertree.GroupedBalancedGraphSignerFromCache67

end

/-! The honest sign operation is a finite monitor View: two cache-consistent
private tag-6/tag-5 oracle reads, one bottom-source disclosure, and an exact
signature assembled from the setup cache. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphHonestSignView67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphSignerFromCache67
set_option maxRecDepth 8192
open scoped Classical

theorem locate_randomizer_none (secretKey : SecretKey) (message : Message) :
    GroupedBalancedGraphQuery67.locate
      (SecurityRandomOracle.randomizerInput secretKey message) = none := by
  unfold GroupedBalancedGraphQuery67.locate
  split
  next found =>
    obtain ⟨position, data, same⟩ := found
    have addressEq : (⟨6, 0, 0, 0, 0, 0⟩ : SecurityGraph.Address) =
        position.val := SecurityGraph.Address.eq_of_input_eq same.symm
    have tags := congrArg
      (fun address : SecurityGraph.Address => address.tag.val) addressEq
    change (6 : Nat) = position.val.tag.val at tags
    rcases position.property with chain | leaf | node <;> omega
  next absent => rfl

theorem locate_index_none (message : Message) (randomizer : Bytes 32) :
    GroupedBalancedGraphQuery67.locate
      (SecurityRandomOracle.indexInput message randomizer) = none := by
  unfold GroupedBalancedGraphQuery67.locate
  split
  next found =>
    obtain ⟨position, data, same⟩ := found
    have addressEq : (⟨5, 0, 0, 0, 0, 0⟩ : SecurityGraph.Address) =
        position.val := SecurityGraph.Address.eq_of_input_eq same.symm
    have tags := congrArg
      (fun address : SecurityGraph.Address => address.tag.val) addressEq
    change (5 : Nat) = position.val.tag.val at tags
    rcases position.property with chain | leaf | node <;> omega
  next absent => rfl

def signatureFromAnswers (cache : QueryCache PointSpec)
    (randomizer : Bytes 32) (index : BitVec 160)
    (bottomAnswer : BitVec 256) : GroupedBalancedScheme67.Signature :=
  ⟨randomizer,
    GroupedBalancedGraphBottomWitnessCache67.witnessFromCache cache
      index bottomAnswer 10 (GroupedMixedIndex.bottomTree index),
    GroupedBalancedGraphUpperLayersCache67.cachedLayers cache
      (labelsFrom cache) GroupedBalancedScheme67.Heights 10
      (GroupedMixedIndex.bottomTree index)⟩

theorem signature_from_cache_answers (residual : Hash)
    (secretKey : SecretKey) (message : Message)
    (cache : QueryCache PointSpec) (bottomAnswer : BitVec 256) :
    signatureFromCache residual secretKey message cache bottomAnswer =
      signatureFromAnswers cache
        (Reference.randomizer residual secretKey message)
        (Reference.indexOf residual message
          (Reference.randomizer residual secretKey message)) bottomAnswer := rfl

theorem programmed_sign_from_answers
    (residual : Hash) (secretKey : SecretKey) (labels : Labels)
    (table : PointTable)
    (labelsMatch : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
    (bottomMatch : ∀ index : BitVec 160,
      (GroupedBalancedGraphReference67.sourceAnswers residual secretKey).bottom index =
        (GroupedBalancedGraphMonitorTable67.privateOf table).bottom index)
    (sourceMatch : ∀ base leaf chain,
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        base leaf chain =
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        base leaf chain)
    (message : Message) :
    let hash := GroupedBalancedGraphProgrammedReference67.programmedGrouped
      residual secretKey labels
    let randomizer := residual
      (SecurityRandomOracle.randomizerInput secretKey message)
    let indexAnswer := residual
      (SecurityRandomOracle.indexInput message randomizer)
    let index : BitVec 160 := indexAnswer.extractLsb' 0 160
    GroupedBalancedScheme67.sign hash secretKey message =
      signatureFromAnswers (GroupedBalancedGraphMonitorSetup67.cache table)
        randomizer index (table (.inr (.inl index))) := by
  simpa only [Reference.randomizer, Reference.indexOf,
    SecurityRandomOracle.randomizerInput,
    SecurityRandomOracle.indexInput,
    SecurityRandomOracle.query_eq,
    signature_from_cache_answers] using
    (programmed_sign_from_cache residual secretKey labels table
      labelsMatch bottomMatch sourceMatch message)

noncomputable def honestSign {α : Type} (secretKey : SecretKey)
    (message : Message) (cache : QueryCache PointSpec)
    (next : GroupedBalancedScheme67.Signature → View α) : View α :=
  .privateHash (SecurityRandomOracle.randomizerInput secretKey message)
    (locate_randomizer_none secretKey message) (fun randomizer =>
      .privateHash (SecurityRandomOracle.indexInput message randomizer)
        (locate_index_none message randomizer) (fun indexAnswer =>
          let index : BitVec 160 := indexAnswer.extractLsb' 0 160
          .sign index (fun bottomAnswer =>
            next (signatureFromAnswers cache randomizer index bottomAnswer))))

end SigGolfCandidate.Hypertree.GroupedBalancedGraphHonestSignView67
