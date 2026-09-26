import SigGolfCandidate.Hypertree.GroupedBalancedUpperMerkleBadLogged67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphWotsContact67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTrace67
import SigGolfCandidate.Hypertree.GroupedBalancedUpperPathFault67
import SigGolfCandidate.Hypertree.GroupedBalancedMixedPathFault67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphSignHistory67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphWotsLogged67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedPathFaultLogged67. -/
section
/-! Every upper WOTS collision contact from an accepted path names an actual
query in the selected upper verifier leaf. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphWotsLogged67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67
open GroupedBalancedGraphProgrammedReference67
open GroupedBalancedUpperTree67
open GroupedBalancedWotsExtraction67 SecurityExtraction
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem leaf_collision_logged
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
    (base : Fin 150) (leaf : BitVec 160)
    (message : Reference.Digest)
    (values : ChainMixed → Reference.Digest)
    (bad : LeafCollision (programmedGrouped residual secretKey labels)
      secretKey (base.val + 10) leaf.toNat message values) :
    ∃ query,
      GroupedBalancedGraphMonitorPublicCoupling67.outputHit table query
        ((programmedGrouped residual secretKey labels) query) ∧
      query ∈ SecurityVerifyTrace.queries
        (programmedGrouped residual secretKey labels)
        (GroupedBalancedVerifyOracle67.recoverLeaf
          (base.val + 10) leaf.toNat message values) := by
  let hash := programmedGrouped residual secretKey labels
  rcases bad with leafCollision | chainCollision
  · have endpoints :
        (fun chain : ChainMixed => endpoint hash secretKey
          (base.val + 10) leaf.toNat chain) =
        (fun chain : ChainMixed => truncate
          (labels (upperChain base leaf chain (endpointStep chain)))) := by
      funext chain
      exact GroupedBalancedGraphProgrammedLeaf67.programmed_upper_endpoint
        residual secretKey labels base leaf chain
    have expectedPayload :
        ((List.ofFn (endpoint hash secretKey
          (base.val + 10) leaf.toNat)).flatMap bytes) =
        ((List.ofFn (fun chain : ChainMixed => truncate
          (labels (upperChain base leaf chain (endpointStep chain))))).flatMap bytes) := by
      rw [← endpoints]
    rw [expectedPayload] at leafCollision
    let payload := ((List.ofFn (fun chain => walk
      (chainHash hash (base.val + 10) leaf.toNat chain)
      (digit message chain).val
      (maxDigit chain - (digit message chain).val)
      (values chain))).flatMap bytes)
    let query := (upperLeaf base leaf).input payload
    refine ⟨query, ?_, ?_⟩
    · exact GroupedBalancedGraphMonitorCollisionBridge67.upper_leaf_collision_outputHit
        table residual secretKey labels labelsMatch bottomMatch sourceMatch
        base leaf _ leafCollision
    · simpa only [query, payload, upper_leaf_input] using
        GroupedBalancedVerifyTrace67.mem_recoverLeaf_compress hash
          (base.val + 10) leaf.toNat message values
  · rcases chainCollision with ⟨chain, offset, offsetBound, collision⟩
    let step := (digit message chain).val + offset
    have digitBound := GroupedBalancedChecksum67.digit_le_max message chain
    change (digit message chain).val ≤ maxDigit chain at digitBound
    change offset < maxDigit chain - (digit message chain).val at offsetBound
    have stepBound : step < maxDigit chain := by
      dsimp [step]
      omega
    have stepTen : step < 10 := lt_of_lt_of_le stepBound
      (GroupedBalancedSecurityGraph67.max_digit_le_ten chain)
    by_cases zero : step = 0
    · have stepEq : (digit message chain).val + offset = 0 := by
        simpa only [step] using zero
      have canonical :
          walk (chainHash hash (base.val + 10) leaf.toNat chain) 0 0
            (secret hash secretKey (base.val + 10) leaf.toNat chain) =
          secret residual secretKey (base.val + 10) leaf.toNat chain := by
        simpa only [walk] using
          GroupedBalancedGraphProgrammedReference67.programmed_upper_secret
            residual secretKey labels base leaf chain
      rw [stepEq, canonical] at collision
      let payload := bytes (walk
        (chainHash hash (base.val + 10) leaf.toNat chain)
        (digit message chain).val offset (values chain))
      let query := (upperChain base leaf chain 0).input payload
      refine ⟨query, ?_, ?_⟩
      · exact GroupedBalancedGraphMonitorCollisionBridge67.upper_zero_collision_outputHit
          table residual secretKey labels labelsMatch bottomMatch
          sourceMatch base leaf chain _ collision
      · simpa [query, payload, upper_chain_input, stepEq] using
          GroupedBalancedVerifyTrace67.mem_recoverLeaf_chain hash
            (base.val + 10) leaf.toNat message values chain offset offsetBound

    · let previous := step - 1
      have stepEq : (digit message chain).val + offset = previous + 1 := by
        dsimp [step, previous] at *
        omega
      have previousBound : previous < 9 := by
        dsimp [previous] at *
        omega
      let previousFin : Fin 9 := ⟨previous, previousBound⟩
      have canonical :
          walk (chainHash hash (base.val + 10) leaf.toNat chain) 0
            (previous + 1)
            (secret hash secretKey (base.val + 10) leaf.toNat chain) =
          truncate (labels
            (upperChain base leaf chain ⟨previous, by omega⟩)) := by
        simpa only [Nat.succ_eq_add_one] using
          GroupedBalancedGraphProgrammedLeaf67.programmed_upper_walk
            residual secretKey labels base leaf chain previous (by omega)
      rw [stepEq, canonical] at collision
      let payload := bytes (walk
        (chainHash hash (base.val + 10) leaf.toNat chain)
        (digit message chain).val offset (values chain))
      let query := (upperChain base leaf chain
        ⟨previous + 1, by omega⟩).input payload
      refine ⟨query, ?_, ?_⟩
      · exact GroupedBalancedGraphMonitorCollisionBridge67.upper_step_collision_outputHit
          table residual secretKey labels labelsMatch bottomMatch
          sourceMatch base leaf chain previousFin _ collision
      · simpa [query, payload, upper_chain_input, stepEq] using
          GroupedBalancedVerifyTrace67.mem_recoverLeaf_chain hash
            (base.val + 10) leaf.toNat message values chain offset offsetBound

theorem upper_collision_logged
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
    (base : Fin 150) (leaf : BitVec 160)
    (message : Reference.Digest)
    (values : ChainMixed → Reference.Digest)
    (height address index : Nat)
    (witness : GroupedBalancedUpperTree67.Witness height)
    (leafEq : GroupedBottomTree.selectedLeafAddress height address index = leaf.toNat)
    (valuesEq : GroupedBalancedUpperIndex67.witnessValues witness = values)
    (bad : LeafCollision (programmedGrouped residual secretKey labels)
      secretKey (base.val + 10) leaf.toNat message values) :
    ∃ query,
      GroupedBalancedGraphMonitorPublicCoupling67.outputHit table query
        ((programmedGrouped residual secretKey labels) query) ∧
      query ∈ SecurityVerifyTrace.queries
        (programmedGrouped residual secretKey labels)
        (GroupedBalancedVerifyOracle67.recoverUpper
          (base.val + 10) height address index message witness) := by
  obtain ⟨query, hit, member⟩ := leaf_collision_logged table residual secretKey
    labels labelsMatch bottomMatch sourceMatch base leaf message values bad
  refine ⟨query, hit, ?_⟩
  apply GroupedBalancedVerifyTrace67.mem_recoverUpper_leaf
    (programmedGrouped residual secretKey labels) (base.val + 10)
    height address index message witness query
  simpa only [leafEq, valuesEq] using member

#print axioms upper_collision_logged

end SigGolfCandidate.Hypertree.GroupedBalancedGraphWotsLogged67
end

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedUpperFaultLogged67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedPathFaultLogged67. -/
section
/-! Any upper-path fault contacts a public output on the group verifier trace. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedUpperFaultLogged67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67
open GroupedBalancedGraphProgrammedReference67
open GroupedBalancedUpperPathFault67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem upper_fault_logged
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
    (base : Fin 150) (height index : Nat)
    (heightBound : height ≤ 4)
    (levelBound : base.val + height ≤ 150)
    (aligned : ∀ offset < height,
      GroupedBalancedGraphPayload67.groupBase
        (base.val + 10 + offset) = base.val + 10)
    (indexBound : index < 2 ^ 160)
    (message : Reference.Digest)
    (witness : GroupedBalancedUpperTree67.Witness height)
    (bad : Bad (programmedGrouped residual secretKey labels)
      secretKey (base.val + 10) height index message witness) :
    ∃ query,
      GroupedBalancedGraphMonitorPublicCoupling67.outputHit table query
        ((programmedGrouped residual secretKey labels) query) ∧
      query ∈ SecurityVerifyTrace.queries
        (programmedGrouped residual secretKey labels)
        (GroupedBalancedVerifyOracle67.recoverUpper
          (base.val + 10) height (index / 2 ^ height) index message witness) := by
  rcases bad with merkle | wots
  · have addressBound : index / 2 ^ height < 2 ^ (160 - height) := by
      rw [Nat.div_lt_iff_lt_mul (pow_pos (by decide) _)]
      have exponent : 160 - height + height = 160 := by omega
      rw [← pow_add, exponent]
      exact indexBound
    exact GroupedBalancedUpperMerkleBadLogged67.bad_contact_logged table
      residual secretKey labels labelsMatch bottomMatch sourceMatch base
      message height (index / 2 ^ height) index heightBound levelBound
      aligned addressBound witness merkle
  · have leafFits : (BitVec.ofNat 160 index).toNat = index := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt indexBound
    have leafEq : GroupedBottomTree.selectedLeafAddress height
        (index / 2 ^ height) index = (BitVec.ofNat 160 index).toNat := by
      rw [GroupedBottomTree.selectedLeafAddress_index, leafFits]
    exact GroupedBalancedGraphWotsLogged67.upper_collision_logged table
      residual secretKey labels labelsMatch bottomMatch sourceMatch
      base (BitVec.ofNat 160 index) message
      (GroupedBalancedUpperIndex67.witnessValues witness)
      height (index / 2 ^ height) index witness leafEq rfl
      (by simpa only [leafFits] using wots)

#print axioms upper_fault_logged

end SigGolfCandidate.Hypertree.GroupedBalancedUpperFaultLogged67

end

/-! An upper path fault yields either a contact on the upper verifier trace
or a strictly earlier canonical WOTS point. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPathFaultLogged67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedScheme67
open GroupedBalancedGraphProgrammedReference67
open GroupedBalancedMixedPathFault67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

def EarlierExposure (hash : Hash) (secretKey : SecretKey) :
    (heights : List Nat) → (base index : Nat) →
      (expected actual : Reference.Digest) → UpperWitnesses heights → Prop
  | [], _, _, _, _, .nil => False
  | height :: rest, base, index, expected, actual, .cons head tail =>
      let tree := index / 2 ^ height
      let actualRoot := GroupedBalancedUpperTree67.recover hash base height tree
        index actual head
      let canonicalRoot := GroupedBalancedUpperTree67.root hash secretKey base
        height tree
      (expected ≠ actual ∧
        GroupedBalancedUpperPathFault67.EarlierPointExposure hash secretKey
          base index expected actual head) ∨
      EarlierExposure hash secretKey rest (base + height) tree
        canonicalRoot actualRoot tail

theorem path_fault_logged_or_exposure
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
    (heights : List Nat) :
    ∀ (base index : Nat) (expected actual : Reference.Digest)
      (witnesses : UpperWitnesses heights),
      GroupedBalancedGraphSignHistory67.Schedule base heights →
      10 ≤ base → base ≤ 160 →
      index < 2 ^ (160 - base) →
      PathFault (programmedGrouped residual secretKey labels) secretKey
        heights base index expected actual witnesses →
      (∃ query,
        GroupedBalancedGraphMonitorPublicCoupling67.outputHit table query
          ((programmedGrouped residual secretKey labels) query) ∧
        query ∈ SecurityVerifyTrace.queries
          (programmedGrouped residual secretKey labels)
          (GroupedBalancedVerifyOracle67.recoverLayers
            heights base index actual witnesses)) ∨
      EarlierExposure (programmedGrouped residual secretKey labels)
        secretKey heights base index expected actual witnesses := by
  induction heights with
  | nil =>
      intro base index expected actual witnesses _ _ _ _ fault
      cases witnesses
      exact False.elim fault
  | cons height rest ih =>
      intro base index expected actual witnesses schedule baseMin baseMax
        indexBound fault
      cases witnesses with
      | cons head tail =>
          obtain ⟨heightPositive, heightMax, nextBaseMax,
            aligned, tailSchedule⟩ := schedule
          let hash := programmedGrouped residual secretKey labels
          let tree := index / 2 ^ height
          let actualRoot := GroupedBalancedUpperTree67.recover hash base
            height tree index actual head
          let canonicalRoot := GroupedBalancedUpperTree67.root hash
            secretKey base height tree
          change GroupedBalancedUpperPathFault67.Bad hash secretKey base
              height index actual head ∨
            (expected ≠ actual ∧
              GroupedBalancedUpperPathFault67.EarlierPointExposure
                hash secretKey base index expected actual head) ∨
            PathFault hash secretKey rest (base + height) tree
              canonicalRoot actualRoot tail at fault
          rcases fault with bad | exposure | tailFault
          · have baseLt : base < 160 := by omega
            let baseFin : Fin 150 := ⟨base - 10, by omega⟩
            have baseEq : baseFin.val + 10 = base := by
              dsimp [baseFin]
              omega
            have alignedFin : ∀ offset < height,
                GroupedBalancedGraphPayload67.groupBase
                  (baseFin.val + 10 + offset) = baseFin.val + 10 := by
              intro offset bound
              simpa only [baseEq] using aligned offset bound
            have indexFits : index < 2 ^ 160 :=
              lt_of_lt_of_le indexBound
                (pow_le_pow_right₀ (by decide : 1 ≤ (2 : Nat))
                  (Nat.sub_le 160 base))
            obtain ⟨query, hit, member⟩ :=
              GroupedBalancedUpperFaultLogged67.upper_fault_logged
                table residual secretKey labels labelsMatch bottomMatch
                sourceMatch baseFin height index heightMax
                (by dsimp [baseFin]; omega) alignedFin indexFits actual head
                (by simpa only [baseEq, hash] using bad)
            refine Or.inl ⟨query, hit, ?_⟩
            apply GroupedBalancedVerifyTrace67.mem_recoverLayers_head
              hash height rest base index actual head tail query
            simpa only [baseEq] using member
          · exact Or.inr (by
              change (expected ≠ actual ∧
                  GroupedBalancedUpperPathFault67.EarlierPointExposure
                    hash secretKey base index expected actual head) ∨
                EarlierExposure hash secretKey rest (base + height) tree
                  canonicalRoot actualRoot tail
              exact Or.inl exposure)
          · have tailBound : tree < 2 ^ (160 - (base + height)) :=
              GroupedBalancedGraphSignHistory67.address_bound base height
                index nextBaseMax indexBound
            rcases ih (base + height) tree canonicalRoot actualRoot tail
              tailSchedule (by omega) nextBaseMax tailBound tailFault with
              contact | exposure
            · obtain ⟨query, hit, member⟩ := contact
              refine Or.inl ⟨query, hit, ?_⟩
              exact GroupedBalancedVerifyTrace67.mem_recoverLayers_tail
                hash height rest base index actual head tail query member
            · exact Or.inr (by
                change (expected ≠ actual ∧
                    GroupedBalancedUpperPathFault67.EarlierPointExposure
                      hash secretKey base index expected actual head) ∨
                  EarlierExposure hash secretKey rest (base + height) tree
                    canonicalRoot actualRoot tail
                exact Or.inr exposure)

#print axioms path_fault_logged_or_exposure

end SigGolfCandidate.Hypertree.GroupedBalancedPathFaultLogged67
