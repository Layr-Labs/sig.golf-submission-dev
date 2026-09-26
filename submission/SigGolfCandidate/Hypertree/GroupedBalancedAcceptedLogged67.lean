import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTrace67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphEarlierInputHit67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSuccessor67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorExposure67
import SigGolfCandidate.Hypertree.GroupedBalancedPathFaultLogged67
import SigGolfCandidate.Hypertree.GroupedBalancedBottomVerifyLogged67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedEarlierInputLogged67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedAcceptedLogged67. -/
section
/-! A verifier starting a WOTS chain before the signed frontier reads a hidden
canonical predecessor at a concrete query of the selected upper group. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedEarlierInputLogged67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedSecurityGraph67
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorAuthorization67
open GroupedBalancedGraphMonitorPredecessor67
open GroupedBalancedGraphMonitorPublicCoupling67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem predecessor_earlier (base : Fin 150) (leaf : BitVec 160)
    (chain : Fin 67) (digit : Fin 11) (bound : digit.val < 10) :
    predecessor
      (upperChain base leaf chain ⟨digit.val, bound⟩).val =
      some (earlierPoint base leaf chain digit) := by
  by_cases zero : digit.val = 0
  · have stepEq : (⟨digit.val, bound⟩ : Fin 10) = 0 := Fin.ext zero
    rw [stepEq,
      GroupedBalancedGraphMonitorSuccessor67.predecessor_upper_zero]
    simp only [earlierPoint, zero, dif_pos]
  · have positive : 0 < (⟨digit.val, bound⟩ : Fin 10).val := by
      change 0 < digit.val
      omega
    rw [GroupedBalancedGraphMonitorSuccessor67.predecessor_upper_positive
      base leaf chain ⟨digit.val, bound⟩ positive]
    simp [earlierPoint, zero]

theorem exposure_input_logged
    (table : GroupedBalancedGraphPassive67.PointTable)
    (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (labelsMatch : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
    (sourceMatch : ∀ base leaf chain,
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        base leaf chain =
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        base leaf chain)
    (signedBottom : Finset (BitVec 160))
    (exposed : QueryCache PointSpec)
    (safe : GroupedBalancedGraphMonitorInvariant67.ExposedSafe
      (GroupedBalancedGraphMonitorTable67.labelsOf table)
      signedBottom exposed)
    (base : Fin 150) (leaf : BitVec 160)
    (signed forged : Reference.Digest)
    (signedEq : signed = canonicalMessage labels base leaf)
    {height : Nat} (witness : GroupedBalancedUpperTree67.Witness height)
    (address index : Nat)
    (leafEq : GroupedBottomTree.selectedLeafAddress height address index =
      leaf.toNat)
    (exposure : GroupedBalancedUpperPathFault67.EarlierPointExposure
      (GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels)
      secretKey (base.val + 10) leaf.toNat signed forged witness) :
    ∃ query,
      inputHit table exposed query ∧
      query ∈ SecurityVerifyTrace.queries
        (GroupedBalancedGraphProgrammedReference67.programmedGrouped
          residual secretKey labels)
        (GroupedBalancedVerifyOracle67.recoverUpper
          (base.val + 10) height address index forged witness) := by
  obtain ⟨chain, earlier, witnessEq⟩ :=
    GroupedBalancedGraphEarlierExposure67.exposure_eq_graph_point
      residual secretKey labels base leaf signed forged witness exposure
  let digit := GroupedBalancedUpperTree67.digit forged chain
  have digitBound := GroupedBalancedChecksum67.digit_le_max signed chain
  change (GroupedBalancedUpperTree67.digit signed chain).val ≤
    GroupedBalancedUpperTree67.maxDigit chain at digitBound
  have maxBound := GroupedBalancedSecurityGraph67.max_digit_le_ten chain
  have stepBound : digit.val < 10 := by
    dsimp [digit]
    omega
  let position := upperChain base leaf chain ⟨digit.val, stepBound⟩
  let point := earlierPoint base leaf chain digit
  have previous : predecessor position.val = some point := by
    exact predecessor_earlier base leaf chain digit stepBound
  have unauthorized : ¬Authorized
      (GroupedBalancedGraphMonitorTable67.labelsOf table)
      signedBottom point := by
    rw [← labelsMatch]
    apply earlier_unauthorized labels signedBottom base leaf chain digit
    change digit.val <
      (GroupedBalancedUpperTree67.digit
        (canonicalMessage labels base leaf) chain).val
    rw [← signedEq]
    exact earlier
  have hidden : exposed point = none :=
    safe.hidden _ _ exposed point unauthorized
  have valueEq :
      GroupedBalancedUpperIndex67.witnessValues witness chain =
      truncate (table point) := by
    exact witnessEq.trans
      (GroupedBalancedGraphMonitorExposure67.earlierValue_eq_table
        residual secretKey labels table labelsMatch sourceMatch
        base leaf chain digit)
  let query := position.input
    (bytes (GroupedBalancedUpperIndex67.witnessValues witness chain))
  have canonical : query =
      GroupedBalancedGraphCausality67.graphInput
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        (GroupedBalancedGraphMonitorTable67.labelsOf table) position := by
    have chainPayload :=
      GroupedBalancedGraphMonitorPredecessor67.chain_payload_eq table position.val
    rw [previous] at chainPayload
    dsimp only [query]
    rw [valueEq]
    simp only [query, GroupedBalancedGraphCausality67.graphInput]
    have tagTwo : position.val.tag.val = 2 := by rfl
    rw [GroupedBalancedGraphPayload67.payload, if_pos tagTwo]
    exact congrArg position.input chainPayload.symm
  refine ⟨query, ?_, ?_⟩
  have located : GroupedBalancedGraphQuery67.locate query = some position := by
    exact GroupedBalancedGraphQuery67.locate_address position _
  have tagTwo : position.val.tag.val = 2 := by rfl
  simp only [inputHit, located, tagTwo, if_pos, previous]
  · exact ⟨hidden, canonical⟩
  · let hash := GroupedBalancedGraphProgrammedReference67.programmedGrouped
      residual secretKey labels
    have within : 0 < GroupedBalancedUpperTree67.maxDigit chain -
        (GroupedBalancedUpperTree67.digit forged chain).val := by
      omega
    have leafMember := GroupedBalancedVerifyTrace67.mem_recoverLeaf_chain
      hash (base.val + 10) leaf.toNat forged
      (GroupedBalancedUpperIndex67.witnessValues witness) chain 0 within
    have inputMember : query ∈ SecurityVerifyTrace.queries hash
        (GroupedBalancedVerifyOracle67.recoverLeaf
          (base.val + 10) leaf.toNat forged
          (GroupedBalancedUpperIndex67.witnessValues witness)) := by
      simpa only [query, position, digit,
        GroupedBalancedSecurityGraph67.upper_chain_input,
        Nat.add_zero, Hypertree.walk] using leafMember
    apply GroupedBalancedVerifyTrace67.mem_recoverUpper_leaf
      hash (base.val + 10) height address index forged witness query
    simpa only [leafEq] using inputMember

#print axioms exposure_input_logged

end SigGolfCandidate.Hypertree.GroupedBalancedEarlierInputLogged67
end

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedPathInputLogged67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedAcceptedLogged67. -/
section
/-! A strictly earlier WOTS point on the 45-group path gives a hidden-input
contact at a query executed by the actual upper verifier walk. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPathInputLogged67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedScheme67
open GroupedBalancedGraphProgrammedReference67
open GroupedBalancedPathFaultLogged67
open GroupedBalancedGraphMonitorAuthorization67
open GroupedBalancedGraphSignHistory67
open GroupedBalancedGraphCanonicalRoot67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem earlier_exposure_logged
    (table : GroupedBalancedGraphPassive67.PointTable)
    (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (labelsMatch : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
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
    (heights : List Nat) :
    ∀ (base index : Nat) (expected actual : Reference.Digest)
      (witnesses : UpperWitnesses heights),
      Schedule base heights →
      10 ≤ base → base ≤ 160 →
      index < 2 ^ (160 - base) →
      (∃ baseFin : Fin 150, baseFin.val + 10 = base ∧
        expected = canonicalMessage labels baseFin
          (BitVec.ofNat 160 index)) →
      EarlierExposure (programmedGrouped residual secretKey labels)
        secretKey heights base index expected actual witnesses →
      ∃ query,
        GroupedBalancedGraphMonitorPublicCoupling67.inputHit table exposed query ∧
        query ∈ SecurityVerifyTrace.queries
          (programmedGrouped residual secretKey labels)
          (GroupedBalancedVerifyOracle67.recoverLayers
            heights base index actual witnesses) := by
  induction heights with
  | nil =>
      intro base index expected actual witnesses _ _ _ _ _ exposure
      cases witnesses
      exact False.elim exposure
  | cons height rest ih =>
      intro base index expected actual witnesses schedule baseMin baseMax
        indexBound incoming exposure
      cases witnesses with
      | cons head tail =>
          obtain ⟨baseFin, baseEq, expectedEq⟩ := incoming
          obtain ⟨heightPositive, heightMax, nextBaseMax,
            aligned, tailSchedule⟩ := schedule
          let hash := programmedGrouped residual secretKey labels
          let tree := index / 2 ^ height
          let actualRoot := GroupedBalancedUpperTree67.recover hash base
            height tree index actual head
          let canonicalRoot := GroupedBalancedUpperTree67.root hash
            secretKey base height tree
          change (expected ≠ actual ∧
              GroupedBalancedUpperPathFault67.EarlierPointExposure
                hash secretKey base index expected actual head) ∨
            EarlierExposure hash secretKey rest (base + height) tree
              canonicalRoot actualRoot tail at exposure
          rcases exposure with front | tailExposure
          · have leafFits : (BitVec.ofNat 160 index).toNat = index :=
              bitvec_roundtrip base index baseMax indexBound
            have frontAtLeaf :
                GroupedBalancedUpperPathFault67.EarlierPointExposure hash
                  secretKey (baseFin.val + 10)
                  (BitVec.ofNat 160 index).toNat expected actual head := by
              simpa only [baseEq, leafFits, hash] using front.2
            have leafEq : GroupedBottomTree.selectedLeafAddress height tree index =
                (BitVec.ofNat 160 index).toNat := by
              rw [GroupedBottomTree.selectedLeafAddress_index, leafFits]
            obtain ⟨query, hit, member⟩ :=
              GroupedBalancedEarlierInputLogged67.exposure_input_logged
                table residual secretKey labels labelsMatch sourceMatch
                signedBottom exposed safe baseFin (BitVec.ofNat 160 index)
                expected actual expectedEq head tree index leafEq frontAtLeaf
            refine ⟨query, hit, ?_⟩
            apply GroupedBalancedVerifyTrace67.mem_recoverLayers_head
              hash height rest base index actual head tail query
            simpa only [baseEq, tree] using member
          · cases rest with
            | nil =>
                cases tail
                exact False.elim tailExposure
            | cons nextHeight remainder =>
                have nextPositive : 0 < nextHeight := tailSchedule.1
                have nextBaseLt : base + height < 160 := by
                  have nextScheduleBound := tailSchedule.2.2.1
                  omega
                have treeBound : tree < 2 ^ (160 - (base + height)) :=
                  address_bound base height index nextBaseMax indexBound
                have rootAddressBound : tree < 2 ^ (160 - height) :=
                  lt_of_lt_of_le treeBound
                    (pow_le_pow_right₀ (by decide : 1 ≤ (2 : Nat))
                      (by omega))
                have nextFinBound : baseFin.val + height < 150 := by
                  omega
                have alignedFin : ∀ offset < height,
                    GroupedBalancedGraphPayload67.groupBase
                      (baseFin.val + 10 + offset) = baseFin.val + 10 := by
                  simpa only [baseEq] using aligned
                have nextExpected : canonicalRoot =
                    canonicalMessage labels
                      ⟨baseFin.val + height, nextFinBound⟩
                      (BitVec.ofNat 160 tree) := by
                  dsimp only [canonicalRoot, hash]
                  rw [← baseEq]
                  exact upper_root_canonical residual secretKey labels
                    baseFin height tree heightPositive heightMax
                    nextFinBound alignedFin rootAddressBound
                have nextBaseFin :
                    (⟨baseFin.val + height, nextFinBound⟩ : Fin 150).val + 10 =
                      base + height := by
                  change baseFin.val + height + 10 = base + height
                  omega
                obtain ⟨query, hit, member⟩ :=
                  ih (base + height) tree canonicalRoot actualRoot tail
                    tailSchedule (by omega) nextBaseMax treeBound
                    ⟨⟨baseFin.val + height, nextFinBound⟩,
                      nextBaseFin, nextExpected⟩ tailExposure
                refine ⟨query, hit, ?_⟩
                exact GroupedBalancedVerifyTrace67.mem_recoverLayers_tail
                  hash height (nextHeight :: remainder) base index actual
                  head tail query member

#print axioms earlier_exposure_logged

end SigGolfCandidate.Hypertree.GroupedBalancedPathInputLogged67

end

/-! An accepted direct67 signature has a monitor contact at a verifier read,
or carries the exact private bottom seed. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedAcceptedLogged67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedScheme67
open GroupedBalancedGraphProgrammedReference67
open GroupedBalancedGraphSignHistory67
open GroupedBalancedGraphCanonicalRoot67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem accepted_logged_or_bottom_source
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
    (pk : PublicKey) (message : Message)
    (index : BitVec 160) (signature : GroupedBalancedScheme67.Signature)
    (indexEq : Reference.indexOf
      (programmedGrouped residual secretKey labels)
      message signature.randomizer = index)
    (accepted : recoverLayers
      (programmedGrouped residual secretKey labels) Heights 10
      (GroupedMixedIndex.bottomTree index)
      (GroupedBottomTree.recover
        (programmedGrouped residual secretKey labels) 10
        (GroupedMixedIndex.bottomTree index) index.toNat signature.bottom)
      signature.upper = GroupedBalancedScheme67.keygen
        (programmedGrouped residual secretKey labels) secretKey) :
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
    signature.bottom.seedValue =
      GroupedBottomTree.secret
        (programmedGrouped residual secretKey labels)
        secretKey index.toNat := by
  let hash := programmedGrouped residual secretKey labels
  have indexEqHash : Reference.indexOf hash message signature.randomizer =
      index := indexEq
  have indexBound : GroupedMixedIndex.bottomTree index < 2 ^ (160 - 10) := by
    change index.toNat / 2 ^ 10 < 2 ^ (160 - 10)
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 10)]
    have factor : 2 ^ (160 - 10) * 2 ^ 10 = 2 ^ 160 := by decide
    rw [factor]
    exact index.isLt
  rcases GroupedBalancedMixedPathFault67.accepted_fault_or_bottom_source
    hash secretKey index signature accepted with upper | source | bottomBad
  · rcases GroupedBalancedPathFaultLogged67.path_fault_logged_or_exposure
      table residual secretKey labels labelsMatch bottomMatch sourceMatch
      Heights 10 (GroupedMixedIndex.bottomTree index)
      (GroupedBottomTree.root hash secretKey 10
        (GroupedMixedIndex.bottomTree index))
      (GroupedBottomTree.recover hash 10
        (GroupedMixedIndex.bottomTree index) index.toNat signature.bottom)
      signature.upper heights_schedule (by decide) (by decide)
      indexBound upper with contact | exposure
    · obtain ⟨query, hit, member⟩ := contact
      refine Or.inl ⟨query, hit, ?_⟩
      apply GroupedBalancedVerifyTrace67.mem_verify_upper hash pk
        message signature query
      simpa only [indexEqHash] using member
    · have incoming :
          ∃ baseFin : Fin 150, baseFin.val + 10 = 10 ∧
            GroupedBottomTree.root hash secretKey 10
              (GroupedMixedIndex.bottomTree index) =
            GroupedBalancedGraphMonitorAuthorization67.canonicalMessage
              labels baseFin
              (BitVec.ofNat 160 (GroupedMixedIndex.bottomTree index)) := by
        refine ⟨⟨0, by decide⟩, rfl, ?_⟩
        exact bottom_root_canonical residual secretKey labels index
      obtain ⟨query, hit, member⟩ :=
        GroupedBalancedPathInputLogged67.earlier_exposure_logged
          table residual secretKey labels labelsMatch sourceMatch
          signedBottom exposed safe Heights 10
          (GroupedMixedIndex.bottomTree index)
          (GroupedBottomTree.root hash secretKey 10
            (GroupedMixedIndex.bottomTree index))
          (GroupedBottomTree.recover hash 10
            (GroupedMixedIndex.bottomTree index) index.toNat signature.bottom)
          signature.upper heights_schedule (by decide) (by decide)
          indexBound incoming exposure
      refine Or.inr (Or.inl ⟨query, hit, ?_⟩)
      apply GroupedBalancedVerifyTrace67.mem_verify_upper hash pk
        message signature query
      simpa only [indexEqHash] using member
  · exact Or.inr (Or.inr source)
  · exact Or.inl
      (GroupedBalancedBottomVerifyLogged67.bad_verify_logged table
        residual secretKey labels labelsMatch bottomMatch sourceMatch pk
        message signature index indexEq bottomBad)

#print axioms accepted_logged_or_bottom_source

end SigGolfCandidate.Hypertree.GroupedBalancedAcceptedLogged67
