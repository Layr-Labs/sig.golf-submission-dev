import SigGolfCandidate.Hypertree.GroupedBalancedGraphEarlierInputHit67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphBottomMerkleContact67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphPathInputHit67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphAcceptedExtraction67. -/
section
/-! A strictly earlier WOTS point anywhere in the 45-group verification path
forces a hidden-input contact under the monitor's safe exposure invariant. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphPathInputHit67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedScheme67
open GroupedBalancedGraphProgrammedReference67
open GroupedBalancedGraphPathFaultContact67
open GroupedBalancedGraphMonitorAuthorization67
open GroupedBalancedGraphSignHistory67
open GroupedBalancedGraphCanonicalRoot67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem earlier_exposure_inputHit
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
        GroupedBalancedGraphMonitorPublicCoupling67.inputHit table exposed query := by
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
            exact GroupedBalancedGraphEarlierInputHit67.exposure_inputHit
              table residual secretKey labels labelsMatch sourceMatch
              signedBottom exposed safe baseFin (BitVec.ofNat 160 index)
              expected actual expectedEq head frontAtLeaf
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
                exact ih (base + height) tree canonicalRoot actualRoot tail
                  tailSchedule (by omega) nextBaseMax treeBound
                  ⟨⟨baseFin.val + height, nextFinBound⟩,
                    nextBaseFin, nextExpected⟩ tailExposure

end SigGolfCandidate.Hypertree.GroupedBalancedGraphPathInputHit67

end

/-! An accepted direct67 structured signature either produces a monitored
verifier contact or exposes the exact private bottom seed at its selected
index. The former covers every Merkle, leaf, and WOTS fault. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphAcceptedExtraction67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedScheme67
open GroupedBalancedGraphProgrammedReference67
open GroupedBalancedGraphSignHistory67
open GroupedBalancedGraphCanonicalRoot67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem accepted_contact_or_bottom_source
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
    (index : BitVec 160) (signature : GroupedBalancedScheme67.Signature)
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
        ((programmedGrouped residual secretKey labels) query)) ∨
    (∃ query,
      GroupedBalancedGraphMonitorPublicCoupling67.inputHit table exposed query) ∨
    signature.bottom.seedValue =
      GroupedBottomTree.secret
        (programmedGrouped residual secretKey labels)
        secretKey index.toNat := by
  let hash := programmedGrouped residual secretKey labels
  have indexBound : GroupedMixedIndex.bottomTree index < 2 ^ (160 - 10) := by
    change index.toNat / 2 ^ 10 < 2 ^ (160 - 10)
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 10)]
    have factor : 2 ^ (160 - 10) * 2 ^ 10 = 2 ^ 160 := by decide
    rw [factor]
    exact index.isLt
  rcases GroupedBalancedMixedPathFault67.accepted_fault_or_bottom_source
    hash secretKey index signature accepted with upper | source | bottomBad
  · rcases GroupedBalancedGraphPathFaultContact67.path_fault_contact_or_exposure
      table residual secretKey labels labelsMatch bottomMatch sourceMatch
      Heights 10 (GroupedMixedIndex.bottomTree index)
      (GroupedBottomTree.root hash secretKey 10
        (GroupedMixedIndex.bottomTree index))
      (GroupedBottomTree.recover hash 10
        (GroupedMixedIndex.bottomTree index) index.toNat signature.bottom)
      signature.upper heights_schedule (by decide) (by decide)
      indexBound upper with contact | exposure
    · exact Or.inl contact
    · have incoming :
          ∃ baseFin : Fin 150, baseFin.val + 10 = 10 ∧
            GroupedBottomTree.root hash secretKey 10
              (GroupedMixedIndex.bottomTree index) =
            GroupedBalancedGraphMonitorAuthorization67.canonicalMessage
              labels baseFin
              (BitVec.ofNat 160 (GroupedMixedIndex.bottomTree index)) := by
        refine ⟨⟨0, by decide⟩, rfl, ?_⟩
        exact bottom_root_canonical residual secretKey labels index
      exact Or.inr (Or.inl
        (GroupedBalancedGraphPathInputHit67.earlier_exposure_inputHit
          table residual secretKey labels labelsMatch sourceMatch
          signedBottom exposed safe Heights 10
          (GroupedMixedIndex.bottomTree index)
          (GroupedBottomTree.root hash secretKey 10
            (GroupedMixedIndex.bottomTree index))
          (GroupedBottomTree.recover hash 10
            (GroupedMixedIndex.bottomTree index) index.toNat signature.bottom)
          signature.upper heights_schedule (by decide) (by decide)
          indexBound incoming exposure))
  · exact Or.inr (Or.inr source)
  · exact Or.inl
      (GroupedBalancedGraphBottomMerkleContact67.bad_contact table
        residual secretKey labels labelsMatch bottomMatch sourceMatch
        10 (GroupedMixedIndex.bottomTree index) index.toNat
        (by decide) indexBound signature.bottom bottomBad)

end SigGolfCandidate.Hypertree.GroupedBalancedGraphAcceptedExtraction67
