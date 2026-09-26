import SigGolfCandidate.Hypertree.GroupedBalancedGraphUpperWitnessCache67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphUpperLayersCache67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphBottomWitnessCache67. -/
section
/-! All 45 upper signing witnesses are reconstructed from the initially
disclosed graph cache, at the successive tree addresses. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphUpperLayersCache67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorAuthorization67
open GroupedBalancedGraphSignHistory67
open GroupedBalancedGraphUpperWitnessCache67
open GroupedBalancedGraphCanonicalRoot67
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

def cachedLayers (cache : QueryCache PointSpec) (labels : Labels) :
    (heights : List Nat) → (base index : Nat) →
      GroupedBalancedScheme67.UpperWitnesses heights
  | [], _, _ => .nil
  | height :: rest, base, index =>
      let baseFin : Fin 150 := Fin.ofNat 150 (base - 10)
      let message := canonicalMessage labels baseFin (BitVec.ofNat 160 index)
      .cons (witnessFromCache cache baseFin message height
        (index / 2 ^ height) index)
        (cachedLayers cache labels rest (base + height) (index / 2 ^ height))

theorem signLayers_from_cache
    (residual : Hash) (secretKey : SecretKey) (labels : Labels)
    (table : PointTable)
    (labelsMatch : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
    (sourceMatch : ∀ base leaf chain,
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        base leaf chain =
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        base leaf chain)
    (heights : List Nat) :
    ∀ (base index : Nat) (message : Reference.Digest),
      Schedule base heights → 10 ≤ base →
      index < 2 ^ (160 - base) →
      (heights ≠ [] →
        ∃ baseFin : Fin 150, baseFin.val + 10 = base ∧
          message = canonicalMessage labels baseFin (BitVec.ofNat 160 index)) →
      GroupedBalancedScheme67.signLayers
        (GroupedBalancedGraphProgrammedReference67.programmedGrouped
          residual secretKey labels)
        secretKey heights base index message =
      cachedLayers (GroupedBalancedGraphMonitorSetup67.cache table)
        labels heights base index := by
  induction heights with
  | nil =>
      intro base index message schedule baseMin indexBound incoming
      rfl
  | cons height rest ih =>
      intro base index message schedule baseMin indexBound incoming
      obtain ⟨baseFin, baseEq, messageEq⟩ := incoming (by simp)
      obtain ⟨heightPositive, heightMax, nextBaseMax, aligned, tailSchedule⟩ := schedule
      let hash := GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels
      let tree := index / 2 ^ height
      let cachedBase : Fin 150 := Fin.ofNat 150 (base - 10)
      have baseMax : base < 160 := by omega
      have cachedBaseEq : cachedBase = baseFin := by
        apply Fin.ext
        simp only [cachedBase, Fin.ofNat, Fin.val_mk]
        rw [Nat.mod_eq_of_lt (by omega : base - 10 < 150)]
        omega
      have indexFits : index < 2 ^ 160 :=
        lt_of_lt_of_le indexBound
          (pow_le_pow_right₀ (by decide : 1 ≤ (2 : Nat)) (Nat.sub_le 160 base))
      have alignedFin : ∀ offset < height,
          GroupedBalancedGraphPayload67.groupBase
            (baseFin.val + 10 + offset) = baseFin.val + 10 := by
        simpa only [baseEq] using aligned
      have headEq :
          (GroupedBalancedUpperTree67.build hash secretKey base height
            tree index message).witness =
          witnessFromCache (GroupedBalancedGraphMonitorSetup67.cache table)
            cachedBase
            (canonicalMessage labels cachedBase (BitVec.ofNat 160 index))
            height tree index := by
        rw [cachedBaseEq, ← messageEq, ← baseEq]
        exact build_witness_from_cache_at_index residual secretKey labels table
          labelsMatch sourceMatch baseFin message height index
          heightMax (by omega) alignedFin indexFits messageEq
      have tailEq :
          GroupedBalancedScheme67.signLayers hash secretKey rest
            (base + height) tree
            (GroupedBalancedUpperTree67.build hash secretKey base height
              tree index message).root =
          cachedLayers (GroupedBalancedGraphMonitorSetup67.cache table)
            labels rest (base + height) tree := by
        cases rest with
        | nil => rfl
        | cons nextHeight remainder =>
            have nextPositive : 0 < nextHeight := tailSchedule.1
            have nextBaseBound : base + height < 160 := by
              have later := tailSchedule.2.2.1
              omega
            have treeBound : tree < 2 ^ (160 - (base + height)) :=
              address_bound base height index nextBaseMax indexBound
            have rootAddressBound : tree < 2 ^ (160 - height) :=
              lt_of_lt_of_le treeBound
                (pow_le_pow_right₀ (by decide : 1 ≤ (2 : Nat)) (by omega))
            have nextFinBound : baseFin.val + height < 150 := by omega
            have nextMessage :
                (GroupedBalancedUpperTree67.build hash secretKey base
                  height tree index message).root =
                canonicalMessage labels ⟨baseFin.val + height, nextFinBound⟩
                  (BitVec.ofNat 160 tree) := by
              rw [GroupedBalancedUpperTree67.build_root, ←baseEq]
              exact upper_root_canonical residual secretKey labels baseFin
                height tree heightPositive heightMax nextFinBound
                alignedFin rootAddressBound
            exact ih (base + height) tree
              (GroupedBalancedUpperTree67.build hash secretKey base height
                tree index message).root tailSchedule (by omega)
              treeBound (fun _ =>
                ⟨⟨baseFin.val + height, nextFinBound⟩,
                  by change baseFin.val + height + 10 = base + height; omega,
                  nextMessage⟩)
      change GroupedBalancedScheme67.UpperWitnesses.cons
          (GroupedBalancedUpperTree67.build hash secretKey base height
            tree index message).witness
          (GroupedBalancedScheme67.signLayers hash secretKey rest
            (base + height) tree
            (GroupedBalancedUpperTree67.build hash secretKey base height
              tree index message).root) =
        GroupedBalancedScheme67.UpperWitnesses.cons
          (witnessFromCache (GroupedBalancedGraphMonitorSetup67.cache table)
            cachedBase
            (canonicalMessage labels cachedBase (BitVec.ofNat 160 index))
            height tree index)
          (cachedLayers (GroupedBalancedGraphMonitorSetup67.cache table)
            labels rest (base + height) tree)
      rw [headEq, tailEq]

theorem sign_upper_from_cache_for_index
    (residual : Hash) (secretKey : SecretKey) (labels : Labels)
    (table : PointTable)
    (labelsMatch : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
    (sourceMatch : ∀ base leaf chain,
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        base leaf chain =
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        base leaf chain)
    (index : BitVec 160) :
    GroupedBalancedScheme67.signLayers
      (GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels)
      secretKey GroupedBalancedScheme67.Heights 10
      (GroupedMixedIndex.bottomTree index)
      (GroupedBottomTree.build
        (GroupedBalancedGraphProgrammedReference67.programmedGrouped
          residual secretKey labels)
        secretKey 10 (GroupedMixedIndex.bottomTree index) index.toNat).root =
    cachedLayers (GroupedBalancedGraphMonitorSetup67.cache table)
      labels GroupedBalancedScheme67.Heights 10
      (GroupedMixedIndex.bottomTree index) := by
  let hash := GroupedBalancedGraphProgrammedReference67.programmedGrouped
    residual secretKey labels
  have indexBound : GroupedMixedIndex.bottomTree index < 2 ^ (160 - 10) := by
    change index.toNat / 2 ^ 10 < 2 ^ (160 - 10)
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 10)]
    have factor : 2 ^ (160 - 10) * 2 ^ 10 = 2 ^ 160 := by decide
    rw [factor]
    exact index.isLt
  have incoming :
      (GroupedBottomTree.build hash secretKey 10
        (GroupedMixedIndex.bottomTree index) index.toNat).root =
      canonicalMessage labels ⟨0, by decide⟩
        (BitVec.ofNat 160 (GroupedMixedIndex.bottomTree index)) := by
    rw [GroupedBottomTree.build_root]
    exact bottom_root_canonical residual secretKey labels index
  exact signLayers_from_cache residual secretKey labels table labelsMatch sourceMatch
    GroupedBalancedScheme67.Heights 10 (GroupedMixedIndex.bottomTree index)
    (GroupedBottomTree.build hash secretKey 10
      (GroupedMixedIndex.bottomTree index) index.toNat).root
    heights_schedule (by decide) indexBound
    (fun _ => ⟨⟨0, by decide⟩, rfl, incoming⟩)

theorem programmed_sign_upper_from_cache
    (residual : Hash) (secretKey : SecretKey) (labels : Labels)
    (table : PointTable)
    (labelsMatch : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
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
    let randomizer := Reference.randomizer hash secretKey message
    let index := Reference.indexOf hash message randomizer
    (GroupedBalancedScheme67.sign hash secretKey message).upper =
      cachedLayers (GroupedBalancedGraphMonitorSetup67.cache table)
        labels GroupedBalancedScheme67.Heights 10
        (GroupedMixedIndex.bottomTree index) := by
  simp only [GroupedBalancedScheme67.sign]
  exact sign_upper_from_cache_for_index residual secretKey labels table
    labelsMatch sourceMatch _

end SigGolfCandidate.Hypertree.GroupedBalancedGraphUpperLayersCache67

end

/-! The height-ten bottom witness consists of the newly revealed source seed
and public Merkle siblings already available in the setup cache. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphBottomWitnessCache67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorAuthorization67
open GroupedBalancedGraphProgrammedTree67
open GroupedBalancedGraphUpperWitnessCache67
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
open scoped Classical

theorem bottom_root_position_authorized (labels : Labels)
    (signedBottom : Finset (BitVec 160))
    (height address : Nat) :
    Authorized labels signedBottom
      (.inl (bottomRootPosition height address)) := by
  intro base leaf chain step same
  cases height with
  | zero =>
      have levelEq := congrArg (fun p : Position => p.val.level.val) same
      change (0 : Nat) = base.val + 10 at levelEq
      omega
  | succ height =>
      have tagEq := congrArg (fun p : Position => p.val.tag.val) same
      change (4 : Nat) = 2 at tagEq
      omega

theorem known_bottom_root (table : PointTable)
    (height address : Nat) :
    knownDigest (GroupedBalancedGraphMonitorSetup67.cache table)
      (.inl (bottomRootPosition height address)) =
    truncate (table (.inl (bottomRootPosition height address))) := by
  have covered := GroupedBalancedGraphMonitorSetup67.cache_covers table
    (.inl (bottomRootPosition height address))
    (bottom_root_position_authorized
      (GroupedBalancedGraphMonitorTable67.labelsOf table) ∅ height address)
  simp [knownDigest, covered]

def witnessFromCache (cache : QueryCache PointSpec)
    (index : BitVec 160) (answer : BitVec 256) :
    (height address : Nat) → GroupedBottomTree.Witness height
  | 0, _ => .seed (truncate answer)
  | height + 1, address =>
      if index.toNat / 2 ^ height % 2 = 0 then
        .step (witnessFromCache cache index answer height (2 * address))
          (knownDigest cache
            (.inl (bottomRootPosition height (2 * address + 1))))
      else
        .step (witnessFromCache cache index answer height (2 * address + 1))
          (knownDigest cache
            (.inl (bottomRootPosition height (2 * address))))

private theorem child_bound (height address : Nat)
    (heightBound : height + 1 ≤ 160)
    (addressBound : address < 2 ^ (160 - (height + 1))) :
    2 * address + 1 < 2 ^ (160 - height) := by
  have exponent : 160 - height = 160 - (height + 1) + 1 := by omega
  rw [exponent, pow_succ]
  omega

theorem build_witness_from_cache
    (residual : Hash) (secretKey : SecretKey) (labels : Labels)
    (table : PointTable)
    (labelsMatch : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
    (bottomMatch : ∀ index : BitVec 160,
      (GroupedBalancedGraphReference67.sourceAnswers residual secretKey).bottom index =
        (GroupedBalancedGraphMonitorTable67.privateOf table).bottom index)
    (index : BitVec 160) (height : Nat) :
    ∀ address : Nat, height ≤ 10 → address < 2 ^ (160 - height) →
      GroupedBottomTree.selectedLeafAddress height address index.toNat = index.toNat →
      (GroupedBottomTree.build
        (GroupedBalancedGraphProgrammedReference67.programmedGrouped
          residual secretKey labels)
        secretKey height address index.toNat).witness =
      witnessFromCache (GroupedBalancedGraphMonitorSetup67.cache table)
        index (table (.inr (.inl index))) height address := by
  induction height with
  | zero =>
      intro address heightBound addressBound selected
      have addressEq : address = index.toNat := selected
      subst address
      change GroupedBottomTree.Witness.seed
          (GroupedBottomTree.secret
            (GroupedBalancedGraphProgrammedReference67.programmedGrouped
              residual secretKey labels)
            secretKey index.toNat) =
        GroupedBottomTree.Witness.seed
          (truncate (table (.inr (.inl index))))
      congr 1
      rw [GroupedBalancedGraphProgrammedReference67.programmed_bottom_secret,
        ← GroupedBalancedGraphReference67.bottom_source_value,
        bottomMatch index]
      rfl
  | succ height ih =>
      intro address heightBound addressBound selected
      have childBoundLeft : 2 * address < 2 ^ (160 - height) := by
        exact lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_of_lt
          (child_bound height address (by omega) addressBound))
      have childBoundRight : 2 * address + 1 < 2 ^ (160 - height) :=
        child_bound height address (by omega) addressBound
      by_cases bit : index.toNat / 2 ^ height % 2 = 0
      · have selectedLeft :
            GroupedBottomTree.selectedLeafAddress height (2 * address)
              index.toNat = index.toNat := by
          simpa only [GroupedBottomTree.selectedLeafAddress, if_pos bit] using selected
        simp only [GroupedBottomTree.build, witnessFromCache, if_pos bit]
        congr 1
        · exact ih (2 * address) (by omega) childBoundLeft selectedLeft
        · rw [GroupedBottomTree.build_root,
            GroupedBalancedGraphProgrammedTree67.programmed_bottom_root
              residual secretKey labels height (2 * address + 1)
              (by omega) childBoundRight]
          rw [known_bottom_root]
          simp only [labelsMatch, GroupedBalancedGraphMonitorTable67.labelsOf]
      · have selectedRight :
            GroupedBottomTree.selectedLeafAddress height (2 * address + 1)
              index.toNat = index.toNat := by
          simpa only [GroupedBottomTree.selectedLeafAddress, if_neg bit] using selected
        simp only [GroupedBottomTree.build, witnessFromCache, if_neg bit]
        congr 1
        · exact ih (2 * address + 1) (by omega) childBoundRight selectedRight
        · rw [GroupedBottomTree.build_root,
            GroupedBalancedGraphProgrammedTree67.programmed_bottom_root
              residual secretKey labels height (2 * address)
              (by omega) childBoundLeft]
          rw [known_bottom_root]
          simp only [labelsMatch, GroupedBalancedGraphMonitorTable67.labelsOf]

theorem build_ten_witness_from_cache
    (residual : Hash) (secretKey : SecretKey) (labels : Labels)
    (table : PointTable)
    (labelsMatch : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
    (bottomMatch : ∀ index : BitVec 160,
      (GroupedBalancedGraphReference67.sourceAnswers residual secretKey).bottom index =
        (GroupedBalancedGraphMonitorTable67.privateOf table).bottom index)
    (index : BitVec 160) :
    (GroupedBottomTree.build
      (GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels)
      secretKey 10 (GroupedMixedIndex.bottomTree index) index.toNat).witness =
    witnessFromCache (GroupedBalancedGraphMonitorSetup67.cache table)
      index (table (.inr (.inl index))) 10
      (GroupedMixedIndex.bottomTree index) := by
  have bound : GroupedMixedIndex.bottomTree index < 2 ^ (160 - 10) := by
    change index.toNat / 2 ^ 10 < 2 ^ (160 - 10)
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 10)]
    have factor : 2 ^ (160 - 10) * 2 ^ 10 = 2 ^ 160 := by decide
    rw [factor]
    exact index.isLt
  exact build_witness_from_cache residual secretKey labels table
    labelsMatch bottomMatch index 10 (GroupedMixedIndex.bottomTree index)
    (by decide) bound (GroupedBottomTree.selectedLeafAddress_index 10 index.toNat)

end SigGolfCandidate.Hypertree.GroupedBalancedGraphBottomWitnessCache67
