import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorExposure67
import SigGolfCandidate.Hypertree.GroupedBalancedUpperIndex67


/-! One honest direct 67-chain WOTS leaf discloses exactly its canonical
frontier point for each chain. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphSignDisclosure67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorAuthorization67
abbrev Digest := Reference.Digest

def upperPoints (labels : GroupedBalancedSecurityGraph67.Labels)
    (base : Fin 150) (leaf : BitVec 160) : List Point :=
  List.ofFn (fun chain : Fin 67 =>
    earlierPoint base leaf chain
      (GroupedBalancedUpperTree67.digit
        (canonicalMessage labels base leaf) chain))

theorem upperPoints_authorized
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (signedBottom : Finset (BitVec 160))
    (base : Fin 150) (leaf : BitVec 160)
    (point : Point) (member : point ∈ upperPoints labels base leaf) :
    Authorized labels signedBottom point := by
  obtain ⟨chain, same⟩ := List.mem_ofFn.mp member
  rw [← same]
  exact canonical_signature_point_authorized
    labels signedBottom base leaf chain

theorem programmed_upper_fragment_at_point
    (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (table : PointTable)
    (labelsMatch : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
    (sourceMatch : ∀ base leaf chain,
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        base leaf chain =
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        base leaf chain)
    (base : Fin 150) (leaf : BitVec 160) (chain : Fin 67) :
    (GroupedBalancedUpperTree67.signValues
      (GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels)
      secretKey (base.val + 10) leaf.toNat
      (canonicalMessage labels base leaf)) chain =
    truncate (table (earlierPoint base leaf chain
      (GroupedBalancedUpperTree67.digit
        (canonicalMessage labels base leaf) chain))) := by
  rw [GroupedBalancedGraphProgrammedTree67.programmed_upper_sign_fragment]
  exact GroupedBalancedGraphMonitorExposure67.earlierValue_eq_table
    residual secretKey labels table labelsMatch sourceMatch
    base leaf chain
    (GroupedBalancedUpperTree67.digit
      (canonicalMessage labels base leaf) chain)

theorem bottom_source_authorized
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (signedBottom : Finset (BitVec 160)) (index : BitVec 160)
    (member : index ∈ signedBottom) :
    Authorized labels signedBottom (.inr (.inl index)) := member

end SigGolfCandidate.Hypertree.GroupedBalancedGraphSignDisclosure67



/-! The output root of each planted tree is the fixed incoming digest for
the next direct 67-chain group at that tree address. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphCanonicalRoot67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67
open GroupedBalancedGraphProgrammedReference67
open GroupedBalancedGraphProgrammedTree67
open GroupedBalancedGraphMonitorAuthorization67
set_option maxRecDepth 8192

theorem bottom_root_canonical (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (index : BitVec 160) :
    GroupedBottomTree.root (programmedGrouped residual secretKey labels)
      secretKey 10 (index.toNat / 2 ^ 10) =
    canonicalMessage labels ⟨0, by decide⟩
      (BitVec.ofNat 160 (index.toNat / 2 ^ 10)) := by
  have addressBound : index.toNat / 2 ^ 10 < 2 ^ (160 - 10) := by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 10)]
    have factor : 2 ^ (160 - 10) * 2 ^ 10 = 2 ^ 160 := by decide
    rw [factor]
    exact index.isLt
  rw [programmed_bottom_root residual secretKey labels 10
    (index.toNat / 2 ^ 10) (by decide) addressBound]
  simp [bottomRootPosition, canonicalMessage, Fin.ofNat]

theorem upper_root_canonical (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (base : Fin 150) (height address : Nat)
    (positive : 0 < height) (heightBound : height ≤ 4)
    (nextBaseBound : base.val + height < 150)
    (aligned : ∀ offset < height,
      GroupedBalancedGraphPayload67.groupBase
        (base.val + 10 + offset) = base.val + 10)
    (addressBound : address < 2 ^ (160 - height)) :
    GroupedBalancedUpperTree67.root
      (programmedGrouped residual secretKey labels)
      secretKey (base.val + 10) height address =
    canonicalMessage labels ⟨base.val + height, nextBaseBound⟩
      (BitVec.ofNat 160 address) := by
  rw [programmed_upper_root residual secretKey labels base height address
    heightBound (by omega) aligned addressBound]
  cases height with
  | zero => omega
  | succ prior =>
      have notZero : ¬base.val + (prior + 1) = 0 := by omega
      simp only [upperRootPosition, canonicalMessage, dif_neg notZero]
      have finEq : Fin.ofNat 150 (base.val + prior) =
          (⟨base.val + (prior + 1) - 1, by omega⟩ : Fin 150) := by
        apply Fin.ext
        simp only [Fin.ofNat, Fin.val_mk]
        rw [Nat.mod_eq_of_lt (by omega : base.val + prior < 150)]
        omega
      rw [finEq]

end SigGolfCandidate.Hypertree.GroupedBalancedGraphCanonicalRoot67


/-! The mixed height schedule follows exactly the group bases used by the
programmed graph. This certificate also tracks the address and digest passed
between successive honest signing groups. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphSignHistory67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67
open GroupedBalancedGraphPayload67
open GroupedBalancedGraphMonitorAuthorization67
open GroupedBalancedGraphCanonicalRoot67
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def Schedule : Nat → List Nat → Prop
  | _, [] => True
  | base, height :: rest =>
      0 < height ∧ height ≤ 4 ∧ base + height ≤ 160 ∧
      (∀ offset < height,
        GroupedBalancedGraphPayload67.groupBase (base + offset) = base) ∧
      Schedule (base + height) rest

theorem schedule_high (group count : Nat) (bound : group + count ≤ 15)
    (rest : List Nat)
    (tail : Schedule (100 + 4 * (group + count)) rest) :
    Schedule (100 + 4 * group) (List.replicate count 4 ++ rest) := by
  induction count generalizing group with
  | zero => simpa using tail
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append, Schedule]
      refine ⟨by decide, by decide, by omega, ?_, ?_⟩
      · intro offset offsetBound
        exact groupBase_high group offset (by omega) offsetBound
      · have next : 100 + 4 * group + 4 = 100 + 4 * (group + 1) := by omega
        rw [next]
        apply ih (group + 1) (by omega)
        simpa only [show group + 1 + count = group + (count + 1) by omega] using tail

theorem schedule_low (group count : Nat) (bound : group + count ≤ 30)
    (rest : List Nat)
    (tail : Schedule (10 + 3 * (group + count)) rest) :
    Schedule (10 + 3 * group) (List.replicate count 3 ++ rest) := by
  induction count generalizing group with
  | zero => simpa using tail
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append, Schedule]
      refine ⟨by decide, by decide, by omega, ?_, ?_⟩
      · intro offset offsetBound
        exact groupBase_low group offset (by omega) offsetBound
      · have next : 10 + 3 * group + 3 = 10 + 3 * (group + 1) := by omega
        rw [next]
        apply ih (group + 1) (by omega)
        simpa only [show group + 1 + count = group + (count + 1) by omega] using tail

theorem heights_schedule : Schedule 10 GroupedBalancedScheme67.Heights := by
  change Schedule 10 (List.replicate 30 3 ++ List.replicate 15 4)
  have high : Schedule 100 (List.replicate 15 4) := by
    simpa using schedule_high 0 15 (by decide) [] (by simp [Schedule])
  simpa only [show 10 + 3 * 0 = 10 by decide,
    show 10 + 3 * (0 + 30) = 100 by decide] using
    schedule_low 0 30 (by decide) (List.replicate 15 4) high

def CanonicalWitnesses (labels : Labels) (table : GroupedBalancedGraphPassive67.PointTable) :
    (heights : List Nat) → (base index : Nat) →
      GroupedBalancedScheme67.UpperWitnesses heights → Prop
  | [], _, _, .nil => True
  | height :: rest, base, index, .cons head tail =>
      (∃ (baseFin : Fin 150), baseFin.val + 10 = base ∧
        ∀ chain : Fin 67,
          GroupedBalancedUpperIndex67.witnessValues head chain =
            truncate (table (earlierPoint baseFin (BitVec.ofNat 160 index) chain
              (GroupedBalancedUpperTree67.digit
                (canonicalMessage labels baseFin (BitVec.ofNat 160 index)) chain)))) ∧
      CanonicalWitnesses labels table rest (base + height) (index / 2 ^ height) tail

theorem address_bound (base height index : Nat)
    (baseHeight : base + height ≤ 160)
    (bound : index < 2 ^ (160 - base)) :
    index / 2 ^ height < 2 ^ (160 - (base + height)) := by
  rw [Nat.div_lt_iff_lt_mul (pow_pos (by decide) _)]
  have exponents : 160 - (base + height) + height = 160 - base := by omega
  rw [← pow_add, exponents]
  exact bound

theorem bitvec_roundtrip (base index : Nat) (baseBound : base ≤ 160)
    (bound : index < 2 ^ (160 - base)) :
    (BitVec.ofNat 160 index).toNat = index := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact lt_of_lt_of_le bound
    (pow_le_pow_right₀ (by decide : 1 ≤ (2 : Nat)) (Nat.sub_le 160 base))

theorem signLayers_canonical
    (residual : Hash) (secretKey : SecretKey) (labels : Labels)
    (table : GroupedBalancedGraphPassive67.PointTable)
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
      heights ≠ [] → Schedule base heights → 10 ≤ base → base < 160 →
      index < 2 ^ (160 - base) →
      (∃ baseFin : Fin 150, baseFin.val + 10 = base ∧
        message = canonicalMessage labels baseFin (BitVec.ofNat 160 index)) →
      CanonicalWitnesses labels table heights base index
        (GroupedBalancedScheme67.signLayers
          (GroupedBalancedGraphProgrammedReference67.programmedGrouped
            residual secretKey labels)
          secretKey heights base index message) := by
  induction heights with
  | nil =>
      intro base index message nonempty
      exact False.elim (nonempty rfl)
  | cons height rest ih =>
      intro base index message nonempty schedule baseMin baseMax indexBound incoming
      obtain ⟨baseFin, baseEq, messageEq⟩ := incoming
      obtain ⟨heightPositive, heightMax, nextBaseMax, aligned, tailSchedule⟩ := schedule
      let hash := GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels
      let tree := index / 2 ^ height
      have valueEq : ∀ chain : Fin 67,
          GroupedBalancedUpperIndex67.witnessValues
            (GroupedBalancedUpperTree67.build hash secretKey base height tree index message).witness
              chain =
          truncate (table (earlierPoint baseFin (BitVec.ofNat 160 index) chain
            (GroupedBalancedUpperTree67.digit
              (canonicalMessage labels baseFin (BitVec.ofNat 160 index)) chain))) := by
        intro chain
        rw [GroupedBalancedUpperIndex67.build_witness_values_at_index,
          messageEq]
        have indexRoundtrip := bitvec_roundtrip base index (by omega) indexBound
        simpa only [baseEq, indexRoundtrip] using
          (GroupedBalancedGraphSignDisclosure67.programmed_upper_fragment_at_point
            residual secretKey labels table labelsMatch sourceMatch
            baseFin (BitVec.ofNat 160 index) chain)
      change (∃ baseFin : Fin 150, baseFin.val + 10 = base ∧
          ∀ chain : Fin 67,
            GroupedBalancedUpperIndex67.witnessValues
              (GroupedBalancedUpperTree67.build hash secretKey base height tree index message).witness
                chain =
            truncate (table (earlierPoint baseFin (BitVec.ofNat 160 index) chain
              (GroupedBalancedUpperTree67.digit
                (canonicalMessage labels baseFin (BitVec.ofNat 160 index)) chain)))) ∧
        CanonicalWitnesses labels table rest (base + height) tree
          (GroupedBalancedScheme67.signLayers hash secretKey rest (base + height) tree
            (GroupedBalancedUpperTree67.build hash secretKey base height tree index message).root)
      constructor
      · exact ⟨baseFin, baseEq, valueEq⟩
      · cases rest with
        | nil => trivial
        | cons nextHeight remainder =>
            have nextPositive : 0 < nextHeight := tailSchedule.1
            have nextMax : base + height < 160 := by
              have nextScheduleBound := tailSchedule.2.2.1
              omega
            have treeBound : tree < 2 ^ (160 - (base + height)) :=
              address_bound base height index nextBaseMax indexBound
            have upperAddressBound : tree < 2 ^ (160 - height) :=
              lt_of_lt_of_le treeBound
                (pow_le_pow_right₀ (by decide : 1 ≤ (2 : Nat)) (by omega))
            have nextFinBound : baseFin.val + height < 150 := by omega
            have alignedFin : ∀ offset < height,
                GroupedBalancedGraphPayload67.groupBase
                  (baseFin.val + 10 + offset) = baseFin.val + 10 := by
              simpa only [baseEq] using aligned
            have nextMessage :
                (GroupedBalancedUpperTree67.build hash secretKey base height tree index message).root =
                canonicalMessage labels ⟨baseFin.val + height, nextFinBound⟩
                  (BitVec.ofNat 160 tree) := by
              rw [GroupedBalancedUpperTree67.build_root]
              rw [← baseEq]
              exact upper_root_canonical residual secretKey labels baseFin height tree
                heightPositive heightMax nextFinBound alignedFin upperAddressBound
            have nextBaseFin :
                (⟨baseFin.val + height, nextFinBound⟩ : Fin 150).val + 10 =
                  base + height := by
              change baseFin.val + height + 10 = base + height
              omega
            exact ih (base + height) tree
              (GroupedBalancedUpperTree67.build hash secretKey base height tree index message).root
              (by simp) tailSchedule (by omega) nextMax treeBound
              ⟨⟨baseFin.val + height, nextFinBound⟩, nextBaseFin, nextMessage⟩

theorem sign_upper_for_index
    (residual : Hash) (secretKey : SecretKey) (labels : Labels)
    (table : GroupedBalancedGraphPassive67.PointTable)
    (labelsMatch : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
    (sourceMatch : ∀ base leaf chain,
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        base leaf chain =
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        base leaf chain)
    (index : BitVec 160) :
    CanonicalWitnesses labels table GroupedBalancedScheme67.Heights 10
      (GroupedMixedIndex.bottomTree index)
      (GroupedBalancedScheme67.signLayers
        (GroupedBalancedGraphProgrammedReference67.programmedGrouped
          residual secretKey labels)
        secretKey GroupedBalancedScheme67.Heights 10
        (GroupedMixedIndex.bottomTree index)
        (GroupedBottomTree.build
          (GroupedBalancedGraphProgrammedReference67.programmedGrouped
            residual secretKey labels)
          secretKey 10 (GroupedMixedIndex.bottomTree index) index.toNat).root) := by
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
  exact signLayers_canonical residual secretKey labels table labelsMatch sourceMatch
    GroupedBalancedScheme67.Heights 10 (GroupedMixedIndex.bottomTree index)
    (GroupedBottomTree.build hash secretKey 10
      (GroupedMixedIndex.bottomTree index) index.toNat).root
    (by decide) heights_schedule (by decide) (by decide) indexBound
    ⟨⟨0, by decide⟩, rfl, incoming⟩

theorem programmed_sign_upper_canonical
    (residual : Hash) (secretKey : SecretKey) (labels : Labels)
    (table : GroupedBalancedGraphPassive67.PointTable)
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
    CanonicalWitnesses labels table GroupedBalancedScheme67.Heights 10
      (GroupedMixedIndex.bottomTree index)
      (GroupedBalancedScheme67.sign hash secretKey message).upper := by
  simp only [GroupedBalancedScheme67.sign]
  exact sign_upper_for_index residual secretKey labels table
    labelsMatch sourceMatch _

theorem programmed_sign_bottom_seed
    (residual : Hash) (secretKey : SecretKey) (labels : Labels)
    (table : GroupedBalancedGraphPassive67.PointTable)
    (bottomMatch : ∀ index : BitVec 160,
      (GroupedBalancedGraphReference67.sourceAnswers residual secretKey).bottom index =
        (GroupedBalancedGraphMonitorTable67.privateOf table).bottom index)
    (index : BitVec 160) :
    (GroupedBottomTree.build
      (GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels)
      secretKey 10 (GroupedMixedIndex.bottomTree index) index.toNat).witness.seedValue =
      truncate (table (.inr (.inl index))) := by
  rw [GroupedBalancedGraphProgrammedTree67.programmed_bottom_sign_seed]
  rw [← GroupedBalancedGraphReference67.bottom_source_value]
  rw [bottomMatch index]
  rfl

end SigGolfCandidate.Hypertree.GroupedBalancedGraphSignHistory67
