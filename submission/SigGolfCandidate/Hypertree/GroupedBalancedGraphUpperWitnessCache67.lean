import SigGolfCandidate.Hypertree.GroupedBalancedGraphSignExposure67

/-! The honest upper authentication witness is determined by the setup cache:
the selected WOTS values are canonical frontier points, and every sibling is
a public leaf or node label. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphUpperWitnessCache67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorAuthorization67
open GroupedBalancedGraphProgrammedTree67
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
open scoped Classical

def knownDigest (cache : QueryCache PointSpec) (point : Point) : Reference.Digest :=
  truncate ((cache point).getD 0)

theorem root_position_authorized (labels : Labels)
    (signedBottom : Finset (BitVec 160)) (base : Fin 150)
    (height address : Nat) :
    Authorized labels signedBottom
      (.inl (upperRootPosition base height address)) := by
  intro otherBase otherLeaf otherChain otherStep same
  have tagEq := congrArg (fun p : Position => p.val.tag.val) same
  cases height with
  | zero =>
      change (3 : Nat) = 2 at tagEq
      omega
  | succ height =>
      change (4 : Nat) = 2 at tagEq
      omega

theorem known_root (table : PointTable) (base : Fin 150)
    (height address : Nat) :
    knownDigest (GroupedBalancedGraphMonitorSetup67.cache table)
      (.inl (upperRootPosition base height address)) =
    truncate (table (.inl (upperRootPosition base height address))) := by
  have covered := GroupedBalancedGraphMonitorSetup67.cache_covers table
    (.inl (upperRootPosition base height address))
    (root_position_authorized
      (GroupedBalancedGraphMonitorTable67.labelsOf table) ∅ base height address)
  simp [knownDigest, covered]

def witnessFromCache (cache : QueryCache PointSpec)
    (base : Fin 150) (message : Reference.Digest) :
    (height address index : Nat) → GroupedBalancedUpperTree67.Witness height
  | 0, _, index =>
      .leaf (fun chain => knownDigest cache
        (earlierPoint base (BitVec.ofNat 160 index) chain
          (GroupedBalancedUpperTree67.digit message chain)))
  | height + 1, address, index =>
      if index / 2 ^ height % 2 = 0 then
        .step (witnessFromCache cache base message height (2 * address) index)
          (knownDigest cache
            (.inl (upperRootPosition base height (2 * address + 1))))
      else
        .step (witnessFromCache cache base message height (2 * address + 1) index)
          (knownDigest cache
            (.inl (upperRootPosition base height (2 * address))))

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
    (sourceMatch : ∀ base leaf chain,
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        base leaf chain =
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        base leaf chain)
    (base : Fin 150) (message : Reference.Digest)
    (height : Nat) :
    ∀ (address index : Nat), height ≤ 4 → base.val + height ≤ 150 →
      (∀ offset < height,
        GroupedBalancedGraphPayload67.groupBase
          (base.val + 10 + offset) = base.val + 10) →
      address < 2 ^ (160 - height) →
      GroupedBottomTree.selectedLeafAddress height address index = index →
      index < 2 ^ 160 →
      message = canonicalMessage labels base (BitVec.ofNat 160 index) →
      (GroupedBalancedUpperTree67.build
        (GroupedBalancedGraphProgrammedReference67.programmedGrouped
          residual secretKey labels)
        secretKey (base.val + 10) height address index message).witness =
      witnessFromCache (GroupedBalancedGraphMonitorSetup67.cache table)
        base message height address index := by
  induction height with
  | zero =>
      intro address index heightBound levelBound aligned addressBound selected indexBound messageEq
      have addressEq : address = index := selected
      subst address
      change GroupedBalancedUpperTree67.Witness.leaf
          (GroupedBalancedUpperTree67.signValues
            (GroupedBalancedGraphProgrammedReference67.programmedGrouped
              residual secretKey labels)
            secretKey (base.val + 10) index message) =
        GroupedBalancedUpperTree67.Witness.leaf (fun chain =>
          knownDigest (GroupedBalancedGraphMonitorSetup67.cache table)
            (earlierPoint base (BitVec.ofNat 160 index) chain
              (GroupedBalancedUpperTree67.digit message chain)))
      congr 1
      funext chain
      rw [messageEq]
      have fragment :=
        GroupedBalancedGraphSignDisclosure67.programmed_upper_fragment_at_point
          residual secretKey labels table labelsMatch sourceMatch
          base (BitVec.ofNat 160 index) chain
      have roundtrip : (BitVec.ofNat 160 index).toNat = index := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexBound]
      let point := earlierPoint base (BitVec.ofNat 160 index) chain
        (GroupedBalancedUpperTree67.digit
          (canonicalMessage labels base (BitVec.ofNat 160 index)) chain)
      have allowed : Authorized
          (GroupedBalancedGraphMonitorTable67.labelsOf table) ∅ point := by
        rw [← labelsMatch]
        exact canonical_signature_point_authorized labels ∅ base
          (BitVec.ofNat 160 index) chain
      have covered := GroupedBalancedGraphMonitorSetup67.cache_covers table
        point allowed
      have known : knownDigest (GroupedBalancedGraphMonitorSetup67.cache table)
          point = truncate (table point) := by
        simp only [knownDigest, covered, Option.getD_some]
      rw [known]
      simpa only [roundtrip, point] using fragment
  | succ height ih =>
      intro address index heightBound levelBound aligned addressBound selected indexBound messageEq
      have childBoundLeft : 2 * address < 2 ^ (160 - height) := by
        exact lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_of_lt
          (child_bound height address (by omega) addressBound))
      have childBoundRight : 2 * address + 1 < 2 ^ (160 - height) :=
        child_bound height address (by omega) addressBound
      have alignedChild : ∀ offset < height,
          GroupedBalancedGraphPayload67.groupBase
            (base.val + 10 + offset) = base.val + 10 := by
        intro offset bound
        exact aligned offset (by omega)
      by_cases bit : index / 2 ^ height % 2 = 0
      · have selectedLeft :
            GroupedBottomTree.selectedLeafAddress height (2 * address) index = index := by
          simpa only [GroupedBottomTree.selectedLeafAddress, if_pos bit] using selected
        simp only [GroupedBalancedUpperTree67.build, witnessFromCache, if_pos bit]
        congr 1
        · exact ih (2 * address) index (by omega) (by omega)
            alignedChild childBoundLeft selectedLeft indexBound messageEq
        · rw [GroupedBalancedGraphProgrammedTree67.programmed_upper_root
            residual secretKey labels base height (2 * address + 1)
            (by omega) (by omega) alignedChild childBoundRight]
          rw [known_root]
          simp only [labelsMatch, GroupedBalancedGraphMonitorTable67.labelsOf]

      · have selectedRight :
            GroupedBottomTree.selectedLeafAddress height (2 * address + 1) index = index := by
          simpa only [GroupedBottomTree.selectedLeafAddress, if_neg bit] using selected
        simp only [GroupedBalancedUpperTree67.build, witnessFromCache, if_neg bit]
        congr 1
        · exact ih (2 * address + 1) index (by omega) (by omega)
            alignedChild childBoundRight selectedRight indexBound messageEq
        · rw [GroupedBalancedGraphProgrammedTree67.programmed_upper_root
            residual secretKey labels base height (2 * address)
            (by omega) (by omega) alignedChild childBoundLeft]
          rw [known_root]
          simp only [labelsMatch, GroupedBalancedGraphMonitorTable67.labelsOf]

theorem build_witness_from_cache_at_index
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
    (base : Fin 150) (message : Reference.Digest)
    (height index : Nat)
    (heightBound : height ≤ 4) (levelBound : base.val + height ≤ 150)
    (aligned : ∀ offset < height,
      GroupedBalancedGraphPayload67.groupBase
        (base.val + 10 + offset) = base.val + 10)
    (indexBound : index < 2 ^ 160)
    (messageEq : message = canonicalMessage labels base (BitVec.ofNat 160 index)) :
    (GroupedBalancedUpperTree67.build
      (GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels)
      secretKey (base.val + 10) height (index / 2 ^ height) index message).witness =
    witnessFromCache (GroupedBalancedGraphMonitorSetup67.cache table)
      base message height (index / 2 ^ height) index := by
  have addressBound : index / 2 ^ height < 2 ^ (160 - height) := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos (by decide) _)]
    have exponent : 160 - height + height = 160 := by omega
    rw [← pow_add, exponent]
    exact indexBound
  exact build_witness_from_cache residual secretKey labels table
    labelsMatch sourceMatch base message height
    (index / 2 ^ height) index heightBound levelBound aligned addressBound
    (GroupedBottomTree.selectedLeafAddress_index height index) indexBound messageEq

end SigGolfCandidate.Hypertree.GroupedBalancedGraphUpperWitnessCache67
