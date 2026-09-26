import SigGolfCandidate.Hypertree.GroupedBalancedGraphProgrammedTree67
import SigGolfCandidate.Hypertree.GroupedBalancedUpperPathFault67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorOracle67


/-! The earlier WOTS point forced by a changed digest is a private zero point
or a planted public chain label in the direct 67-chain graph. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphEarlierExposure67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphProgrammedTree67
abbrev Digest := Reference.Digest

def earlierValue (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (base : Fin 150)
    (leaf : BitVec 160) (chain : Fin 67) (digit : Fin 11) : Digest :=
  if digit.val = 0 then
    GroupedBalancedUpperTree67.secret residual secretKey (base.val + 10) leaf.toNat chain
  else
    truncate (labels (upperChain base leaf chain
      ⟨digit.val - 1, by have := digit.isLt; omega⟩))

theorem point_eq_earlierValue (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (base : Fin 150)
    (leaf : BitVec 160) (chain : Fin 67) (digit : Fin 11) :
    walk (GroupedBalancedUpperTree67.chainHash
      (GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels)
      (base.val + 10) leaf.toNat chain) 0 digit.val
      (GroupedBalancedUpperTree67.secret
        (GroupedBalancedGraphProgrammedReference67.programmedGrouped
          residual secretKey labels)
        secretKey (base.val + 10) leaf.toNat chain) =
      earlierValue residual secretKey labels base leaf chain digit := by
  by_cases zero : digit.val = 0
  · simp only [earlierValue, zero, if_pos, walk]
    exact GroupedBalancedGraphProgrammedReference67.programmed_upper_secret
      residual secretKey labels base leaf chain
  · have positive : 1 ≤ digit.val := by omega
    have countBound : digit.val - 1 < 10 := by have := digit.isLt; omega
    have point := GroupedBalancedGraphProgrammedLeaf67.programmed_upper_walk
      residual secretKey labels base leaf chain (digit.val - 1) countBound
    have countEq : digit.val - 1 + 1 = digit.val := by omega
    rw [countEq] at point
    simpa only [earlierValue, if_neg zero] using point

theorem exposure_eq_graph_point (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (base : Fin 150)
    (leaf : BitVec 160) (signed forged : Digest) {height : Nat}
    (witness : GroupedBalancedUpperTree67.Witness height)
    (exposure : GroupedBalancedUpperPathFault67.EarlierPointExposure
      (GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels)
      secretKey (base.val + 10) leaf.toNat signed forged witness) :
    ∃ chain : Fin 67,
      (GroupedBalancedUpperTree67.digit forged chain).val <
        (GroupedBalancedUpperTree67.digit signed chain).val ∧
      GroupedBalancedUpperIndex67.witnessValues witness chain =
        earlierValue residual secretKey labels base leaf chain
          (GroupedBalancedUpperTree67.digit forged chain) := by
  obtain ⟨chain, earlier, point⟩ := exposure
  exact ⟨chain, earlier, point.trans
    (point_eq_earlierValue residual secretKey labels base leaf chain
      (GroupedBalancedUpperTree67.digit forged chain))⟩

end SigGolfCandidate.Hypertree.GroupedBalancedGraphEarlierExposure67


/-! Static canonical WOTS frontier for direct 67-chain grouped signatures. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorAuthorization67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
abbrev Digest := Reference.Digest

def canonicalMessage (labels : GroupedBalancedSecurityGraph67.Labels)
    (base : Fin 150) (leaf : BitVec 160) : Digest :=
  if zero : base.val = 0 then
    truncate (labels (bottomNode ⟨9, by decide⟩ leaf))
  else
    truncate (labels (upperNode ⟨base.val - 1, by omega⟩ leaf))

def threshold (labels : GroupedBalancedSecurityGraph67.Labels)
    (base : Fin 150) (leaf : BitVec 160) (chain : Fin 67) : Nat :=
  (GroupedBalancedUpperTree67.digit (canonicalMessage labels base leaf) chain).val

def Authorized (labels : GroupedBalancedSecurityGraph67.Labels)
    (signedBottom : Finset (BitVec 160)) : Point → Prop
  | .inl position =>
      ∀ base leaf chain step, position = upperChain base leaf chain step →
        threshold labels base leaf chain ≤ step.val + 1
  | .inr (.inl index) => index ∈ signedBottom
  | .inr (.inr (address, chain)) =>
      threshold labels address.1 address.2 chain = 0

def earlierPoint (base : Fin 150) (leaf : BitVec 160)
    (chain : Fin 67) (digit : Fin 11) : Point :=
  if zero : digit.val = 0 then .inr (.inr ((base, leaf), chain))
  else .inl (upperChain base leaf chain
    ⟨digit.val - 1, by have := digit.isLt; omega⟩)

theorem earlier_unauthorized (labels : GroupedBalancedSecurityGraph67.Labels)
    (signedBottom : Finset (BitVec 160))
    (base : Fin 150) (leaf : BitVec 160) (chain : Fin 67)
    (forged : Fin 11)
    (earlier : forged.val < threshold labels base leaf chain) :
    ¬Authorized labels signedBottom
      (earlierPoint base leaf chain forged) := by
  by_cases zero : forged.val = 0
  · simp only [earlierPoint, dif_pos zero, Authorized]
    omega
  · simp only [earlierPoint, dif_neg zero, Authorized]
    intro authorized
    have bound := authorized base leaf chain
      ⟨forged.val - 1, by have := forged.isLt; omega⟩ rfl
    change threshold labels base leaf chain ≤ forged.val - 1 + 1 at bound
    omega

theorem upper_endpoint_authorized
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (signedBottom : Finset (BitVec 160)) (base : Fin 150)
    (leaf : BitVec 160) (chain : Fin 67) :
    Authorized labels signedBottom
      (.inl (upperChain base leaf chain (endpointStep chain))) := by
  intro otherBase otherLeaf otherChain otherStep same
  have chainEq := congrArg (fun p : Position => p.val.chain.val) same
  have stepEq := congrArg (fun p : Position => p.val.step.val) same
  change chain.val = otherChain.val at chainEq
  have sameChain : chain = otherChain := Fin.ext chainEq
  subst otherChain
  change (endpointStep chain).val = otherStep.val at stepEq
  have bound := GroupedBalancedChecksum67.digit_le_max
    (canonicalMessage labels otherBase otherLeaf) chain
  rw [← stepEq]
  change (GroupedBalancedChecksum67.digit
    (canonicalMessage labels otherBase otherLeaf) chain).val ≤
    GroupedBalancedChecksum67.maxDigit chain - 1 + 1
  have positive := max_digit_positive chain
  omega

theorem upperChain_injective (base otherBase : Fin 150)
    (leaf otherLeaf : BitVec 160) (chain otherChain : Fin 67)
    (step otherStep : Fin 10)
    (same : upperChain base leaf chain step =
      upperChain otherBase otherLeaf otherChain otherStep) :
    base = otherBase ∧ leaf = otherLeaf ∧
      chain = otherChain ∧ step = otherStep := by
  have levelEq := congrArg (fun p : Position => p.val.level.val) same
  have treeEq := congrArg (fun p : Position => p.val.tree.toNat) same
  have chainEq := congrArg (fun p : Position => p.val.chain.val) same
  have stepEq := congrArg (fun p : Position => p.val.step.val) same
  have baseSame : base = otherBase := by
    apply Fin.ext
    change base.val + 10 = otherBase.val + 10 at levelEq
    omega
  have leafSame : leaf = otherLeaf := by
    apply BitVec.eq_of_toNat_eq
    change (BitVec.ofNat 192 leaf.toNat).toNat =
      (BitVec.ofNat 192 otherLeaf.toNat).toNat at treeEq
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (GroupedBottomIndex.index_fits_tree_field leaf),
      BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (GroupedBottomIndex.index_fits_tree_field otherLeaf)] at treeEq
    exact treeEq
  have chainSame : chain = otherChain := Fin.ext (by
    change chain.val = otherChain.val at chainEq
    exact chainEq)
  have stepSame : step = otherStep := Fin.ext (by
    change step.val = otherStep.val at stepEq
    exact stepEq)
  exact ⟨baseSame, leafSame, chainSame, stepSame⟩

theorem canonical_signature_point_authorized
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (signedBottom : Finset (BitVec 160))
    (base : Fin 150) (leaf : BitVec 160) (chain : Fin 67) :
    Authorized labels signedBottom
      (earlierPoint base leaf chain
        (GroupedBalancedUpperTree67.digit (canonicalMessage labels base leaf) chain)) := by
  let digit := GroupedBalancedUpperTree67.digit
    (canonicalMessage labels base leaf) chain
  change Authorized labels signedBottom (earlierPoint base leaf chain digit)
  by_cases zero : digit.val = 0
  · simp only [earlierPoint, dif_pos zero, Authorized]
    change threshold labels base leaf chain = 0
    exact zero
  · simp only [earlierPoint, dif_neg zero, Authorized]
    intro otherBase otherLeaf otherChain otherStep same
    obtain ⟨baseEq, leafEq, chainEq, stepEq⟩ :=
      upperChain_injective base otherBase leaf otherLeaf chain otherChain
        ⟨digit.val - 1, by have := digit.isLt; omega⟩ otherStep same
    subst otherBase
    subst otherLeaf
    subst otherChain
    subst otherStep
    change threshold labels base leaf chain ≤ digit.val - 1 + 1
    have thresholdEq : threshold labels base leaf chain = digit.val := rfl
    omega

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorAuthorization67
