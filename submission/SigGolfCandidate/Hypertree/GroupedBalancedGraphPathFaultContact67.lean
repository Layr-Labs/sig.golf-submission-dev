import SigGolfCandidate.Hypertree.GroupedBalancedGraphMerkleBadContact67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphWotsContact67
import SigGolfCandidate.Hypertree.GroupedBalancedUpperPathFault67
import SigGolfCandidate.Hypertree.GroupedBalancedMixedPathFault67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphSignHistory67


/-! Any concrete upper-path collision fault in a direct67 group is a monitored
public output contact. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphUpperFaultContact67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67
open GroupedBalancedGraphProgrammedReference67
open GroupedBalancedUpperPathFault67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem upper_fault_contact
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
        ((programmedGrouped residual secretKey labels) query) := by
  rcases bad with merkle | wots
  · have addressBound : index / 2 ^ height < 2 ^ (160 - height) := by
      rw [Nat.div_lt_iff_lt_mul (pow_pos (by decide) _)]
      have exponent : 160 - height + height = 160 := by omega
      rw [← pow_add, exponent]
      exact indexBound
    exact GroupedBalancedGraphMerkleBadContact67.bad_contact table
      residual secretKey labels labelsMatch bottomMatch sourceMatch base
      message height (index / 2 ^ height) index heightBound levelBound
      aligned addressBound witness merkle
  · have leafFits : (BitVec.ofNat 160 index).toNat = index := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt indexBound
    have contact := GroupedBalancedGraphWotsContact67.leaf_collision_contact
      table residual secretKey labels labelsMatch bottomMatch sourceMatch
      base (BitVec.ofNat 160 index) message
      (GroupedBalancedUpperIndex67.witnessValues witness)
      (by simpa only [leafFits] using wots)
    exact contact

end SigGolfCandidate.Hypertree.GroupedBalancedGraphUpperFaultContact67


/-! A fault along any of the 45 upper groups either contacts a planted public
output or yields a strictly earlier canonical WOTS point. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphPathFaultContact67
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

theorem path_fault_contact_or_exposure
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
          ((programmedGrouped residual secretKey labels) query)) ∨
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
            have faultContact :=
              GroupedBalancedGraphUpperFaultContact67.upper_fault_contact
                table residual secretKey labels labelsMatch bottomMatch
                sourceMatch baseFin height index heightMax
                (by dsimp [baseFin]; omega) alignedFin indexFits actual head
                (by simpa only [baseEq, hash] using bad)
            exact Or.inl faultContact
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
            · exact Or.inl contact
            · exact Or.inr (by
                change (expected ≠ actual ∧
                    GroupedBalancedUpperPathFault67.EarlierPointExposure
                      hash secretKey base index expected actual head) ∨
                  EarlierExposure hash secretKey rest (base + height) tree
                    canonicalRoot actualRoot tail
                exact Or.inr exposure)

end SigGolfCandidate.Hypertree.GroupedBalancedGraphPathFaultContact67
