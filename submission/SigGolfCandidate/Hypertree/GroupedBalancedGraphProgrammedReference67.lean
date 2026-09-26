import SigGolfCandidate.Hypertree.GroupedBalancedGraphReference67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphProgramming67

/-! Planting grouped public graph labels leaves the actual bottom, paired
upper, and nonce derivations unchanged. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphProgrammedReference67
open SigGolf SigGolfCandidate.Hypertree Reference

noncomputable def programmedGrouped (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) : Hash :=
  GroupedBalancedGraphProgramming67.programmed
    (GroupedBalancedGraphPayload67.payload
      (GroupedBalancedGraphReference67.sourceAnswers residual secretKey) labels)
    labels residual

theorem programmed_bottom_secret (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (index : BitVec 160) :
    GroupedBottomTree.secret (programmedGrouped residual secretKey labels)
      secretKey index.toNat =
      GroupedBottomTree.secret residual secretKey index.toNat := by
  change truncate (programmedGrouped residual secretKey labels
    (GroupedBalancedPrivateDerivation67.input secretKey (.bottom index))) = _
  rw [programmedGrouped, GroupedBalancedGraphProgramming67.programmed_private]
  rfl

theorem programmed_upper_pair (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (base : Fin 150)
    (leaf : BitVec 160) (pair : Fin 34) :
    GroupedBalancedUpperTree67.secretPair (programmedGrouped residual secretKey labels)
      secretKey (base.val + 10) leaf.toNat pair.val =
      GroupedBalancedUpperTree67.secretPair residual secretKey
        (base.val + 10) leaf.toNat pair.val := by
  change programmedGrouped residual secretKey labels
      (GroupedBalancedPrivateDerivation67.input secretKey (.upper base leaf pair)) = _
  rw [programmedGrouped, GroupedBalancedGraphProgramming67.programmed_private]
  rfl

theorem programmed_upper_secret (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (base : Fin 150)
    (leaf : BitVec 160) (chain : Fin 67) :
    GroupedBalancedUpperTree67.secret (programmedGrouped residual secretKey labels)
      secretKey (base.val + 10) leaf.toNat chain =
      GroupedBalancedUpperTree67.secret residual secretKey
        (base.val + 10) leaf.toNat chain := by
  unfold GroupedBalancedUpperTree67.secret
  rw [show chain.val / 2 = (⟨chain.val / 2, by have := chain.isLt; omega⟩ : Fin 34).val
    from rfl]
  rw [programmed_upper_pair residual secretKey labels base leaf]

theorem programmed_randomizer (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (message : Message) :
    Reference.randomizer (programmedGrouped residual secretKey labels)
      secretKey message =
      Reference.randomizer residual secretKey message := by
  change programmedGrouped residual secretKey labels
      (GroupedBalancedPrivateDerivation67.input secretKey (.randomizer message)) = _
  rw [programmedGrouped, GroupedBalancedGraphProgramming67.programmed_private]
  rfl

end SigGolfCandidate.Hypertree.GroupedBalancedGraphProgrammedReference67
