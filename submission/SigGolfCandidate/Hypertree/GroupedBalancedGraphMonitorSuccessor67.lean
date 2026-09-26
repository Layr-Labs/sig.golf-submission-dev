import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSafeReveal67

/-! A canonical chain query moves the static WOTS exposure frontier forward. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSuccessor67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorAuthorization67 GroupedBalancedGraphMonitorPredecessor67

set_option maxRecDepth 4096

theorem predecessor_upper_zero (base : Fin 150) (leaf : BitVec 160)
    (chain : Fin 67) :
    predecessor (upperChain base leaf chain 0).val =
      some (.inr (.inr ((base, leaf), chain))) := by
  simp [predecessor, upperChain,
    show 10 ≤ base.val + 10 by omega,
    show base.val + 10 < 160 by have := base.isLt; omega,
    show chain.val < 67 by exact chain.isLt]
  have treeBound := GroupedBottomIndex.index_fits_tree_field leaf
  norm_num at treeBound
  simp [Nat.mod_eq_of_lt treeBound]

theorem predecessor_upper_positive (base : Fin 150) (leaf : BitVec 160)
    (chain : Fin 67) (step : Fin 10) (positive : 0 < step.val) :
    predecessor (upperChain base leaf chain step).val =
      some (.inl (upperChain base leaf chain
        ⟨step.val - 1, by have := step.isLt; omega⟩)) := by
  simp [predecessor, upperChain, positive,
    show 10 ≤ base.val + 10 by omega,
    show base.val + 10 < 160 by have := base.isLt; omega,
    show chain.val < 67 by exact chain.isLt,
    show step.val < 10 by exact step.isLt]
  have treeBound := GroupedBottomIndex.index_fits_tree_field leaf
  norm_num at treeBound
  have stepNe : step ≠ 0 := by
    intro same
    have := congrArg Fin.val same
    omega
  simp [stepNe, Nat.mod_eq_of_lt treeBound]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt leaf.isLt, Nat.mod_eq_of_lt treeBound]

theorem authorized_after_predecessor
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (signedBottom : Finset (BitVec 160))
    (position : Position) (previous : Point)
    (located : predecessor position.val = some previous)
    (known : Authorized labels signedBottom previous) :
    Authorized labels signedBottom (.inl position) := by
  intro base leaf chain step same
  rw [same] at located
  by_cases zero : step.val = 0
  · have stepEq : step = 0 := Fin.ext zero
    subst step
    rw [predecessor_upper_zero] at located
    have prevEq := Option.some.inj located
    subst previous
    simp only [Authorized] at known
    change threshold labels base leaf chain = 0 at known
    omega
  · have positive : 0 < step.val := by omega
    rw [predecessor_upper_positive base leaf chain step positive] at located
    have prevEq := Option.some.inj located
    subst previous
    have bound := known base leaf chain
      ⟨step.val - 1, by have := step.isLt; omega⟩ rfl
    change threshold labels base leaf chain ≤ step.val - 1 + 1 at bound
    omega

theorem authorized_no_predecessor
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (signedBottom : Finset (BitVec 160))
    (position : Position)
    (absent : predecessor position.val = none) :
    Authorized labels signedBottom (.inl position) := by
  intro base leaf chain step same
  rw [same] at absent
  by_cases zero : step.val = 0
  · have stepEq : step = 0 := Fin.ext zero
    subst step
    rw [predecessor_upper_zero] at absent
    cases absent
  · have positive : 0 < step.val := by omega
    rw [predecessor_upper_positive base leaf chain step positive] at absent
    cases absent

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSuccessor67
