import SigGolfCandidate.Hypertree.GroupedBalancedGraphOracle67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorTable67
import SigGolfCandidate.Hypertree.GroupedBalancedQueryClasses67
import SigGolfCandidate.Hypertree.SecurityGameHop

/-! A sampled direct67 public graph cache is disjoint from every legacy
private derivation input. It can therefore initialize both sides of the old
secret-key separation coupling. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPlantedCache67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorTable67
open GroupedBalancedGraphOracle67
open SecurityDerivation SecuritySeparation
set_option backward.isDefEq.respectTransparency false
open scoped Classical

noncomputable def planted (table : PointTable) : QueryCache HashSpec :=
  embed (privateOf table) (labelsOf table) ∅

theorem planted_private_none (table : PointTable)
    (secretKey : SecretKey) (slot : SecurityDerivation.Slot) :
    planted table (SecurityDerivation.input secretKey slot) = none := by
  rw [planted, embed_lookup]
  have absent := GroupedBalancedQueryClasses67.legacy_eligible_locate_none
    (SecurityDerivation.input secretKey slot)
    (SecuritySeparation.secretKeyEligible_input secretKey slot)
  simp [GroupedBalancedGraphOracle67.canonical, absent]

theorem planted_related (table : PointTable) (secretKey : SecretKey) :
    Related secretKey (planted table) (∅, planted table) := by
  constructor
  · intro slot
    simp only [planted_private_none]
    rfl
  · intro query _
    rfl

#print axioms planted_private_none
#print axioms planted_related

end SigGolfCandidate.Hypertree.GroupedBalancedPlantedCache67
