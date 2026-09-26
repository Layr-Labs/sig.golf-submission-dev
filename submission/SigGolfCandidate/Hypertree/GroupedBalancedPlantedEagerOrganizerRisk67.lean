import SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerJointRisk67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphOrganizerView67

/-! Instantiate the common-distribution direct67 risk bound for the actual
organizer's adaptive wire adversary and signing lifetime. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerOrganizerRisk67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleComp.EvalDist OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphIndexJointIndexBudget67
open GroupedBalancedPlantedEagerJointRisk67
open GroupedBalancedPlantedEagerAnnotated67
open GroupedBalancedPlantedEagerGraphProjection67
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def organizerInteraction (sizes : Sizes)
    (encode : GroupedBalancedScheme67.Signature → Bytes sizes.signature)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (adversary : SigGolf.Adversary sizes)
    (publicCache : Cache) (rounds : Nat) :
    QueryCache PointSpec →
      Interaction (GroupedBalancedGraphOrganizerView67.Result sizes) :=
  fun exposed =>
    let pk := GroupedBalancedGraphMonitorSetupBound67.rootFrom exposed
    GroupedBalancedGraphOrganizerView67.ofInteract sizes
      encode decodeWitness decodeSignature adversary pk rounds
      (adversary.initial pk publicCache) {}

theorem organizer_index_budget (sizes : Sizes)
    (encode : GroupedBalancedScheme67.Signature → Bytes sizes.signature)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (adversary : SigGolf.Adversary sizes)
    (publicCache : Cache) (rounds budget : Nat)
    (answers : SecurityGraphIdeal.PrivateTable)
    (cache : QueryCache PointSpec) :
    IndexBudget LIFETIME
      (viewOf answers
        (organizerInteraction sizes encode decodeWitness decodeSignature
          adversary publicCache rounds) budget cache) := by
  unfold viewOf organizerInteraction
  apply GroupedBalancedIdealEagerCutoffBudget67.eager_cutoff_index
  let pk := GroupedBalancedGraphMonitorSetupBound67.rootFrom cache
  simpa only [Nat.sub_zero] using
    GroupedBalancedGraphSignBudget67.interact_budget sizes
      encode decodeWitness decodeSignature adversary pk rounds
      (adversary.initial pk publicCache) ({} : SigGolf.Transcript sizes)

theorem organizer_combined_risk_le_budget (sizes : Sizes)
    (encode : GroupedBalancedScheme67.Signature → Bytes sizes.signature)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (adversary : SigGolf.Adversary sizes)
    (publicCache : Cache) (rounds budget : Nat) :
    let interaction := organizerInteraction sizes encode decodeWitness
      decodeSignature adversary publicCache rounds
    Pr[fun result => result.1.bad = true ∨
      SecurityIndexTrace.Conflict result.2 |
      annotatedJointGlobal interaction budget] +
    expectedValue (annotatedJointGlobal interaction budget)
      (fun result =>
        (GroupedBalancedGraphIndexJointClassTrace67.secretCount result.1 : ENNReal) /
          (2 : ENNReal) ^ 128) ≤
      (budget : ENNReal) / (2 : ENNReal) ^ 127 := by
  dsimp only
  exact annotated_combined_risk_le_budget _ budget
    (fun answers cache => organizer_index_budget sizes encode decodeWitness
      decodeSignature adversary publicCache rounds budget answers cache)

#print axioms organizer_combined_risk_le_budget

end SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerOrganizerRisk67
