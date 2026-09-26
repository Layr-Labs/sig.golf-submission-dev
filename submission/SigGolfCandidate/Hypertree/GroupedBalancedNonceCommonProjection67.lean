import SigGolfCandidate.Hypertree.GroupedBalancedNonceRisk67
import SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerJointRisk67
import SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerOrganizerRisk67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedNonceReserve67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedNonceCommonProjection67. -/
section
/-! The stopped audit's actual H5 draw count is exactly the index trace
length in the common annotated graph/H5 simulation. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceCostProjection67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphPassive67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem paired_expected_draws_eq {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    expectedValue
      (GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
        interaction budget)
      (fun result => (result.2.1.2.length : ENNReal)) =
    expectedValue
      (GroupedBalancedPlantedEagerAnnotated67.annotatedJointGlobal
        interaction budget)
      (fun result => (result.2.length : ENNReal)) := by
  calc
    _ = expectedValue
      (Prod.snd <$>
        GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
          interaction budget)
      (fun result => (result.1.2.length : ENNReal)) := by
        rw [expectedValue_map]
    _ = expectedValue
      (GroupedBalancedIndexLabeledAudit67.auditedAnnotatedGlobal
        interaction budget)
      (fun result => (result.1.2.length : ENNReal)) := by
        rw [GroupedBalancedIndexLabeledPairedGlobal67.paired_projection]
    _ = expectedValue
      ((fun result => (result.1.1,
        result.1.2.map Prod.snd)) <$>
        GroupedBalancedIndexLabeledAudit67.auditedAnnotatedGlobal
          interaction budget)
      (fun result => (result.2.length : ENNReal)) := by
        rw [expectedValue_map]
        simp only [List.length_map]
    _ = _ := by
      rw [GroupedBalancedIndexLabeledAudit67.audited_annotated_projection]

theorem paired_nonce_hit_le_index_expected {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    Pr[fun result =>
      SecurityMonitorIndexContact.NonceHit
        (fun message => result.1 (.randomizer message))
        (GroupedBalancedIndexLabeledHistory67.history
          result.2.2 result.2.1.2) |
      GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
        interaction budget] ≤
    expectedValue
      (GroupedBalancedPlantedEagerAnnotated67.annotatedJointGlobal
        interaction budget)
      (fun result => (result.2.length : ENNReal)) /
        (2 : ENNReal)^256 := by
  rw [← paired_expected_draws_eq]
  exact GroupedBalancedNonceRisk67.paired_nonce_hit_le_draws
    interaction budget

#print axioms paired_expected_draws_eq
#print axioms paired_nonce_hit_le_index_expected

end SigGolfCandidate.Hypertree.GroupedBalancedNonceCostProjection67


/-! The sharp shared weight already reserves one 256-bit nonce guess for
each H5 draw. This module exposes that reserve in the common distribution. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceReserve67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphIndexJointClassTrace67
open GroupedBalancedGraphIndexJointIndexBudget67
open GroupedBalancedPlantedEagerAnnotated67
open GroupedBalancedPlantedEagerJointRisk67
open GroupedBalancedPlantedEagerGraphProjection67
open SecuritySharedBudget
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem shared_weight_eq (graph secret index : Nat) :
    ((((2 * graph : ENNReal) + index) / (2 : ENNReal)^128 +
      (secret : ENNReal) / (2 : ENNReal)^128) +
      (index : ENNReal) / (2 : ENNReal)^256) =
    weight ⟨secret, graph, index⟩ := by
  simp only [weight, ENNReal.add_div, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  ac_rfl

theorem annotated_combined_with_nonce_reserve {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat)
    (indexBudget : ∀ answers cache,
      IndexBudget LIFETIME
        (viewOf answers interaction budget cache)) :
    (Pr[fun result => result.1.bad = true ∨
      SecurityIndexTrace.Conflict result.2 |
      annotatedJointGlobal interaction budget] +
      expectedValue (annotatedJointGlobal interaction budget)
        (fun result =>
          (secretCount result.1 : ENNReal) / (2 : ENNReal)^128)) +
      expectedValue (annotatedJointGlobal interaction budget)
        (fun result =>
          (result.2.length : ENNReal) / (2 : ENNReal)^256) ≤
      (budget : ENNReal) / (2 : ENNReal)^127 := by
  calc
    _ ≤ (expectedValue (annotatedJointGlobal interaction budget)
          (fun result =>
            ((2 * result.1.value.graphCalls : ENNReal) +
              result.2.length) / (2 : ENNReal)^128) +
          expectedValue (annotatedJointGlobal interaction budget)
            (fun result =>
              (secretCount result.1 : ENNReal) / (2 : ENNReal)^128)) +
          expectedValue (annotatedJointGlobal interaction budget)
            (fun result =>
              (result.2.length : ENNReal) / (2 : ENNReal)^256) := by
            exact add_le_add
              (add_le_add
                (annotated_bad_le_expected_graph_index
                  interaction budget indexBudget) le_rfl) le_rfl
    _ = expectedValue (annotatedJointGlobal interaction budget)
          (fun result => weight (jointCounts result)) := by
            rw [← expectedValue_add, ← expectedValue_add]
            congr 1
            funext result
            exact shared_weight_eq result.1.value.graphCalls
              (secretCount result.1) result.2.length
    _ ≤ _ := annotated_expected_weight_le interaction budget

theorem organizer_combined_with_nonce_reserve
    (sizes : SigGolf.Sizes)
    (encode : GroupedBalancedScheme67.Signature → Bytes sizes.signature)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (adversary : SigGolf.Adversary sizes)
    (publicCache : SigGolf.Cache) (rounds budget : Nat) :
    let interaction :=
      GroupedBalancedPlantedEagerOrganizerRisk67.organizerInteraction
        sizes encode decodeWitness decodeSignature adversary publicCache
        rounds
    (Pr[fun result => result.1.bad = true ∨
      SecurityIndexTrace.Conflict result.2 |
      annotatedJointGlobal interaction budget] +
      expectedValue (annotatedJointGlobal interaction budget)
        (fun result =>
          (secretCount result.1 : ENNReal) / (2 : ENNReal)^128)) +
      expectedValue (annotatedJointGlobal interaction budget)
        (fun result =>
          (result.2.length : ENNReal) / (2 : ENNReal)^256) ≤
      (budget : ENNReal) / (2 : ENNReal)^127 := by
  dsimp only
  exact annotated_combined_with_nonce_reserve _ budget
    (fun answers cache =>
      GroupedBalancedPlantedEagerOrganizerRisk67.organizer_index_budget
        sizes encode decodeWitness decodeSignature adversary publicCache
        rounds budget answers cache)

#print axioms shared_weight_eq
#print axioms annotated_combined_with_nonce_reserve
#print axioms organizer_combined_with_nonce_reserve

end SigGolfCandidate.Hypertree.GroupedBalancedNonceReserve67
end

/-! Forgetting the private table and audit labels from the paired nonce
experiment yields the same annotated graph/H5 result distribution. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceCommonProjection67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphPassive67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem paired_annotated_projection {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    (fun result => (result.2.1.1,
      result.2.1.2.map Prod.snd)) <$>
      GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
        interaction budget =
    GroupedBalancedPlantedEagerAnnotated67.annotatedJointGlobal
      interaction budget := by
  calc
    _ = (fun result => (result.1.1,
          result.1.2.map Prod.snd)) <$>
        (Prod.snd <$>
          GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
            interaction budget) := by
          simp only [Functor.map_map, Function.comp_def]
    _ = (fun result => (result.1.1,
          result.1.2.map Prod.snd)) <$>
        GroupedBalancedIndexLabeledAudit67.auditedAnnotatedGlobal
          interaction budget := by
          rw [GroupedBalancedIndexLabeledPairedGlobal67.paired_projection]
    _ = _ :=
      GroupedBalancedIndexLabeledAudit67.audited_annotated_projection
        interaction budget

#print axioms paired_annotated_projection

end SigGolfCandidate.Hypertree.GroupedBalancedNonceCommonProjection67
