import SigGolfCandidate.Hypertree.GroupedBalancedNonceCommonProjection67
import SigGolfCandidate.Hypertree.GroupedBalancedEagerSecretHit67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedNonceOrganizerRisk67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedNonceFullRisk67. -/
section
/-! The organizer's stopped graph/H5 and nonce-hit risks share the exact
Q/2^127 weight, leaving the secret-key hit as its charged expectation. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceOrganizerRisk67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphIndexJointClassTrace67
open GroupedBalancedPlantedEagerAnnotated67
open GroupedBalancedPlantedEagerOrganizerRisk67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem paired_graph_nonce_with_secret_reserve
    (sizes : SigGolf.Sizes)
    (encode : GroupedBalancedScheme67.Signature → Bytes sizes.signature)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (adversary : SigGolf.Adversary sizes)
    (publicCache : SigGolf.Cache) (rounds budget : Nat) :
    let interaction := organizerInteraction sizes encode decodeWitness
      decodeSignature adversary publicCache rounds
    Pr[fun result =>
      (result.2.1.1.bad = true ∨
        SecurityIndexTrace.Conflict
          (result.2.1.2.map Prod.snd)) ∨
      SecurityMonitorIndexContact.NonceHit
        (fun message => result.1 (.randomizer message))
        (GroupedBalancedIndexLabeledHistory67.history
          result.2.2 result.2.1.2) |
      GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
        interaction budget] +
    expectedValue
      (GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
        interaction budget)
      (fun result =>
        (secretCount result.2.1.1 : ENNReal) / (2 : ENNReal)^128) ≤
    (budget : ENNReal) / (2 : ENNReal)^127 := by
  dsimp only
  let interaction := organizerInteraction sizes encode decodeWitness
    decodeSignature adversary publicCache rounds
  let paired := GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
    interaction budget
  let common := annotatedJointGlobal interaction budget
  have graphEq :
      Pr[fun result => result.2.1.1.bad = true ∨
        SecurityIndexTrace.Conflict (result.2.1.2.map Prod.snd) | paired] =
      Pr[fun result => result.1.bad = true ∨
        SecurityIndexTrace.Conflict result.2 | common] := by
    dsimp only [paired, common]
    rw [← GroupedBalancedNonceCommonProjection67.paired_annotated_projection
      interaction budget, probEvent_map]
    rfl
  have secretEq :
      expectedValue paired
        (fun result =>
          (secretCount result.2.1.1 : ENNReal) / (2 : ENNReal)^128) =
      expectedValue common
        (fun result =>
          (secretCount result.1 : ENNReal) / (2 : ENNReal)^128) := by
    dsimp only [paired, common]
    rw [← GroupedBalancedNonceCommonProjection67.paired_annotated_projection
      interaction budget, expectedValue_map]
  have nonceBound :
      Pr[fun result => SecurityMonitorIndexContact.NonceHit
        (fun message => result.1 (.randomizer message))
        (GroupedBalancedIndexLabeledHistory67.history
          result.2.2 result.2.1.2) | paired] ≤
      expectedValue common
        (fun result =>
          (result.2.length : ENNReal) / (2 : ENNReal)^256) := by
    simpa only [paired, common, div_eq_mul_inv,
      expectedValue_mul_const] using
      (GroupedBalancedNonceCostProjection67.paired_nonce_hit_le_index_expected
        interaction budget)
  calc
    _ ≤ (Pr[fun result => result.2.1.1.bad = true ∨
            SecurityIndexTrace.Conflict
              (result.2.1.2.map Prod.snd) | paired] +
          Pr[fun result => SecurityMonitorIndexContact.NonceHit
            (fun message => result.1 (.randomizer message))
            (GroupedBalancedIndexLabeledHistory67.history
              result.2.2 result.2.1.2) | paired]) +
        expectedValue paired
          (fun result =>
            (secretCount result.2.1.1 : ENNReal) /
              (2 : ENNReal)^128) := by
          exact add_le_add (probEvent_or_le paired _ _) le_rfl
    _ = (Pr[fun result => result.1.bad = true ∨
          SecurityIndexTrace.Conflict result.2 | common] +
        expectedValue common
          (fun result =>
            (secretCount result.1 : ENNReal) / (2 : ENNReal)^128)) +
        Pr[fun result => SecurityMonitorIndexContact.NonceHit
          (fun message => result.1 (.randomizer message))
          (GroupedBalancedIndexLabeledHistory67.history
            result.2.2 result.2.1.2) | paired] := by
          rw [graphEq, secretEq]
          ac_rfl
    _ ≤ (Pr[fun result => result.1.bad = true ∨
          SecurityIndexTrace.Conflict result.2 | common] +
        expectedValue common
          (fun result =>
            (secretCount result.1 : ENNReal) / (2 : ENNReal)^128)) +
        expectedValue common
          (fun result =>
            (result.2.length : ENNReal) / (2 : ENNReal)^256) := by
          exact add_le_add le_rfl nonceBound
    _ ≤ _ :=
      GroupedBalancedNonceReserve67.organizer_combined_with_nonce_reserve
        sizes encode decodeWitness decodeSignature adversary publicCache
        rounds budget

#print axioms paired_graph_nonce_with_secret_reserve

end SigGolfCandidate.Hypertree.GroupedBalancedNonceOrganizerRisk67
end

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedNonceSecretLift67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedNonceFullRisk67. -/
section
/-! Transport the stopped secret-key hit charge to the paired nonce experiment
while retaining the sampled private table and audit. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceSecretLift67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphIndexJointClassTrace67
open GroupedBalancedEagerSecretHit67
open SecuritySecretKey
open SecurityGameHop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

private theorem sampled_project_event {K A B : Type}
    (keys : ProbComp K) (simulation : ProbComp A)
    (project : A → B) (event : K × B → Prop) :
    Pr[event | do
      let key ← keys
      let result ← simulation
      pure (key, project result)] =
    Pr[fun result => event (result.1, project result.2) | do
      let key ← keys
      let result ← simulation
      pure (key, result)] := by
  calc
    _ = Pr[event |
      (fun result => (result.1, project result.2)) <$> (do
        let key ← keys
        let result ← simulation
        pure (key, result))] := by
          simp only [map_bind, map_pure, bind_assoc, pure_bind]
    _ = _ := by rw [probEvent_map]; rfl

theorem paired_secret_hit_le_count {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    Pr[fun result =>
      SecretKeyHitTrace
        (stoppedInputs
          (GroupedBalancedGraphIndexJointClassTrace67.eraseRun
            (result.2.2.1.1,
              result.2.2.1.2.map Prod.snd))) result.1 |
      do
        let secretKey ← sampleSecretKey
        let result ←
          GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
            interaction budget
        pure (secretKey, result)] ≤
    expectedValue
      (GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
        interaction budget)
      (fun result =>
        (secretCount result.2.1.1 : ENNReal) /
          (2 : ENNReal)^128) := by
  have bound := annotated_secret_hit_le_count_event interaction budget
  rw [← GroupedBalancedNonceCommonProjection67.paired_annotated_projection]
    at bound
  have eventEq := sampled_project_event sampleSecretKey
    (GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
      interaction budget)
    (fun result => (result.2.1.1,
      result.2.1.2.map Prod.snd))
    (fun result =>
      SecretKeyHitTrace
        (stoppedInputs
          (GroupedBalancedGraphIndexJointClassTrace67.eraseRun result.2))
        result.1)
  simp only [map_eq_pure_bind, bind_assoc, pure_bind] at bound
  rw [eventEq] at bound
  simpa only [← map_eq_pure_bind, expectedValue_map,
    Function.comp_def] using bound

#print axioms paired_secret_hit_le_count

end SigGolfCandidate.Hypertree.GroupedBalancedNonceSecretLift67

end

/-! One stopped distribution pays for graph contact, H5 collision, prereveal
nonce hit, and secret-key-class input hit under the organizer's total budget. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceFullRisk67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphIndexJointClassTrace67
open GroupedBalancedEagerSecretHit67
open SecuritySecretKey SecurityGameHop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

private theorem sampled_event_eq {α : Type} (simulation : ProbComp α)
    (event : α → Prop) :
    Pr[fun result : SecretKey × α => event result.2 |
      do
        let secretKey ← sampleSecretKey
        let result ← simulation
        pure (secretKey, result)] =
      Pr[event | simulation] := by
  have equal :
      Pr[fun result : SecretKey × α => event result.2 |
        do
          let secretKey ← sampleSecretKey
          let result ← simulation
          pure (secretKey, result)] =
      Pr[event | sampleSecretKey >>= fun _ => simulation] := by
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    apply tsum_congr
    intro secretKey
    congr 1
    rw [← map_eq_pure_bind, probEvent_map]
    rfl
  rw [equal, probEvent_bind_const]
  simp [sampleSecretKey, probFailure_uniformSample]

theorem organizer_all_four_risks_le_budget
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
    Pr[fun result =>
      ((result.2.2.1.1.bad = true ∨
        SecurityIndexTrace.Conflict
          (result.2.2.1.2.map Prod.snd)) ∨
       SecurityMonitorIndexContact.NonceHit
        (fun message => result.2.1 (.randomizer message))
        (GroupedBalancedIndexLabeledHistory67.history
          result.2.2.2 result.2.2.1.2)) ∨
      SecretKeyHitTrace
        (stoppedInputs
          (eraseRun
            (result.2.2.1.1,
              result.2.2.1.2.map Prod.snd))) result.1 |
      do
        let secretKey ← sampleSecretKey
        let result ←
          GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
            interaction budget
        pure (secretKey, result)] ≤
      (budget : ENNReal) / (2 : ENNReal)^127 := by
  dsimp only
  let interaction :=
    GroupedBalancedPlantedEagerOrganizerRisk67.organizerInteraction
      sizes encode decodeWitness decodeSignature adversary publicCache rounds
  let paired := GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
    interaction budget
  let all := do
    let secretKey ← sampleSecretKey
    let result ← paired
    pure (secretKey, result)
  calc
    _ ≤ Pr[fun result =>
          (result.2.2.1.1.bad = true ∨
            SecurityIndexTrace.Conflict
              (result.2.2.1.2.map Prod.snd)) ∨
          SecurityMonitorIndexContact.NonceHit
            (fun message => result.2.1 (.randomizer message))
            (GroupedBalancedIndexLabeledHistory67.history
              result.2.2.2 result.2.2.1.2) | all] +
        Pr[fun result => SecretKeyHitTrace
          (stoppedInputs
            (eraseRun
              (result.2.2.1.1,
                result.2.2.1.2.map Prod.snd))) result.1 | all] :=
          probEvent_or_le all _ _
    _ = Pr[fun result =>
          (result.2.1.1.bad = true ∨
            SecurityIndexTrace.Conflict
              (result.2.1.2.map Prod.snd)) ∨
          SecurityMonitorIndexContact.NonceHit
            (fun message => result.1 (.randomizer message))
            (GroupedBalancedIndexLabeledHistory67.history
              result.2.2 result.2.1.2) | paired] +
        Pr[fun result => SecretKeyHitTrace
          (stoppedInputs
            (eraseRun
              (result.2.2.1.1,
                result.2.2.1.2.map Prod.snd))) result.1 | all] := by
          dsimp only [all]
          rw [sampled_event_eq paired
            (fun result =>
              (result.2.1.1.bad = true ∨
                SecurityIndexTrace.Conflict
                  (result.2.1.2.map Prod.snd)) ∨
              SecurityMonitorIndexContact.NonceHit
                (fun message => result.1 (.randomizer message))
                (GroupedBalancedIndexLabeledHistory67.history
                  result.2.2 result.2.1.2))]
    _ ≤ Pr[fun result =>
          (result.2.1.1.bad = true ∨
            SecurityIndexTrace.Conflict
              (result.2.1.2.map Prod.snd)) ∨
          SecurityMonitorIndexContact.NonceHit
            (fun message => result.1 (.randomizer message))
            (GroupedBalancedIndexLabeledHistory67.history
              result.2.2 result.2.1.2) | paired] +
        expectedValue paired
          (fun result =>
            (secretCount result.2.1.1 : ENNReal) /
              (2 : ENNReal)^128) := by
          exact add_le_add le_rfl
            (GroupedBalancedNonceSecretLift67.paired_secret_hit_le_count
              interaction budget)
    _ ≤ _ :=
      GroupedBalancedNonceOrganizerRisk67.paired_graph_nonce_with_secret_reserve
        sizes encode decodeWitness decodeSignature adversary publicCache
        rounds budget

#print axioms organizer_all_four_risks_le_budget

end SigGolfCandidate.Hypertree.GroupedBalancedNonceFullRisk67
