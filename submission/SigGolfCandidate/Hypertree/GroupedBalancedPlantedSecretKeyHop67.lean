import SigGolfCandidate.Hypertree.GroupedBalancedGameWorld67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphOrganizerView67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointOrganizerBound67
import SigGolfCandidate.Hypertree.SecurityBudget
import SigGolfCandidate.Hypertree.GroupedBalancedPlantedCache67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGameWorldBudget67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedPlantedSecretKeyHop67. -/
section
/-! The abstract wire organizer is a fixed GameWorld program after the graph
table is sampled. In particular, the program passed to the existing secret-key
separation hop does not depend on the sampled secret key. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGameWorldBudget67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGameWorld67
open GroupedBalancedGraphViewWorld67
open SecurityGameHop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

noncomputable def organizerProgram (sizes : Sizes)
    (encode : GroupedBalancedScheme67.Signature → Bytes sizes.signature)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (adversary : SigGolf.Adversary sizes)
    (publicCache : Cache) (rounds : Nat) (table : PointTable) :
    OracleComp GameWorld
      (GroupedBalancedGraphOrganizerView67.Result sizes) :=
  let exposed := GroupedBalancedGraphMonitorSetup67.cache table
  let pk := GroupedBalancedGraphMonitorSetupBound67.rootFrom exposed
  gameView table exposed
    (GroupedBalancedGraphOrganizerView67.ofInteract sizes encode
      decodeWitness decodeSignature adversary pk rounds
      (adversary.initial pk publicCache) {})

theorem resolve_organizerProgram (sizes : Sizes)
    (encode : GroupedBalancedScheme67.Signature → Bytes sizes.signature)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (secretKey : SecretKey) (adversary : SigGolf.Adversary sizes)
    (publicCache : Cache) (rounds : Nat) (table : PointTable) :
    resolve secretKey
      (organizerProgram sizes encode decodeWitness decodeSignature
        adversary publicCache rounds table) =
    ofView table
      (GroupedBalancedGraphIndexJointOrganizerBound67.organizerView sizes
        encode decodeWitness decodeSignature secretKey adversary
        publicCache rounds
        (GroupedBalancedGraphMonitorSetup67.cache table)) := by
  unfold organizerProgram
    GroupedBalancedGraphIndexJointOrganizerBound67.organizerView
  exact resolve_gameView secretKey table
    (GroupedBalancedGraphMonitorSetup67.cache table) _

/-- The old secret-key erasure bound applies to this direct67 abstract game
without selecting the attacker's program after the secret key draw. -/
theorem organizer_secretKey_hop (sizes : Sizes)
    (encode : GroupedBalancedScheme67.Signature → Bytes sizes.signature)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (adversary : SigGolf.Adversary sizes)
    (publicCache : Cache) (rounds budget : Nat) (table : PointTable) :
    Pr[fun result => result.1.won = true ∧ result.2 ≤ budget |
      sampleSecretKey >>= fun secretKey =>
        (simulateQ (realGameOracle secretKey)
          (SecurityBudget.counted
            (organizerProgram sizes encode decodeWitness decodeSignature
              adversary publicCache rounds table))).run' ∅] ≤
    Pr[fun result => result.1.won = true ∧ result.2 ≤ budget |
      (simulateQ idealGameOracle
        (SecurityBudget.counted
          (organizerProgram sizes encode decodeWitness decodeSignature
            adversary publicCache rounds table))).run' (∅, ∅)] +
      (budget : ENNReal) / (2 : ENNReal) ^ 128 :=
  SecurityBudget.prob_counted_real_le_ideal_add_secretKey
    (organizerProgram sizes encode decodeWitness decodeSignature
      adversary publicCache rounds table) budget
    (fun result => result.won = true)

#print axioms resolve_organizerProgram
#print axioms organizer_secretKey_hop

end SigGolfCandidate.Hypertree.GroupedBalancedGameWorldBudget67

end

/-! The legacy secret-key erasure argument also works from a sampled planted
public graph cache. The graph cache has no secret-derivation input, so the
related-cache invariant holds for every possible secret key. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPlantedSecretKeyHop67
open SigGolf SigGolfCandidate.Hypertree OracleComp OracleSpec
open SecurityGameHop SecuritySeparation
open GroupedBalancedGraphPassive67
open GroupedBalancedPlantedCache67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

private theorem run'_query_bind {σ α : Type}
    (implementation : QueryImpl GameWorld (StateT σ ProbComp))
    (query : GameWorld.Domain)
    (next : GameWorld.Range query → OracleComp GameWorld α) (cache : σ) :
    (simulateQ implementation (liftM (GameWorld.query query) >>= next)).run' cache =
      ((implementation query).run cache >>= fun result =>
        (simulateQ implementation (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run'_eq, StateT.run_bind,
    map_bind]

private theorem stopped_le {σ α : Type}
    (implementation : QueryImpl GameWorld (StateT σ ProbComp))
    (secretKey : SecretKey) (program : OracleComp GameWorld α)
    (cache : σ) (event : α → Prop) :
    Pr[fun value => ∃ x, value = some x ∧ event x |
      (simulateQ implementation (stop secretKey program)).run' cache] ≤
    Pr[event | (simulateQ implementation program).run' cache] := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind query next ih =>
      rw [stop_query_bind]
      split
      · simp
      · simp only [run'_query_bind, probEvent_bind_eq_tsum]
        exact ENNReal.tsum_le_tsum fun result =>
          mul_le_mul' le_rfl (ih result.1 result.2)

private theorem le_stopped_add_stop {σ α : Type}
    (implementation : QueryImpl GameWorld (StateT σ ProbComp))
    (secretKey : SecretKey) (program : OracleComp GameWorld α)
    (cache : σ) (event : α → Prop) :
    Pr[event | (simulateQ implementation program).run' cache] ≤
      Pr[fun value => ∃ x, value = some x ∧ event x |
        (simulateQ implementation (stop secretKey program)).run' cache] +
      Pr[= none | (simulateQ implementation
        (stop secretKey program)).run' cache] := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind query next ih =>
      rw [stop_query_bind]
      split
      · simp
      · simp only [run'_query_bind, probEvent_bind_eq_tsum,
          probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
        exact ENNReal.tsum_le_tsum fun result =>
          (mul_le_mul' le_rfl (ih result.1 result.2)).trans_eq (mul_add ..)

theorem related_hop {α : Type}
    (real : QueryCache HashSpec) (ideal : SplitCache)
    (related : ∀ secretKey, Related secretKey real ideal)
    (program : OracleComp GameWorld α) (limit : Nat)
    (bounded : PublicTraceBound program ideal limit)
    (event : α → Prop) :
    Pr[event | sampleSecretKey >>= fun secretKey =>
      (simulateQ (realGameOracle secretKey) program).run' real] ≤
    Pr[event | (simulateQ idealGameOracle program).run' ideal] +
      (limit : ENNReal) / (2 : ENNReal) ^ 128 := by
  have compare (secretKey : SecretKey) :
      Pr[event | (simulateQ (realGameOracle secretKey) program).run' real] ≤
      Pr[event | (simulateQ idealGameOracle program).run' ideal] +
      Pr[= none | (simulateQ idealGameOracle
        (stop secretKey program)).run' ideal] := by
    have h := le_stopped_add_stop
      (realGameOracle secretKey) secretKey program real event
    rw [stopped_separation secretKey program real ideal (related secretKey)] at h
    exact h.trans (add_le_add
      (stopped_le idealGameOracle secretKey program ideal event) le_rfl)
  calc
    _ ≤ Pr[event | sampleSecretKey >>= fun _ =>
          (simulateQ idealGameOracle program).run' ideal] +
        Pr[= none | sampleSecretKey >>= fun secretKey =>
          (simulateQ idealGameOracle
            (stop secretKey program)).run' ideal] := by
      simp only [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum,
        ← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum fun secretKey =>
        (mul_le_mul' le_rfl (compare secretKey)).trans_eq (mul_add ..)
    _ ≤ _ := by
      simpa using add_le_add
        (le_refl (Pr[event |
          (simulateQ idealGameOracle program).run' ideal]))
        (prob_stop_secretKey_le program ideal limit bounded)

/-- The sharp penalty retains the expected number of eligible public probes
in the independent planted-cache world for a shared query-class budget. -/
theorem related_hop_expected {α : Type}
    (real : QueryCache HashSpec) (ideal : SplitCache)
    (related : ∀ secretKey, Related secretKey real ideal)
    (program : OracleComp GameWorld α) (event : α → Prop) :
    Pr[event | sampleSecretKey >>= fun secretKey =>
      (simulateQ (realGameOracle secretKey) program).run' real] ≤
    Pr[event | (simulateQ idealGameOracle program).run' ideal] +
      expectedSecretKeyQueries program ideal / (2 : ENNReal) ^ 128 := by
  have compare (secretKey : SecretKey) :
      Pr[event | (simulateQ (realGameOracle secretKey) program).run' real] ≤
      Pr[event | (simulateQ idealGameOracle program).run' ideal] +
      Pr[= none | (simulateQ idealGameOracle
        (stop secretKey program)).run' ideal] := by
    have h := le_stopped_add_stop
      (realGameOracle secretKey) secretKey program real event
    rw [stopped_separation secretKey program real ideal (related secretKey)] at h
    exact h.trans (add_le_add
      (stopped_le idealGameOracle secretKey program ideal event) le_rfl)
  calc
    _ ≤ Pr[event | sampleSecretKey >>= fun _ =>
          (simulateQ idealGameOracle program).run' ideal] +
        Pr[= none | sampleSecretKey >>= fun secretKey =>
          (simulateQ idealGameOracle
            (stop secretKey program)).run' ideal] := by
      simp only [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum,
        ← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum fun secretKey =>
        (mul_le_mul' le_rfl (compare secretKey)).trans_eq (mul_add ..)
    _ ≤ _ := by
      simpa using add_le_add
        (le_refl (Pr[event |
          (simulateQ idealGameOracle program).run' ideal]))
        (prob_stop_secretKey_le_expected program ideal)

/-- A fully planted-cache secret-key hop, valid for any adaptive program. -/
theorem planted_hop {α : Type} (table : PointTable)
    (program : OracleComp GameWorld α) (limit : Nat)
    (bounded : PublicTraceBound program
      (∅, planted table) limit) (event : α → Prop) :
    Pr[event | sampleSecretKey >>= fun secretKey =>
      (simulateQ (realGameOracle secretKey) program).run' (planted table)] ≤
    Pr[event | (simulateQ idealGameOracle program).run'
      (∅, planted table)] +
      (limit : ENNReal) / (2 : ENNReal) ^ 128 :=
  related_hop (planted table) (∅, planted table)
    (planted_related table) program limit bounded event

theorem planted_hop_expected {α : Type} (table : PointTable)
    (program : OracleComp GameWorld α) (event : α → Prop) :
    Pr[event | sampleSecretKey >>= fun secretKey =>
      (simulateQ (realGameOracle secretKey) program).run' (planted table)] ≤
    Pr[event | (simulateQ idealGameOracle program).run'
      (∅, planted table)] +
      expectedSecretKeyQueries program (∅, planted table) /
        (2 : ENNReal) ^ 128 :=
  related_hop_expected (planted table) (∅, planted table)
    (planted_related table) program event

#print axioms related_hop
#print axioms related_hop_expected
#print axioms planted_hop
#print axioms planted_hop_expected

end SigGolfCandidate.Hypertree.GroupedBalancedPlantedSecretKeyHop67
