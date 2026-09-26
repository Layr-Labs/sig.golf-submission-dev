import SigGolfCandidate.Hypertree.GroupedBalancedPlantedSecretKeyHop67
import SigGolfCandidate.Hypertree.GroupedBalancedGameQueryTrace67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedPlantedSecretKeyBudget67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedPlantedSecretKeyClass67. -/
section
/-! The planted-cache secret-key hop uses the same total-call cutoff and
counted event as the organizer's security game. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPlantedSecretKeyBudget67
open SigGolf SigGolfCandidate.Hypertree OracleComp OracleComp.EvalDist OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedPlantedCache67
open GroupedBalancedPlantedSecretKeyHop67
open GroupedBalancedGameWorldBudget67
open SecurityGameHop
set_option backward.isDefEq.respectTransparency false
open scoped Classical

theorem planted_counted_hop {α : Type} (table : PointTable)
    (program : OracleComp GameWorld α) (budget : Nat)
    (event : α → Prop) :
    Pr[fun result => event result.1 ∧ result.2 ≤ budget |
      sampleSecretKey >>= fun secretKey =>
        (simulateQ (realGameOracle secretKey)
          (SecurityBudget.counted program)).run' (planted table)] ≤
    Pr[fun result => event result.1 ∧ result.2 ≤ budget |
      (simulateQ idealGameOracle
        (SecurityBudget.counted program)).run'
          (∅, planted table)] +
      (budget : ENNReal) / (2 : ENNReal) ^ 128 := by
  have h := planted_hop table (SecurityBudget.cutoff program budget)
    budget
    (SecurityBudget.cutoff_publicTraceBound program
      (∅, planted table) budget)
    (fun value => ∃ output, value = some output ∧ event output)
  simpa only [probEvent_bind_eq_tsum,
    SecurityBudget.prob_cutoff_eq_counted] using h

/-- The counted event with its exact secret-key-eligible public query cost. -/
theorem planted_counted_hop_expected {α : Type} (table : PointTable)
    (program : OracleComp GameWorld α) (budget : Nat)
    (event : α → Prop) :
    Pr[fun result => event result.1 ∧ result.2 ≤ budget |
      sampleSecretKey >>= fun secretKey =>
        (simulateQ (realGameOracle secretKey)
          (SecurityBudget.counted program)).run' (planted table)] ≤
    Pr[fun result => event result.1 ∧ result.2 ≤ budget |
      (simulateQ idealGameOracle
        (SecurityBudget.counted program)).run'
          (∅, planted table)] +
      SecurityGameHop.expectedSecretKeyQueries
        (SecurityBudget.cutoff program budget)
        (∅, planted table) / (2 : ENNReal) ^ 128 := by
  have h := planted_hop_expected table
    (SecurityBudget.cutoff program budget)
    (fun value => ∃ output, value = some output ∧ event output)
  simpa only [probEvent_bind_eq_tsum,
    SecurityBudget.prob_cutoff_eq_counted] using h

theorem organizer_planted_counted_hop (sizes : Sizes)
    (encode : GroupedBalancedScheme67.Signature → Bytes sizes.signature)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (adversary : SigGolf.Adversary sizes) (publicCache : Cache)
    (rounds budget : Nat) (table : PointTable) :
    Pr[fun result => result.1.won = true ∧ result.2 ≤ budget |
      sampleSecretKey >>= fun secretKey =>
        (simulateQ (realGameOracle secretKey)
          (SecurityBudget.counted
            (organizerProgram sizes encode decodeWitness decodeSignature
              adversary publicCache rounds table))).run'
          (planted table)] ≤
    Pr[fun result => result.1.won = true ∧ result.2 ≤ budget |
      (simulateQ idealGameOracle
        (SecurityBudget.counted
          (organizerProgram sizes encode decodeWitness decodeSignature
            adversary publicCache rounds table))).run'
          (∅, planted table)] +
      (budget : ENNReal) / (2 : ENNReal) ^ 128 :=
  planted_counted_hop table
    (organizerProgram sizes encode decodeWitness decodeSignature
      adversary publicCache rounds table) budget
    (fun result => result.won = true)

/-- Sampling the public graph before the secret key preserves the fixed-table
hop. The sampled table is shared by both games and never selected from the key. -/
theorem sampled_organizer_planted_hop (sizes : Sizes)
    (encode : GroupedBalancedScheme67.Signature → Bytes sizes.signature)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (adversary : SigGolf.Adversary sizes) (publicCache : Cache)
    (rounds budget : Nat) :
    Pr[fun result => result.1.won = true ∧ result.2 ≤ budget | do
      let table ← $ᵗ PointTable
      let secretKey ← sampleSecretKey
      (simulateQ (realGameOracle secretKey)
        (SecurityBudget.counted
          (organizerProgram sizes encode decodeWitness decodeSignature
            adversary publicCache rounds table))).run' (planted table)] ≤
    Pr[fun result => result.1.won = true ∧ result.2 ≤ budget | do
      let table ← $ᵗ PointTable
      (simulateQ idealGameOracle
        (SecurityBudget.counted
          (organizerProgram sizes encode decodeWitness decodeSignature
            adversary publicCache rounds table))).run'
        (∅, planted table)] +
      (budget : ENNReal) / (2 : ENNReal) ^ 128 := by
  simp only [probEvent_bind_eq_expectedValue]
  calc
    _ ≤ expectedValue ($ᵗ PointTable)
        (fun table =>
          Pr[fun result => result.1.won = true ∧ result.2 ≤ budget |
            (simulateQ idealGameOracle
              (SecurityBudget.counted
                (organizerProgram sizes encode decodeWitness
                  decodeSignature adversary publicCache rounds table))).run'
              (∅, planted table)] +
            (budget : ENNReal) / (2 : ENNReal) ^ 128) := by
          apply expectedValue_mono
          intro table
          simpa only [probEvent_bind_eq_expectedValue] using
            (organizer_planted_counted_hop sizes encode decodeWitness
              decodeSignature adversary publicCache rounds budget table)
    _ = _ := by
      rw [expectedValue_add]
      rw [expectedValue_const NeverFail.probFailure_eq_zero]

#print axioms planted_counted_hop
#print axioms planted_counted_hop_expected
#print axioms organizer_planted_counted_hop
#print axioms sampled_organizer_planted_hop

end SigGolfCandidate.Hypertree.GroupedBalancedPlantedSecretKeyBudget67

end

/-! Express the planted secret-key hop's sharp loss as the secret-key class
of one full, ideal hash-query log. This is the same log that can later charge
graph and H5 queries, including the honest randomizer/index calls. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPlantedSecretKeyClass67
open SigGolf SigGolfCandidate.Hypertree OracleComp OracleComp.EvalDist OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedPlantedCache67
open GroupedBalancedPlantedSecretKeyBudget67
open SecurityGameHop
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def classPenalty {α : Type} (table : PointTable)
    (program : OracleComp GameWorld α) (budget : Nat) : ENNReal :=
  expectedValue
    ((simulateQ idealGameOracle
      (GroupedBalancedGameQueryTrace67.logged
        (SecurityBudget.cutoff program budget))).run'
      (∅, planted table))
    (fun result =>
      ((GroupedBalancedGameQueryTrace67.counts result.2).secretKey : ENNReal))

theorem classPenalty_eq_expected {α : Type} (table : PointTable)
    (program : OracleComp GameWorld α) (budget : Nat) :
    classPenalty table program budget =
      SecurityGameHop.expectedSecretKeyQueries
        (SecurityBudget.cutoff program budget) (∅, planted table) := by
  exact (GroupedBalancedGameQueryTrace67.expectedSecretKeyQueries_eq_class
    (SecurityBudget.cutoff program budget) (∅, planted table)).symm

/-- The loss of the real-to-ideal planted hop is paid by the secret-key class
of its exact stopped ideal hash-query trace. -/
theorem planted_counted_hop_class {α : Type} (table : PointTable)
    (program : OracleComp GameWorld α) (budget : Nat)
    (event : α → Prop) :
    Pr[fun result => event result.1 ∧ result.2 ≤ budget |
      sampleSecretKey >>= fun secretKey =>
        (simulateQ (realGameOracle secretKey)
          (SecurityBudget.counted program)).run' (planted table)] ≤
    Pr[fun result => event result.1 ∧ result.2 ≤ budget |
      (simulateQ idealGameOracle
        (SecurityBudget.counted program)).run'
          (∅, planted table)] +
      classPenalty table program budget / (2 : ENNReal) ^ 128 := by
  simpa only [classPenalty_eq_expected] using
    planted_counted_hop_expected table program budget event

#print axioms classPenalty_eq_expected
#print axioms planted_counted_hop_class

end SigGolfCandidate.Hypertree.GroupedBalancedPlantedSecretKeyClass67
