import SigGolfCandidate.Hypertree.GroupedBalancedPlantedSecretKeyUnion67
import SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerGlobalUnion67
import SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerAnnotated67
import SigGolfCandidate.Hypertree.GroupedBalancedEagerSecretHit67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedPlantedRealUnion67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedPlantedRealJointUnion67. -/
section
/-! The planted real GameWorld cutoff is covered by an eager ideal event that
keeps the independent sampled secret key only for its public-query hit test. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPlantedRealUnion67
open SigGolf SigGolfCandidate.Hypertree OracleComp OracleComp.EvalDist OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphInteraction67 GroupedBalancedGameWorld67
open GroupedBalancedPlantedCache67 GroupedBalancedPlantedEagerHop67
open GroupedBalancedPlantedSecretKeyUnion67
open GroupedBalancedPlantedEagerGlobalUnion67
open GroupedBalancedGameQueryTrace67
open SecurityGameHop SecuritySecretKey
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

noncomputable def realPlantedGlobal {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) : ProbComp (Option α) := do
  let table ← $ᵗ PointTable
  let secretKey ← sampleSecretKey
  (simulateQ (realGameOracle secretKey)
    (SecurityBudget.cutoff
      (gameView table (GroupedBalancedGraphMonitorSetup67.cache table)
        (interaction (GroupedBalancedGraphMonitorSetup67.cache table)))
      budget)).run' (planted table)

noncomputable def eagerSecretGlobal {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) : ProbComp
      (SecretKey × (Option α × List Action)) := do
  let table ← $ᵗ PointTable
  let secretKey ← sampleSecretKey
  let result ← eagerSimulation table
    (GroupedBalancedGraphMonitorSetup67.cache table)
    (interaction (GroupedBalancedGraphMonitorSetup67.cache table)) budget
  pure (secretKey, result)

theorem real_planted_le_eager_union {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) (event : Option α → Prop) :
    Pr[event | realPlantedGlobal interaction budget] ≤
      Pr[fun result => event result.2.1 ∨
        SecretKeyHitTrace (secretInputs result.2.2) result.1 |
        eagerSecretGlobal interaction budget] := by
  unfold realPlantedGlobal eagerSecretGlobal
  conv_lhs => rw [probEvent_bind_eq_tsum]
  conv_rhs => rw [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro table
  apply mul_le_mul' le_rfl
  conv_lhs => rw [probEvent_bind_eq_tsum]
  conv_rhs => rw [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro secretKey
  apply mul_le_mul' le_rfl
  simpa only [bind_pure_comp, probEvent_map,
    Function.comp_def] using
    planted_real_le_eager_union table secretKey
      (GroupedBalancedGraphMonitorSetup67.cache table)
      (interaction (GroupedBalancedGraphMonitorSetup67.cache table))
      budget event

theorem eagerSecretGlobal_swap {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    𝒮[eagerSecretGlobal interaction budget] =
      𝒮[do
        let secretKey ← sampleSecretKey
        let result ← eagerGlobal interaction budget
        pure (secretKey, result)] := by
  unfold eagerSecretGlobal eagerGlobal
  rw [evalSPMF_bind_bind_swap]
  simp only [bind_assoc]

#print axioms real_planted_le_eager_union
#print axioms eagerSecretGlobal_swap

end SigGolfCandidate.Hypertree.GroupedBalancedPlantedRealUnion67

end

/-! First-contact union coupling of the planted real game to the annotated
graph/H5 monitor.  Secret-key guesses are tested only on the retained prefix. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPlantedRealJointUnion67
open SigGolf SigGolfCandidate.Hypertree OracleComp OracleComp.EvalDist OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphInteraction67
open GroupedBalancedPlantedRealUnion67
open GroupedBalancedPlantedEagerAnnotated67
open GroupedBalancedPlantedEagerGlobalUnion67
open GroupedBalancedGraphIndexJointClassTrace67
open GroupedBalancedGameQueryTrace67
open SecuritySecretKey
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

noncomputable def annotatedSecretGlobal {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) : ProbComp
      (SecretKey ×
        (GroupedBalancedGraphIndexJoint67.JointOutcome
          ((Option α × List Action) × Nat) ×
          List SecurityIndexTrace.Entry)) := do
  let secretKey ← sampleSecretKey
  let result ← annotatedJointGlobal interaction budget
  pure (secretKey, result)

theorem real_le_annotated_union_raw {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) (event : Option α → Prop) :
    Pr[event | realPlantedGlobal interaction budget] ≤
      Pr[fun result =>
        let plain := eraseRun result.2
        plain.1.bad = true ∨
          GroupedBalancedPlantedEagerUnion67.optionEvent
            (fun value : Option α × List Action =>
              event value.1 ∨
                SecretKeyHitTrace (secretInputs value.2) result.1)
            plain.1.value.value |
        annotatedSecretGlobal interaction budget] := by
  have first := real_planted_le_eager_union interaction budget event
  have swapped := eagerSecretGlobal_swap interaction budget
  have events := probEvent_congr'
    (p := fun result => event result.2.1 ∨
      SecretKeyHitTrace (secretInputs result.2.2) result.1)
    (q := fun result => event result.2.1 ∨
      SecretKeyHitTrace (secretInputs result.2.2) result.1)
    (fun _ _ => Iff.rfl) swapped
  rw [events] at first
  apply first.trans
  unfold annotatedSecretGlobal
  conv_lhs => rw [probEvent_bind_eq_tsum]
  conv_rhs => rw [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro secretKey
  apply mul_le_mul' le_rfl
  simpa only [bind_pure_comp, probEvent_map, Function.comp_def] using
    (GroupedBalancedPlantedEagerAnnotated67.eager_global_le_annotated_union
      interaction budget
      (fun value => event value.1 ∨
        SecretKeyHitTrace (secretInputs value.2) secretKey))

#print axioms real_le_annotated_union_raw

theorem real_le_annotated_union {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) (event : Option α → Prop) :
    Pr[event | realPlantedGlobal interaction budget] ≤
      Pr[fun result =>
        let plain := eraseRun result.2
        plain.1.bad = true ∨
          GroupedBalancedPlantedEagerUnion67.optionEvent
            (fun value : Option α × List Action => event value.1)
            plain.1.value.value ∨
          SecretKeyHitTrace
            (GroupedBalancedEagerSecretHit67.stoppedInputs plain)
            result.1 |
        annotatedSecretGlobal interaction budget] := by
  apply (real_le_annotated_union_raw interaction budget event).trans_eq
  apply probEvent_congr' _ rfl
  intro result _
  let plain := eraseRun result.2
  have hit :=
    (GroupedBalancedEagerSecretHit67.stopped_hit_iff_option plain result.1)
  change (plain.1.bad = true ∨
      GroupedBalancedPlantedEagerUnion67.optionEvent
        (fun value : Option α × List Action =>
          event value.1 ∨
            SecretKeyHitTrace (secretInputs value.2) result.1)
        plain.1.value.value) ↔
      (plain.1.bad = true ∨
        GroupedBalancedPlantedEagerUnion67.optionEvent
          (fun value : Option α × List Action => event value.1)
          plain.1.value.value ∨
        SecretKeyHitTrace
          (GroupedBalancedEagerSecretHit67.stoppedInputs plain)
          result.1)
  rw [hit]
  cases h : plain.1.value.value with
  | none => simp [GroupedBalancedPlantedEagerUnion67.optionEvent, h]
  | some pair => simp [GroupedBalancedPlantedEagerUnion67.optionEvent, h,
      or_assoc]

#print axioms real_le_annotated_union

end SigGolfCandidate.Hypertree.GroupedBalancedPlantedRealJointUnion67
