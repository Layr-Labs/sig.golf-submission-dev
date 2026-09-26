import SigGolfCandidate.Hypertree.GroupedBalancedEagerLogCount67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointMapView67
import SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerAnnotated67
import SigGolfCandidate.Hypertree.SecurityGameHop

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedEagerLogJoint67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedEagerSecretHit67. -/
section
/-! The annotated and unannotated stopped joint experiments have the same
random paths. On each completed path, the annotation is precisely the
secret-key-class count of that path's logged actions. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedEagerLogJoint67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedGraphIndexJointGlobal67
open GroupedBalancedGraphIndexJointClassTrace67
open GroupedBalancedGraphIndexJointMapView67
open GroupedBalancedEagerLogCount67
open GroupedBalancedPlantedEagerGraphProjection67
open GroupedBalancedPlantedEagerAnnotated67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedGraphInteraction67 SecurityGraphIdeal
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem fixed_global_marked {α : Type} (answers : PrivateTable)
    (interaction : QueryCache PointSpec → Interaction α) (budget : Nat) :
    SecurityIndexProgram.execute
      (global (fun cache => annotate (viewOf answers interaction budget cache) 0)
        budget) =
    mapDist (marked (α := Option α) 0)
      (SecurityIndexProgram.execute
        (global (viewOf answers interaction budget) budget)) := by
  rw [global_mapView]
  apply congrArg (fun view => SecurityIndexProgram.execute (global view budget))
  funext cache
  exact eager_log_count answers cache (interaction cache) budget 0

theorem annotated_joint_eq_mapped {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    annotatedJointGlobal interaction budget =
    mapRun (marked (α := Option α) 0) <$>
      GroupedBalancedPlantedEagerGraphProjection67.jointGlobal
        interaction budget := by
  unfold annotatedJointGlobal
    GroupedBalancedPlantedEagerGraphProjection67.jointGlobal
  rw [map_bind]
  apply bind_congr
  intro answers
  exact fixed_global_marked answers interaction budget

theorem mapped_secretCount {α : Type}
    (result : JointOutcome (Option α × List Action)) :
    secretCount (mapOutcome (marked (α := Option α) 0) result) =
      match result.value.value with
      | some (_, trace) => (counts trace).secretKey
      | none => 0 := by
  cases h : result.value.value with
  | none => simp [secretCount, mapOutcome, h]
  | some value =>
      cases value with
      | mk response trace =>
          simp [secretCount, mapOutcome, marked, h]

theorem annotated_expected_secret_eq_stopped_log {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    expectedValue (annotatedJointGlobal interaction budget)
      (fun result => (secretCount result.1 : ENNReal) /
        (2 : ENNReal) ^ 128) =
    expectedValue
      (GroupedBalancedPlantedEagerGraphProjection67.jointGlobal
        interaction budget)
      (fun result =>
        ((match result.1.value.value with
          | some (_, trace) => (counts trace).secretKey
          | none => 0 : Nat) : ENNReal) / (2 : ENNReal) ^ 128) := by
  rw [annotated_joint_eq_mapped, expectedValue_map]
  congr 1
  funext result
  simp only [Function.comp_def, mapRun, mapped_secretCount]

#print axioms annotated_joint_eq_mapped
#print axioms annotated_expected_secret_eq_stopped_log

end SigGolfCandidate.Hypertree.GroupedBalancedEagerLogJoint67

end

/-! A secret-key hit in a graph-stopped action log is charged only to the
secret-key-class queries that occurred before the stop. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedEagerSecretHit67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedGraphIndexJointClassTrace67
open GroupedBalancedEagerLogJoint67
open GroupedBalancedPlantedEagerAnnotated67
open GroupedBalancedPlantedEagerGraphProjection67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedGraphInteraction67 SecurityGraphIdeal
open SecuritySecretKey SecurityGameHop
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem independent_hit_le_expected {α : Type}
    (simulation : ProbComp α) (inputs : α → List Query) :
    Pr[= true | sampleSecretKey >>= fun secretKey =>
      (fun result => decide (SecretKeyHitTrace (inputs result) secretKey))
        <$> simulation] ≤
    expectedValue simulation
      (fun result => ((inputs result).length : ENNReal) /
        (2 : ENNReal) ^ 128) := by
  calc
    _ = Pr[= true | simulation >>= fun result =>
        (fun secretKey => decide
          (SecretKeyHitTrace (inputs result) secretKey)) <$>
          sampleSecretKey] := by
      simp only [← bind_pure_comp]
      exact probOutput_bind_bind_swap _ _ _ _
    _ ≤ ∑' result, Pr[= result | simulation] *
        (((inputs result).length : ENNReal) / (2 : ENNReal) ^ 128) := by
      simp only [probOutput_bind_eq_tsum, probOutput_map,
        decide_eq_true_eq]
      exact ENNReal.tsum_le_tsum fun result =>
        mul_le_mul' le_rfl (prob_secretKeyHitTrace_le (inputs result))
    _ = _ := rfl

noncomputable def stoppedInputs {α : Type}
    (result : JointOutcome (Option α × List Action) ×
      List SecurityIndexTrace.Entry) : List Query :=
  match result.1.value.value with
  | some (_, trace) => secretInputs trace
  | none => []

theorem stopped_hit_iff_option {α : Type}
    (result : JointOutcome (Option α × List Action) ×
      List SecurityIndexTrace.Entry) (secretKey : SecretKey) :
    SecretKeyHitTrace (stoppedInputs result) secretKey ↔
      GroupedBalancedPlantedEagerUnion67.optionEvent
        (fun value : Option α × List Action =>
          SecretKeyHitTrace (secretInputs value.2) secretKey)
        result.1.value.value := by
  cases h : result.1.value.value with
  | none => simp [stoppedInputs, h,
      GroupedBalancedPlantedEagerUnion67.optionEvent,
      SecretKeyHitTrace]
  | some value =>
      cases value with
      | mk response trace =>
          simp [stoppedInputs, h,
            GroupedBalancedPlantedEagerUnion67.optionEvent]

theorem joint_secret_hit_le_annotated_count {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    Pr[= true | sampleSecretKey >>= fun secretKey =>
      (fun result => decide
        (SecretKeyHitTrace (stoppedInputs result) secretKey)) <$>
        GroupedBalancedPlantedEagerGraphProjection67.jointGlobal
          interaction budget] ≤
    expectedValue (annotatedJointGlobal interaction budget)
      (fun result => (secretCount result.1 : ENNReal) /
        (2 : ENNReal) ^ 128) := by
  have bound := independent_hit_le_expected
    (GroupedBalancedPlantedEagerGraphProjection67.jointGlobal
      interaction budget) stoppedInputs
  have countEq (result : JointOutcome (Option α × List Action) ×
      List SecurityIndexTrace.Entry) :
      (stoppedInputs result).length =
        match result.1.value.value with
        | some (_, trace) => (counts trace).secretKey
        | none => 0 := by
    cases h : result.1.value.value with
    | none => simp [stoppedInputs, h]
    | some pair =>
        cases pair with
        | mk response trace =>
            simp [stoppedInputs, h, secretInputs_length_eq_count]
  apply bound.trans_eq
  rw [annotated_expected_secret_eq_stopped_log]
  congr 1
  funext result
  rw [countEq result]

theorem annotated_secret_hit_le_count {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    Pr[= true | sampleSecretKey >>= fun secretKey =>
      (fun result => decide
        (SecretKeyHitTrace (stoppedInputs (eraseRun result)) secretKey))
        <$> annotatedJointGlobal interaction budget] ≤
    expectedValue (annotatedJointGlobal interaction budget)
      (fun result => (secretCount result.1 : ENNReal) /
        (2 : ENNReal) ^ 128) := by
  have bound := joint_secret_hit_le_annotated_count interaction budget
  rw [GroupedBalancedPlantedEagerAnnotated67.jointGlobal_project] at bound
  simpa only [Functor.map_map, Function.comp_def] using bound

theorem annotated_secret_hit_le_count_event {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    Pr[fun result =>
      SecretKeyHitTrace (stoppedInputs (eraseRun result.2)) result.1 |
      do
        let secretKey ← sampleSecretKey
        let result ← annotatedJointGlobal interaction budget
        pure (secretKey, result)] ≤
    expectedValue (annotatedJointGlobal interaction budget)
      (fun result => (secretCount result.1 : ENNReal) /
        (2 : ENNReal) ^ 128) := by
  have bound := annotated_secret_hit_le_count interaction budget
  simpa only [probEvent_bind_eq_tsum, probEvent_map,
    probOutput_bind_eq_tsum, probOutput_map,
    Function.comp_def, decide_eq_true_eq, pure_bind,
    map_eq_pure_bind, probEvent_pure, probOutput_pure,
    true_eq_decide_iff] using bound

#print axioms independent_hit_le_expected
#print axioms stopped_hit_iff_option
#print axioms joint_secret_hit_le_annotated_count
#print axioms annotated_secret_hit_le_count
#print axioms annotated_secret_hit_le_count_event

end SigGolfCandidate.Hypertree.GroupedBalancedEagerSecretHit67
