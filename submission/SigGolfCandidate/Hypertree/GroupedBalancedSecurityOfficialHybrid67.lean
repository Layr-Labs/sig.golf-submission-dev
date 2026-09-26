import SigGolfCandidate.Hypertree.GroupedBalancedSecurityOfficialJoint67

/-! The first public query to a secret H1 source is the exact bad event in
the official-to-planted random-oracle hybrid. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityOfficialHybrid67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedSecurityJointPresample67
open GroupedBalancedSecuritySourceHybrid67
open GroupedBalancedSecurityJointInteraction67
open GroupedBalancedSecurityJointContext67
open GroupedBalancedPrivateFactors67 GroupedBalancedSecurityGraph67
open GroupedBalancedSecurityJointTable67 GroupedBalancedGraphPassive67
open GroupedBalancedPrivateDerivation67
open scoped Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private abbrev submission := GroupedBalancedProgram67ByteSign.submission

theorem source_hit_not_randomizer (secretKey : SecretKey)
    (message : Message) :
    ¬ SourceHit secretKey
      (SecurityRandomOracle.randomizerInput secretKey message) := by
  rintro ⟨slot, source, same⟩
  change input secretKey slot = input secretKey (.randomizer message) at same
  have slots := input_injective secretKey same
  cases slot with
  | bottom _ => cases slots
  | upper _ _ _ => cases slots
  | randomizer _ => cases source

theorem source_hit_not_index (secretKey : SecretKey)
    (message : Message) (randomizer : Bytes 32) :
    ¬ SourceHit secretKey
      (SecurityRandomOracle.indexInput message randomizer) := by
  rintro ⟨slot, _, same⟩
  exact GroupedBalancedQueryClasses67.private_input_ne_index
    secretKey slot message randomizer same

theorem mixture_le_add {α β γ : Type} (outer : ProbComp α)
    (left right : α → ProbComp β) (error : α → ProbComp γ)
    (event : β → Prop) (bad : γ → Prop)
    (step : ∀ value : α,
      Pr[event | left value] ≤ Pr[event | right value] +
        Pr[bad | error value]) :
    Pr[event | outer >>= left] ≤
      Pr[event | outer >>= right] +
      Pr[bad | outer >>= error] := by
  simp only [probEvent_bind_eq_tsum, ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun value =>
    (mul_le_mul' le_rfl (step value)).trans_eq (mul_add ..)

def StoppedRisk {α : Type} (event : α → Prop) : Option α → Prop
  | none => True
  | some value => event value

theorem stopped_risk_sum {α : Type} (event : α → Prop)
    (program : ProbComp (Option α)) :
    Pr[StoppedRisk event | program] =
      Pr[fun value => ∃ result, value = some result ∧ event result | program] +
      Pr[= none | program] := by
  classical
  rw [← probEvent_eq_eq_probOutput program none]
  simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply tsum_congr
  intro value
  cases value with
  | none => simp [StoppedRisk]
  | some result =>
      simp [StoppedRisk]
      rfl

/-- The two bad branches form one disjoint event in the planted stopped game:
either a successful completed result or the first public source H1 hit. -/
theorem source_union (secretKey : SecretKey)
    (answers : PrivateTable) (labels : Labels)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable)
    (program : OracleComp World AttackResult)
    (event : AttackResult → Prop) :
    Pr[event | SecurityGraphHidden.observe program
      (jointCache secretKey answers labels)] ≤
    Pr[StoppedRisk event | SecurityGraphHidden.observe
      (SecurityCache.stopBefore (SourceHit secretKey) program)
      (plantedCache answers labels ghosts)] := by
  have first := SecurityCache.prob_le_stopped_add_stop
    (SourceHit secretKey) program
    (jointCache secretKey answers labels) event
  rw [SecurityCache.stopped_run_eq
    (SourceHit secretKey) program
    (jointCache secretKey answers labels)
    (plantedCache answers labels ghosts)
    (joint_planted_agree secretKey answers labels ghosts)] at first
  simpa only [SecurityGraphHidden.observe, stopped_risk_sum] using first

noncomputable def jointSemantic
    (adversary : Adversary submission.sizes) (rounds : Nat) :
    ProbComp AttackResult := do
  let secretKey ← sampleSecretKey
  let answers ← $ᵗ PrivateTable
  let labels ← $ᵗ Labels
  let ghosts ← $ᵗ GroupedBalancedGlobalPaired67.GhostTable
  SecurityGraphHidden.observe
    (gameWith (semanticInterface answers labels ghosts)
      adversary rounds secretKey)
    (jointCache secretKey answers labels)

noncomputable def plantedSemantic
    (adversary : Adversary submission.sizes) (rounds : Nat) :
    ProbComp AttackResult := do
  let secretKey ← sampleSecretKey
  let answers ← $ᵗ PrivateTable
  let labels ← $ᵗ Labels
  let ghosts ← $ᵗ GroupedBalancedGlobalPaired67.GhostTable
  SecurityGraphHidden.observe
    (gameWith (semanticInterface answers labels ghosts)
      adversary rounds secretKey)
    (plantedCache answers labels ghosts)

noncomputable def sourceStop
    (adversary : Adversary submission.sizes) (rounds : Nat) :
    ProbComp (Option AttackResult) := do
  let secretKey ← sampleSecretKey
  let answers ← $ᵗ PrivateTable
  let labels ← $ᵗ Labels
  let ghosts ← $ᵗ GroupedBalancedGlobalPaired67.GhostTable
  SecurityGraphHidden.observe
    (SecurityCache.stopBefore (SourceHit secretKey)
      (gameWith (semanticInterface answers labels ghosts)
        adversary rounds secretKey))
    (plantedCache answers labels ghosts)

noncomputable def tableInterface (table : PointTable) : Interface where
  keygen _ := pure (some
    (GroupedBalancedGraphMonitorSetupBound67.rootPublic table, (0 : Cache)),
    3983)
  sign secretKey request := semanticSign secretKey table request
  check := actualInterface.check

theorem semanticInterface_tableOf (answers : PrivateTable)
    (labels : Labels)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable) :
    semanticInterface answers labels ghosts =
      tableInterface (tableOf answers labels ghosts) := rfl

/-- Once the source cache is erased, the graph table itself is uniformly
sampled. The secret key remains independently sampled, and no result fields
are projected away. -/
theorem planted_semantic_uniform_table
    (adversary : Adversary submission.sizes) (rounds : Nat) :
    𝒮[plantedSemantic adversary rounds] =
      𝒮[do
        let table ← $ᵗ PointTable
        let secretKey ← sampleSecretKey
        SecurityGraphHidden.observe
          (gameWith (tableInterface table) adversary rounds secretKey)
          (GroupedBalancedPlantedCache67.planted table)] := by
  unfold plantedSemantic
  calc
    _ = 𝒮[do
          let secretKey ← sampleSecretKey
          let table ← $ᵗ PointTable
          SecurityGraphHidden.observe
            (gameWith (tableInterface table) adversary rounds secretKey)
            (GroupedBalancedPlantedCache67.planted table)] := by
          apply evalSPMF_bind_congr
          intro secretKey _
          simpa only [semanticInterface_tableOf, plantedCache] using
            (uniform_table (fun table => SecurityGraphHidden.observe
              (gameWith (tableInterface table) adversary rounds secretKey)
              (GroupedBalancedPlantedCache67.planted table)))
    _ = _ := evalSPMF_bind_bind_swap _ _ _

/-- The source-hit stopped branch likewise depends only on a uniform point
table and an independent secret key. -/
theorem source_stop_uniform_table
    (adversary : Adversary submission.sizes) (rounds : Nat) :
    𝒮[sourceStop adversary rounds] =
      𝒮[do
        let table ← $ᵗ PointTable
        let secretKey ← sampleSecretKey
        SecurityGraphHidden.observe
          (SecurityCache.stopBefore (SourceHit secretKey)
            (gameWith (tableInterface table) adversary rounds secretKey))
          (GroupedBalancedPlantedCache67.planted table)] := by
  unfold sourceStop
  calc
    _ = 𝒮[do
          let secretKey ← sampleSecretKey
          let table ← $ᵗ PointTable
          SecurityGraphHidden.observe
            (SecurityCache.stopBefore (SourceHit secretKey)
              (gameWith (tableInterface table) adversary rounds secretKey))
            (GroupedBalancedPlantedCache67.planted table)] := by
          apply evalSPMF_bind_congr
          intro secretKey _
          simpa only [semanticInterface_tableOf, plantedCache] using
            (uniform_table (fun table => SecurityGraphHidden.observe
              (SecurityCache.stopBefore (SourceHit secretKey)
                (gameWith (tableInterface table) adversary rounds secretKey))
              (GroupedBalancedPlantedCache67.planted table)))
    _ = _ := evalSPMF_bind_bind_swap _ _ _

/-- This is a direct, nonconditional relation between the submitted adaptive
experiment and the planted semantic experiment. It keeps the official result
and charge exactly, and exposes only the source-hit event. -/
theorem official_le_planted_add_source_hit
    (adversary : Adversary submission.sizes) (rounds : Nat)
    (event : AttackResult → Prop) :
    Pr[event | submission.securityExperiment adversary rounds] ≤
      Pr[event | plantedSemantic adversary rounds] +
      Pr[= none | sourceStop adversary rounds] := by
  have same : Pr[event | submission.securityExperiment adversary rounds] =
      Pr[event | jointSemantic adversary rounds] := by
    have dist :=
      GroupedBalancedSecurityOfficialJoint67.official_joint_semantic
        adversary rounds
    exact probEvent_congr' (fun _ _ => Iff.rfl)
      (by simpa only [jointSemantic] using dist)
  rw [same]
  unfold jointSemantic
  unfold plantedSemantic sourceStop
  simp only [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum,
    ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro secretKey
  refine (mul_le_mul' le_rfl ?_).trans_eq (mul_add ..)
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro answers
  refine (mul_le_mul' le_rfl ?_).trans_eq (mul_add ..)
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro labels
  refine (mul_le_mul' le_rfl ?_).trans_eq (mul_add ..)
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro ghosts
  refine (mul_le_mul' le_rfl ?_).trans_eq (mul_add ..)
  exact source_hybrid secretKey answers labels ghosts
    (gameWith (semanticInterface answers labels ghosts)
      adversary rounds secretKey) event

/-- The completed win and the first source hit are represented as one
disjoint event in the same planted stopped execution. This form can be
compared with the organizer's existing four-risk event. -/
theorem official_le_stopped_risk
    (adversary : Adversary submission.sizes) (rounds : Nat)
    (event : AttackResult → Prop) :
    Pr[event | submission.securityExperiment adversary rounds] ≤
      Pr[StoppedRisk event | sourceStop adversary rounds] := by
  have dist := GroupedBalancedSecurityOfficialJoint67.official_joint_semantic
    adversary rounds
  have same : Pr[event | submission.securityExperiment adversary rounds] =
      Pr[event | jointSemantic adversary rounds] := by
    exact probEvent_congr' (fun _ _ => Iff.rfl)
      (by simpa only [jointSemantic] using dist)
  rw [same]
  unfold jointSemantic sourceStop
  simp only [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro secretKey
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro answers
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro labels
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ghosts
  apply mul_le_mul' le_rfl
  exact source_union secretKey answers labels ghosts
    (gameWith (semanticInterface answers labels ghosts)
      adversary rounds secretKey) event

#print axioms official_le_planted_add_source_hit
#print axioms source_union
#print axioms official_le_stopped_risk
#print axioms planted_semantic_uniform_table
#print axioms source_stop_uniform_table
#print axioms source_hit_not_randomizer
#print axioms source_hit_not_index

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityOfficialHybrid67
