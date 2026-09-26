import SigGolfCandidate.Hypertree.GroupedBalancedSecurityOfficialHybrid67
import SigGolfCandidate.Hypertree.GroupedBalancedSecurityCheckObservation67
import SigGolfCandidate.Hypertree.GroupedBalancedSecurityVerifySourceFree67

/-! Replace the submitted checker by the direct67 reference verifier inside
the adaptive security game. The only premise is the actual verifier's fixed
oracle result and call-count refinement. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityFullSemantic67
open SigGolf OracleComp OracleSpec Reference SecurityCache SecurityGraphHidden
open GroupedBalancedGraphPassive67
open GroupedBalancedPrivateFactors67 GroupedBalancedSecurityGraph67
open GroupedBalancedSecurityJointInteraction67
open GroupedBalancedSecurityOfficialHybrid67
open GroupedBalancedSecurityJointContext67
open GroupedBalancedSecuritySourceHybrid67
open scoped Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

private abbrev submission := GroupedBalancedProgram67ByteSign.submission

def countHash {α : Type} (program : OracleComp HashSpec α) :
    OracleComp HashSpec (α × Nat) :=
  OracleComp.construct (fun value => pure (value,0))
    (fun input _ next => do
      let answer ← liftM (HashSpec.query input)
      let result ← next answer
      pure (result.1,result.2+1)) program

theorem countHash_query_bind {α : Type} (input : Query)
    (next : BitVec 256 → OracleComp HashSpec α) :
    countHash (liftM (HashSpec.query input) >>= next) = (do
      let answer ← liftM (HashSpec.query input)
      let result ← countHash (next answer)
      pure (result.1,result.2+1)) := rfl

theorem eval_countHash {α : Type} (hash : Hash)
    (program : OracleComp HashSpec α) :
    evalWithAnswerFn hash (countHash program) =
      (evalWithAnswerFn hash program,SecurityVerifyCost.calls hash program) := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [countHash_query_bind,evalWithAnswerFn_bind,
        evalWithAnswerFn_pure,ih,SecurityVerifyCost.calls_query_bind]
      rfl

def semanticCheck (pk : PublicKey)
    (transcript : Transcript submission.sizes) :
    Forgery submission.sizes → OracleComp HashSpec AttackResult
  | .witness message wire => do
      let result ← countHash
        (GroupedBalancedSecurityCheckConditional67.program pk message wire)
      pure ⟨result.1 && transcript.freshMessage message,
        transcript.hashCalls + result.2⟩
  | .signature message wire => do
      let result ← countHash
        (GroupedBalancedSecurityCheckConditional67.program pk message wire)
      pure ⟨result.1 && transcript.freshSignature message wire,
        transcript.hashCalls + result.2⟩

theorem semantic_check_fixed
    (refinement : GroupedBalancedSecurityCheckConditional67.VerifierRefinement)
    (hash : Hash) (pk : PublicKey)
    (transcript : Transcript submission.sizes)
    (forgery : Forgery submission.sizes) :
    evalWithAnswerFn hash
      (GroupedBalancedSecurityJointInteraction67.actualInterface.check
        pk transcript forgery) =
    evalWithAnswerFn hash (semanticCheck pk transcript forgery) := by
  have first := GroupedBalancedSecurityCheckObservation67.check
    refinement hash pk transcript forgery
  cases forgery with
  | witness message wire =>
      simpa only [actualInterface,semanticCheck,
        GroupedBalancedSecurityCheckObservation67.referenceOutcome,
        evalWithAnswerFn_bind,evalWithAnswerFn_pure,
        eval_countHash] using first
  | signature message wire =>
      simpa only [actualInterface,semanticCheck,
        GroupedBalancedSecurityCheckObservation67.referenceOutcome,
        evalWithAnswerFn_bind,evalWithAnswerFn_pure,
        eval_countHash] using first

noncomputable def fullInterface (table : PointTable) : Interface where
  keygen := (tableInterface table).keygen
  sign := (tableInterface table).sign
  check := semanticCheck

theorem check_context
    (refinement : GroupedBalancedSecurityCheckConditional67.VerifierRefinement)
    {β : Type} (pk : PublicKey)
    (transcript : Transcript submission.sizes)
    (forgery : Forgery submission.sizes)
    (cache : QueryCache HashSpec)
    (next : AttackResult → OracleComp World β) :
    𝒮[observe
      ((actualInterface.check pk transcript forgery).liftComp World >>= next)
      cache] =
    𝒮[observe
      ((semanticCheck pk transcript forgery).liftComp World >>= next)
      cache] := by
  exact SecurityBytecode.contextual_equivalence_at _ _ next cache
    (fun hash _ => semantic_check_fixed refinement hash pk transcript forgery)

theorem interact_check_equivalent_generic
    (left right : Interface)
    (sameSign : ∀ secretKey request,
      left.sign secretKey request = right.sign secretKey request)
    (sameCheck : ∀ pk transcript forgery hash,
      evalWithAnswerFn hash (left.check pk transcript forgery) =
        evalWithAnswerFn hash (right.check pk transcript forgery))
    (secretKey : SecretKey)
    (adversary : Adversary submission.sizes) (pk : PublicKey)
    (rounds : Nat) (state : adversary.State)
    (transcript : Transcript submission.sizes)
    (cache : QueryCache HashSpec) :
    𝒮[observe
      (interactWith left adversary secretKey pk
        rounds state transcript) cache] =
    𝒮[observe
      (interactWith right adversary secretKey pk
        rounds state transcript) cache] := by
  induction rounds generalizing state transcript cache with
  | zero => rfl
  | succ rounds ih =>
      simp only [interactWith]
      cases action : adversary.step state <;> simp only
      case submit candidate =>
        have h := SecurityBytecode.contextual_equivalence
          (left.check pk transcript candidate)
          (right.check pk transcript candidate)
          (fun hash => sameCheck pk transcript candidate hash)
          (fun result => pure result) cache
        simpa only [bind_pure] using h
      case hash input resume =>
        change 𝒮[observe
          ((liftM (HashSpec.query input) : OracleComp HashSpec _).liftComp World >>= _)
          cache] =
          𝒮[observe
            ((liftM (HashSpec.query input) : OracleComp HashSpec _).liftComp World >>= _)
            cache]
        rw [SecurityBytecode.observe_hash_bind,
          SecurityBytecode.observe_hash_bind]
        apply evalSPMF_bind_congr
        intro result _
        exact ih (resume result.1) _ result.2
      case sign request resume =>
        split
        · rw [sameSign secretKey request]
          rw [SecurityBytecode.observe_hash_bind,
            SecurityBytecode.observe_hash_bind]
          apply evalSPMF_bind_congr
          intro result _
          exact ih (resume result.1.1) _ result.2
        · rfl
      case sample n resume =>
        have observe_coin_bind {β : Type}
            (next : Fin (n + 1) → OracleComp World β) :
            observe ((liftM (unifSpec.query n) : OracleComp World _) >>= next)
              cache =
              (do let answer ← liftM (unifSpec.query n)
                  observe (next answer) cache) := by
          unfold observe
          change (simulateQ implementation
            ((liftM (World.query (.inl n))) >>= next)).run' cache = _
          rw [run'_query_bind]
          change ((fun answer => (answer,cache)) <$>
            (liftM (unifSpec.query n) : ProbComp _) >>= _) = _
          simp only [map_eq_bind_pure_comp,Function.comp_apply,
            bind_assoc,pure_bind]
        rw [observe_coin_bind,observe_coin_bind]
        apply evalSPMF_bind_congr
        intro answer _
        exact ih (resume answer) transcript cache
      case step next => exact ih next transcript cache

theorem interact_check_equivalent
    (refinement : GroupedBalancedSecurityCheckConditional67.VerifierRefinement)
    (table : PointTable) (secretKey : SecretKey)
    (adversary : Adversary submission.sizes) (pk : PublicKey)
    (rounds : Nat) (state : adversary.State)
    (transcript : Transcript submission.sizes)
    (cache : QueryCache HashSpec) :
    𝒮[observe
      (interactWith (tableInterface table) adversary secretKey pk
        rounds state transcript) cache] =
    𝒮[observe
      (interactWith (fullInterface table) adversary secretKey pk
        rounds state transcript) cache] := by
  exact interact_check_equivalent_generic
    (tableInterface table) (fullInterface table)
    (fun _ _ => rfl)
    (fun pk transcript forgery hash =>
      semantic_check_fixed refinement hash pk transcript forgery)
    secretKey adversary pk rounds state transcript cache

theorem game_check_equivalent
    (refinement : GroupedBalancedSecurityCheckConditional67.VerifierRefinement)
    (table : PointTable) (secretKey : SecretKey)
    (adversary : Adversary submission.sizes) (rounds : Nat)
    (cache : QueryCache HashSpec) :
    𝒮[observe
      (gameWith (tableInterface table) adversary rounds secretKey) cache] =
    𝒮[observe
      (gameWith (fullInterface table) adversary rounds secretKey) cache] := by
  simp only [gameWith,tableInterface,fullInterface,
    OracleComp.liftComp_pure,pure_bind]
  exact interact_check_equivalent refinement table secretKey adversary
    (GroupedBalancedGraphMonitorSetupBound67.rootPublic table)
    rounds
    (adversary.initial
      (GroupedBalancedGraphMonitorSetupBound67.rootPublic table) (0 : Cache))
    {hashCalls := 3983} cache

noncomputable def jointFull
    (adversary : Adversary submission.sizes) (rounds : Nat) :
    ProbComp AttackResult := do
  let secretKey ← sampleSecretKey
  let answers ← $ᵗ PrivateTable
  let labels ← $ᵗ Labels
  let ghosts ← $ᵗ GroupedBalancedGlobalPaired67.GhostTable
  observe
    (gameWith (fullInterface (GroupedBalancedSecurityJointTable67.tableOf
      answers labels ghosts)) adversary rounds secretKey)
    (jointCache secretKey answers labels)

noncomputable def fullStoppedRisk
    (adversary : Adversary submission.sizes) (rounds : Nat) :
    ProbComp (Option AttackResult) := do
  let table ← $ᵗ PointTable
  let secretKey ← sampleSecretKey
  observe
    (SecurityCache.stopBefore (SourceHit secretKey)
      (gameWith (fullInterface table) adversary rounds secretKey))
    (GroupedBalancedPlantedCache67.planted table)

/-- Under the arbitrary-wire verifier refinement, the actual submitted
experiment has this exact fully semantic graph-view law. -/
theorem official_full_joint
    (refinement : GroupedBalancedSecurityCheckConditional67.VerifierRefinement)
    (adversary : Adversary submission.sizes) (rounds : Nat) :
    𝒮[submission.securityExperiment adversary rounds] =
      𝒮[jointFull adversary rounds] := by
  calc
    _ = 𝒮[GroupedBalancedSecurityOfficialHybrid67.jointSemantic
      adversary rounds] := by
        simpa only [GroupedBalancedSecurityOfficialHybrid67.jointSemantic] using
          GroupedBalancedSecurityOfficialJoint67.official_joint_semantic
            adversary rounds
    _ = _ := by
      unfold GroupedBalancedSecurityOfficialHybrid67.jointSemantic jointFull
      apply evalSPMF_bind_congr
      intro secretKey _
      apply evalSPMF_bind_congr
      intro answers _
      apply evalSPMF_bind_congr
      intro labels _
      apply evalSPMF_bind_congr
      intro ghosts _
      simpa only [semanticInterface_tableOf] using
        game_check_equivalent refinement
          (GroupedBalancedSecurityJointTable67.tableOf answers labels ghosts)
          secretKey adversary rounds (jointCache secretKey answers labels)

/-- The source-hit stopped experiment is a uniform point-table experiment,
matching the organizer's sampling order and retaining the full option result. -/
theorem full_stop_uniform_table
    (adversary : Adversary submission.sizes) (rounds : Nat) :
    𝒮[do
      let secretKey ← sampleSecretKey
      let answers ← $ᵗ PrivateTable
      let labels ← $ᵗ Labels
      let ghosts ← $ᵗ GroupedBalancedGlobalPaired67.GhostTable
      observe
        (SecurityCache.stopBefore (SourceHit secretKey)
          (gameWith (fullInterface
            (GroupedBalancedSecurityJointTable67.tableOf answers labels ghosts))
            adversary rounds secretKey))
        (plantedCache answers labels ghosts)] =
      𝒮[fullStoppedRisk adversary rounds] := by
  calc
    _ = 𝒮[do
          let secretKey ← sampleSecretKey
          let table ← $ᵗ PointTable
          observe
            (SecurityCache.stopBefore (SourceHit secretKey)
              (gameWith (fullInterface table) adversary rounds secretKey))
            (GroupedBalancedPlantedCache67.planted table)] := by
          apply evalSPMF_bind_congr
          intro secretKey _
          simpa only [plantedCache] using
            (GroupedBalancedSecurityJointTable67.uniform_table
              (fun table => observe
                (SecurityCache.stopBefore (SourceHit secretKey)
                  (gameWith (fullInterface table) adversary rounds secretKey))
                (GroupedBalancedPlantedCache67.planted table)))
    _ = _ := evalSPMF_bind_bind_swap _ _ _

/-- The actual submitted success event is charged to one completed-reference
win-or-source-hit event in a planted uniform-table execution. No additive hit
probability is introduced. -/
theorem official_le_full_stopped_risk
    (refinement : GroupedBalancedSecurityCheckConditional67.VerifierRefinement)
    (adversary : Adversary submission.sizes) (rounds : Nat)
    (event : AttackResult → Prop) :
    Pr[event | submission.securityExperiment adversary rounds] ≤
      Pr[StoppedRisk event | fullStoppedRisk adversary rounds] := by
  have dist := official_full_joint refinement adversary rounds
  have same : Pr[event | submission.securityExperiment adversary rounds] =
      Pr[event | jointFull adversary rounds] :=
    probEvent_congr' (fun _ _ => Iff.rfl) dist
  rw [same]
  have raw :
      Pr[event | jointFull adversary rounds] ≤
      Pr[StoppedRisk event | do
        let secretKey ← sampleSecretKey
        let answers ← $ᵗ PrivateTable
        let labels ← $ᵗ Labels
        let ghosts ← $ᵗ GroupedBalancedGlobalPaired67.GhostTable
        observe
          (SecurityCache.stopBefore (SourceHit secretKey)
            (gameWith (fullInterface
              (GroupedBalancedSecurityJointTable67.tableOf answers labels ghosts))
              adversary rounds secretKey))
          (plantedCache answers labels ghosts)] := by
    unfold jointFull
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
      (gameWith (fullInterface
        (GroupedBalancedSecurityJointTable67.tableOf answers labels ghosts))
        adversary rounds secretKey) event
  exact raw.trans_eq (probEvent_congr' (fun _ _ => Iff.rfl)
    (full_stop_uniform_table adversary rounds))

#print axioms semantic_check_fixed
#print axioms check_context
#print axioms interact_check_equivalent
#print axioms game_check_equivalent
#print axioms official_full_joint
#print axioms full_stop_uniform_table
#print axioms official_le_full_stopped_risk

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityFullSemantic67
