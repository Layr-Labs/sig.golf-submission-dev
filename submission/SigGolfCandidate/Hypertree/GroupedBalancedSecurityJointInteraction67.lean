import SigGolfCandidate.Hypertree.GroupedBalancedSecurityJointContext67
import SigGolfCandidate.Hypertree.SecurityBytecodeCache

/-! Adaptive official security interaction with machine keygen/sign replaced
by the graph-view root and two-query signer, retaining all official counts. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityJointInteraction67
open SigGolf OracleComp OracleSpec Reference SecurityCache SecurityGraphHidden
open GroupedBalancedPrivateFactors67 GroupedBalancedSecurityGraph67
open GroupedBalancedSecurityJointPresample67
open GroupedBalancedSecurityJointTable67
open GroupedBalancedSecuritySourceHybrid67
open GroupedBalancedSecurityJointContext67
open scoped Classical
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

private abbrev submission := GroupedBalancedProgram67ByteSign.submission

structure Interface where
  keygen : SecretKey → OracleComp HashSpec (Option (PublicKey × Cache) × Nat)
  sign : SecretKey → SigningRequest →
    OracleComp HashSpec (Option (Bytes submission.sizes.signature) × Nat)
  check : PublicKey → Transcript submission.sizes →
    Forgery submission.sizes → OracleComp HashSpec AttackResult

def actualInterface : Interface where
  keygen secretKey := GroupedBalancedSecurityObservedPhases67.view <$>
    submission.run .keygen secretKey
  sign secretKey request := GroupedBalancedSecurityObservedPhases67.view <$>
    submission.signingOracle secretKey request
  check := submission.checkForgery

def recordView (transcript : Transcript submission.sizes)
    (message : Message)
    (result : Option (Bytes submission.sizes.signature) × Nat) :
    Transcript submission.sizes :=
  { signed := match result.1 with
      | none => transcript.signed
      | some wire => (message,wire) :: transcript.signed
    signingRequests := transcript.signingRequests + 1
    hashCalls := transcript.hashCalls + result.2 }

def interactWith (scheme : Interface)
    (adversary : Adversary submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey) :
    Nat → adversary.State → Transcript submission.sizes →
      OracleComp World AttackResult
  | 0, _, transcript => pure ⟨false,transcript.hashCalls⟩
  | rounds + 1, state, transcript =>
      match adversary.step state with
      | .submit candidate =>
          (scheme.check pk transcript candidate).liftComp World
      | .hash input resume => do
          let answer ← liftM (HashSpec.query input)
          interactWith scheme adversary secretKey pk rounds (resume answer)
            { transcript with hashCalls := transcript.hashCalls + 1 }
      | .sign request resume => do
          if transcript.signingRequests < LIFETIME then
            let result ← (scheme.sign secretKey request).liftComp World
            interactWith scheme adversary secretKey pk rounds
              (resume result.1) (recordView transcript request.message result)
          else pure ⟨false,transcript.hashCalls⟩
      | .sample n resume => do
          let answer ← liftM (unifSpec.query n)
          interactWith scheme adversary secretKey pk rounds (resume answer)
            transcript
      | .step next => interactWith scheme adversary secretKey pk rounds
          next transcript

noncomputable def semanticInterface (answers : PrivateTable) (labels : Labels)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable) :
    Interface where
  keygen _ := semanticKeygen answers labels ghosts
  sign secretKey request := semanticSign secretKey
    (tableOf answers labels ghosts) request
  check := actualInterface.check

theorem interact_equivalent
    (secretKey : SecretKey) (answers : PrivateTable) (labels : Labels)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable)
    (adversary : Adversary submission.sizes) (pk : PublicKey)
    (rounds : Nat) (state : adversary.State)
    (transcript : Transcript submission.sizes)
    (cache : QueryCache HashSpec)
    (known : Known secretKey answers labels cache) :
    𝒮[observe (interactWith
      actualInterface adversary secretKey pk
      rounds state transcript) cache] =
    𝒮[observe (interactWith
      (semanticInterface answers labels ghosts) adversary secretKey pk
      rounds state transcript) cache] := by
  induction rounds generalizing state transcript cache with
  | zero => rfl
  | succ rounds ih =>
      simp only [interactWith]
      cases action : adversary.step state <;> simp only
      case submit candidate => rfl
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
        intro result member
        exact ih (resume result.1) _ result.2
          (SecurityBytecode.Knows.after _ cache known result member)
      case sign request resume =>
        split
        · calc
            _ = 𝒮[observe
              (((semanticInterface answers labels ghosts).sign secretKey request).liftComp World >>=
                fun result => interactWith
                  actualInterface adversary secretKey pk
                  rounds (resume result.1)
                  (recordView transcript request.message result))
              cache] :=
                SecurityBytecode.contextual_equivalence_at _ _ _ cache
                  (fun hash agrees => sign_fixed secretKey answers labels ghosts
                    hash (known hash agrees) request)
            _ = _ := by
              rw [SecurityBytecode.observe_hash_bind,
                SecurityBytecode.observe_hash_bind]
              apply evalSPMF_bind_congr
              intro result member
              exact ih (resume result.1.1) _ result.2
                (SecurityBytecode.Knows.after _ cache known result member)
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
          simp only [map_eq_bind_pure_comp, Function.comp_apply,
            bind_assoc, pure_bind]
        rw [observe_coin_bind, observe_coin_bind]
        apply evalSPMF_bind_congr
        intro answer _
        exact ih (resume answer) transcript cache known
      case step next => exact ih next transcript cache known

def gameWith (scheme : Interface)
    (adversary : Adversary submission.sizes) (rounds : Nat)
    (secretKey : SecretKey) : OracleComp World AttackResult := do
  let result ← (scheme.keygen secretKey).liftComp World
  let some (pk, cache) := result.1 | pure ⟨false,result.2⟩
  interactWith scheme adversary secretKey pk rounds
    (adversary.initial pk cache) {hashCalls := result.2}

/-- Exact distributional replacement for the full adaptive bytecode
interaction, conditional only on starting from the jointly presampled cache.
The returned `AttackResult` keeps the official 3983 keygen calls and 122548
calls per successful sign request. -/
theorem game_equivalent (secretKey : SecretKey)
    (answers : PrivateTable) (labels : Labels)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable)
    (adversary : Adversary submission.sizes) (rounds : Nat) :
    𝒮[observe (gameWith actualInterface
      adversary rounds secretKey) (jointCache secretKey answers labels)] =
    𝒮[observe (gameWith (semanticInterface answers labels ghosts)
      adversary rounds secretKey) (jointCache secretKey answers labels)] := by
  unfold gameWith
  let pk := GroupedBalancedGraphMonitorSetupBound67.rootPublic
    (tableOf answers labels ghosts)
  calc
    _ = 𝒮[observe ((semanticKeygen answers labels ghosts).liftComp World >>= fun result =>
      match result.1 with
      | some (publicKey, publicCache) =>
          interactWith actualInterface
            adversary secretKey publicKey rounds
            (adversary.initial publicKey publicCache) {hashCalls := result.2}
      | _ => pure ⟨false,result.2⟩)
      (jointCache secretKey answers labels)] :=
        keygen_context secretKey answers labels ghosts
          (jointCache secretKey answers labels)
          (known_initial secretKey answers labels) _
    _ = _ := by
      simp only [semanticKeygen,OracleComp.liftComp_pure,pure_bind]
      exact interact_equivalent secretKey answers labels ghosts
        adversary pk rounds (adversary.initial pk (0 : Cache))
        {hashCalls := 3983}
        (jointCache secretKey answers labels)
        (known_initial secretKey answers labels)

theorem record_view (transcript : Transcript submission.sizes)
    (message : Message)
    (result : RunResult (Bytes submission.sizes.signature)) :
    recordView transcript message
      (GroupedBalancedSecurityObservedPhases67.view result) =
      transcript.record message result := by
  cases result with
  | mk value finished cycles calls blocks =>
      cases value <;> rfl

theorem actual_interact (adversary : Adversary submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey)
    (rounds : Nat) (state : adversary.State)
    (transcript : Transcript submission.sizes) :
    interactWith actualInterface adversary secretKey pk rounds state transcript =
      submission.interact adversary secretKey pk rounds state transcript := by
  induction rounds generalizing state transcript with
  | zero => rfl
  | succ rounds ih =>
      simp only [interactWith,Submission.interact]
      cases action : adversary.step state <;> simp only [action] at *
      case submit candidate => rfl
      case hash input resume => simp only [ih]
      case sign request resume =>
        split
        · change ((GroupedBalancedSecurityObservedPhases67.view <$>
            submission.signingOracle secretKey request).liftComp World >>= _) = _
          rw [OracleComp.liftComp_map,bind_map_left]
          apply bind_congr
          intro result
          change interactWith actualInterface adversary secretKey pk rounds
            (resume result.value)
            (recordView transcript request.message
              (GroupedBalancedSecurityObservedPhases67.view result)) = _
          rw [record_view]
          exact ih _ _
        · rfl
      case sample n resume => simp only [ih]
      case step next => exact ih next transcript

theorem actual_game (adversary : Adversary submission.sizes)
    (rounds : Nat) (secretKey : SecretKey) :
    gameWith actualInterface adversary rounds secretKey =
      (do
        let result ← (submission.run .keygen secretKey).liftComp World
        let some (pk, cache) := result.value |
          pure ⟨false,result.hashCalls⟩
        submission.interact adversary secretKey pk rounds
          (adversary.initial pk cache) {hashCalls := result.hashCalls}) := by
  unfold gameWith
  simp only [actualInterface,OracleComp.liftComp_map,bind_map_left,
    GroupedBalancedSecurityObservedPhases67.view]
  apply bind_congr
  intro result
  cases value : result.value with
  | none => rfl
  | some pair =>
      rcases pair with ⟨pk, cache⟩
      exact actual_interact adversary secretKey pk rounds
        (adversary.initial pk cache) {hashCalls := result.hashCalls}

theorem observe_uniform_bind {α β : Type}
    (program : ProbComp α) (next : α → OracleComp World β)
    (cache : QueryCache HashSpec) :
    observe (program.liftComp World >>= next) cache =
      (program >>= fun value => observe (next value) cache) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp [observe]
  | query_bind n continuation ih =>
      rw [OracleComp.liftComp_bind,bind_assoc]
      change observe ((liftM (unifSpec.query n) : OracleComp World _) >>= _)
        cache = _
      have coin {γ : Type} (after : Fin (n + 1) → OracleComp World γ) :
          observe ((liftM (unifSpec.query n) : OracleComp World _) >>= after)
            cache =
            (do let answer ← liftM (unifSpec.query n)
                observe (after answer) cache) := by
        unfold observe
        change (simulateQ implementation
          ((liftM (World.query (.inl n))) >>= after)).run' cache = _
        rw [run'_query_bind]
        change ((fun answer => (answer,cache)) <$>
          (liftM (unifSpec.query n) : ProbComp _) >>= _) = _
        simp only [map_eq_bind_pure_comp,Function.comp_apply,
          bind_assoc,pure_bind]
      rw [coin,bind_assoc]
      apply bind_congr
      intro answer
      exact ih answer

theorem actual_experiment (adversary : Adversary submission.sizes)
    (rounds : Nat) :
    (withRandomness do
      let secretKey ← liftM sampleSecretKey
      gameWith actualInterface adversary rounds secretKey) =
    submission.securityExperiment adversary rounds := by
  unfold Submission.securityExperiment
  congr 1
  apply bind_congr
  intro secretKey
  simp only [gameWith,actualInterface,OracleComp.liftComp_map,
    bind_map_left,GroupedBalancedSecurityObservedPhases67.view]
  apply bind_congr
  intro result
  cases result.value with
  | none => rfl
  | some pair =>
      rcases pair with ⟨pk,cache⟩
      exact actual_interact adversary secretKey pk rounds
        (adversary.initial pk cache) {hashCalls := result.hashCalls}

theorem official_game (adversary : Adversary submission.sizes)
    (rounds : Nat) :
    𝒮[submission.securityExperiment adversary rounds] =
    𝒮[do
      let secretKey ← sampleSecretKey
      observe (gameWith actualInterface adversary rounds secretKey) ∅] := by
  rw [←actual_experiment]
  have h : (withRandomness do
      let secretKey ← liftM sampleSecretKey
      gameWith actualInterface adversary rounds secretKey) =
      observe (sampleSecretKey.liftComp World >>=
        fun secretKey => gameWith actualInterface adversary rounds secretKey) ∅ := rfl
  rw [h]
  rw [observe_uniform_bind]

#print axioms interact_equivalent
#print axioms game_equivalent
#print axioms official_game

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityJointInteraction67
