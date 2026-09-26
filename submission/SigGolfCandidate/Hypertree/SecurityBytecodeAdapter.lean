import SigGolfCandidate.Hypertree.SecurityBytecodeInteraction

/-! Inlined from SigGolfCandidate.Hypertree.SecurityBytecodeExperiment; its only importer was SigGolfCandidate.Hypertree.SecurityBytecodeAdapter. -/
section
namespace SigGolfCandidate.Hypertree.SecurityBytecode
open SigGolf OracleComp OracleSpec SecurityCache SecurityGraphHidden
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

theorem observe_uniform_bind {α β : Type} (program : ProbComp α) (next : α → OracleComp World β)
    (cache : QueryCache HashSpec) :
    observe (program.liftComp World >>= next) cache =
      (program >>= fun value => observe (next value) cache) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp [observe]
  | query_bind n continuation ih =>
    rw [OracleComp.liftComp_bind,bind_assoc]
    change observe ((liftM (unifSpec.query n) : OracleComp World _) >>= _) cache = _
    rw [observe_coin_bind,bind_assoc]
    apply bind_congr
    intro answer
    exact ih answer

def secretKeyedWith (scheme : Interface) (adversary : Adversary submission.sizes) (rounds : Nat) (secretKey : SecretKey) :
    OracleComp World AttackResult := do
  let result ← (scheme.keygen secretKey).liftComp World
  let some (pk,cache) := result.1 | pure ⟨false,result.2⟩
  interactWith scheme adversary secretKey pk rounds (adversary.initial pk cache) {hashCalls:=result.2}

theorem experiment_secretKeyed (scheme : Interface) (adversary : Adversary submission.sizes) (rounds : Nat) :
    experimentWith scheme adversary rounds = (do let secretKey←sampleSecretKey; observe (secretKeyedWith scheme adversary rounds secretKey) ∅) := by
  change observe (sampleSecretKey.liftComp World >>= fun secretKey => secretKeyedWith scheme adversary rounds secretKey) ∅ = _
  exact observe_uniform_bind sampleSecretKey _ ∅

/-- Generic initial-key coupling. Both continuations use the same generated key,
cache, and initial query counter; cached key knowledge justifies adaptive signing. -/
theorem secretKeyed_equivalent_generic (left right : Interface) (adversary : Adversary submission.sizes)
    (rounds : Nat) (secretKey : SecretKey) (fact : PublicKey → Hash → Prop)
    (keyEq : ∀ hash, evalWithAnswerFn hash (left.keygen secretKey)=evalWithAnswerFn hash (right.keygen secretKey))
    (keyKnown : ∀ result ∈ support (runHash (right.keygen secretKey) ∅),
      ∀ pk cache, result.1.1=some (pk,cache) → Knows result.2 (fact pk))
    (signEq : ∀ pk hash, fact pk hash → ∀ request,
      evalWithAnswerFn hash (left.sign secretKey request)=evalWithAnswerFn hash (right.sign secretKey request))
    (checkEq : ∀ pk hash transcript candidate,
      evalWithAnswerFn hash (left.check pk transcript candidate)=evalWithAnswerFn hash (right.check pk transcript candidate)) :
    𝒮[observe (secretKeyedWith left adversary rounds secretKey) ∅]=𝒮[observe (secretKeyedWith right adversary rounds secretKey) ∅] := by
  unfold secretKeyedWith
  calc
    _ = 𝒮[observe ((right.keygen secretKey).liftComp World >>= fun result =>
      match result.1 with
      | some (pk,cache) => interactWith left adversary secretKey pk rounds (adversary.initial pk cache) {hashCalls:=result.2}
      | _ => pure ⟨false,result.2⟩) ∅] :=
      contextual_equivalence _ _ keyEq _ ∅
    _ = _ := by
      rw [observe_hash_bind,observe_hash_bind]
      apply evalSPMF_bind_congr
      intro result mem
      cases value : result.1.1 with
      | none => rfl
      | some pair =>
        rcases pair with ⟨pk,cache⟩
        simp only
        exact interact_equivalent_generic left right (fact pk) adversary secretKey pk rounds
          (adversary.initial pk cache) {hashCalls:=result.1.2} result.2 (keyKnown result mem pk cache value)
          (signEq pk) (checkEq pk)

theorem secretKeyed_equivalent (adversary : Adversary submission.sizes) (rounds : Nat) (secretKey : SecretKey) :
    𝒮[observe (secretKeyedWith actualInterface adversary rounds secretKey) ∅]=
      𝒮[observe (secretKeyedWith referenceInterface adversary rounds secretKey) ∅] := by
  apply secretKeyed_equivalent_generic actualInterface referenceInterface adversary rounds secretKey
    (fun pk hash => Reference.keygen hash secretKey=pk) (fun hash => keygen_equivalent hash secretKey)
  · intro result mem pk cache value hash agree
    have eq := (runHash_support_agrees (referenceInterface.keygen secretKey) ∅ result mem hash agree).2
    have publicEq := congrArg (fun output => output.1.map Prod.fst) eq
    simp only [referenceInterface,referenceKeygen,evalWithAnswerFn_bind,evalWithAnswerFn_pure,
      eval_countHash,SecurityReference.eval_keygen,value,Option.map_some] at publicEq
    exact Option.some.inj publicEq
  · intro _ hash _ request; exact sign_equivalent hash secretKey request
  · intro pk hash transcript candidate; exact check_equivalent hash pk transcript candidate

/-- Exact shared-random-oracle security distribution. This includes private coins,
both forgery forms, supplied caches, replay history, lifetime, and total call counts. -/
theorem experiment_equivalent (adversary : Adversary submission.sizes) (rounds : Nat) :
    𝒮[submission.securityExperiment adversary rounds]=𝒮[experimentWith referenceInterface adversary rounds] := by
  rw [←actual_experiment,experiment_secretKeyed,experiment_secretKeyed]
  apply evalSPMF_bind_congr
  intro secretKey _
  exact secretKeyed_equivalent adversary rounds secretKey

/-- info: 'SigGolfCandidate.Hypertree.SecurityBytecode.experiment_equivalent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms experiment_equivalent
end SigGolfCandidate.Hypertree.SecurityBytecode

end

namespace SigGolfCandidate.Hypertree.SecurityBytecodeAdapter
open SigGolf OracleComp OracleSpec SecurityDerivation SecurityGameHop SecurityBytecode
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

/-- Resolve the private derivation port while retaining the attacker's private coins. -/
def translate (secretKey : SecretKey) : QueryImpl GameWorld (OracleComp World) :=
  HasQuery.toQueryImpl (spec := unifSpec) (m := OracleComp World) +
    fun query => (realImplementation secretKey query).liftComp World

abbrev resolve {α : Type} (secretKey : SecretKey) (program : OracleComp GameWorld α) : OracleComp World α :=
  simulateQ (translate secretKey) program

theorem resolve_split {α : Type} (secretKey : SecretKey) (program : OracleComp SplitWorld α) :
    resolve secretKey (program.liftComp GameWorld) =
      (simulateQ (realImplementation secretKey) program).liftComp World := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
    cases query <;>
      simp [resolve, translate, realImplementation, realDerivation] at ih ⊢ <;>
      exact bind_congr ih

theorem resolve_hash {α : Type} (secretKey : SecretKey) (program : OracleComp HashSpec α) :
    resolve secretKey (program.liftComp GameWorld) = program.liftComp World := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
    simp only [resolve] at ih ⊢
    simp [OracleComp.liftComp_bind, OracleComp.liftComp_query, translate,
      realImplementation, simulateQ_bind] at ih ⊢
    exact bind_congr ih

theorem counted_bind {α β : Type} (program : OracleComp GameWorld α)
    (next : α → OracleComp GameWorld β) :
    SecurityBudget.counted (program >>= next) = (do
      let first ← SecurityBudget.counted program
      let second ← SecurityBudget.counted (next first.1)
      pure (second.1, first.2 + second.2)) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query tail ih =>
    simp only [bind_assoc, SecurityBudget.counted_query_bind, ih, pure_bind]
    apply bind_congr
    intro answer
    apply bind_congr
    intro first
    apply bind_congr
    intro second
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem counted_map {α β : Type} (f : α → β) (program : OracleComp GameWorld α) :
    SecurityBudget.counted (f <$> program) =
      (fun result => (f result.1,result.2)) <$> SecurityBudget.counted program := by
  simp only [map_eq_bind_pure_comp, Function.comp_def, counted_bind, SecurityBudget.counted_pure, pure_bind, Nat.add_zero]

theorem resolve_counted_split {α : Type} (secretKey : SecretKey) (program : OracleComp SplitWorld α) :
    resolve secretKey (SecurityBudget.counted (program.liftComp GameWorld)) =
      (countHash (simulateQ (realImplementation secretKey) program)).liftComp World := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
    simp only [OracleComp.liftComp_bind, OracleComp.liftComp_query]
    change resolve secretKey (SecurityBudget.counted (liftM (GameWorld.query (.inr query)) >>= _)) = _
    rw [SecurityBudget.counted_query_bind]
    cases query <;>
      simp [resolve, translate, realImplementation, realDerivation, SecurityBudget.charge,
        countHash_query_bind] at ih ⊢ <;>
      exact bind_congr (fun answer => by rw [ih])

theorem resolve_counted_hash {α : Type} (secretKey : SecretKey) (program : OracleComp HashSpec α) :
    resolve secretKey (SecurityBudget.counted (program.liftComp GameWorld)) =
      (countHash program).liftComp World := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
    simp only [OracleComp.liftComp_bind, OracleComp.liftComp_query]
    change resolve secretKey (SecurityBudget.counted (liftM (GameWorld.query (.inr (.inr query))) >>= _)) = _
    rw [SecurityBudget.counted_query_bind]
    simp [resolve, translate, realImplementation, SecurityBudget.charge,
      countHash_query_bind] at ih ⊢
    exact bind_congr (fun answer => by rw [ih])

/-- Add the already charged prefix to the reference experiment's local count. -/
def project (initial : Nat) (result : SecurityExperiment.Result × Nat) : AttackResult :=
  ⟨result.1.won, initial + result.2⟩

theorem project_query (secretKey : SecretKey) (initial : Nat) (query : GameWorld.Domain)
    (next : GameWorld.Range query → OracleComp GameWorld SecurityExperiment.Result) :
    project initial <$> resolve secretKey (SecurityBudget.counted (liftM (GameWorld.query query) >>= next)) =
      (translate secretKey query >>= fun answer =>
        project (initial + SecurityBudget.charge query) <$> resolve secretKey (SecurityBudget.counted (next answer))) := by
  simp only [SecurityBudget.counted_query_bind, resolve, simulateQ_bind, simulateQ_spec_query,
    simulateQ_pure, map_bind, map_pure]
  simp only [map_eq_bind_pure_comp, Function.comp_def, project, Nat.add_comm, Nat.add_left_comm]

theorem project_bind {α : Type} (secretKey : SecretKey) (initial : Nat) (program : OracleComp GameWorld α)
    (next : α → OracleComp GameWorld SecurityExperiment.Result) :
    project initial <$> resolve secretKey (SecurityBudget.counted (program >>= next)) =
      (resolve secretKey (SecurityBudget.counted program) >>= fun result =>
        project (initial + result.2) <$> resolve secretKey (SecurityBudget.counted (next result.1))) := by
  simp only [counted_bind, resolve, simulateQ_bind, simulateQ_pure, map_bind, map_pure]
  simp only [map_eq_bind_pure_comp, Function.comp_def, project, Nat.add_assoc]

theorem check (secretKey : SecretKey) (pk : PublicKey) (transcript : Transcript submission.sizes)
    (initial : Nat) (candidate : Forgery submission.sizes) :
    project initial <$> resolve secretKey (SecurityBudget.counted (SecurityExperiment.check pk transcript candidate)) =
      (referenceCheck pk {transcript with hashCalls := initial} candidate).liftComp World := by
  cases candidate <;>
    simp only [SecurityExperiment.check, counted_bind, SecurityBudget.counted_pure, pure_bind, Nat.add_zero,
      resolve, simulateQ_bind, simulateQ_pure, map_bind, map_pure, referenceCheck,
      OracleComp.liftComp_bind, OracleComp.liftComp_pure]
  all_goals
    rw [show simulateQ (translate secretKey) (SecurityBudget.counted ((SecurityVerify.verifyCompact _ _ _).liftComp GameWorld)) =
      (countHash (SecurityVerify.verifyCompact _ _ _)).liftComp World from resolve_counted_hash secretKey _]
    rfl

theorem interaction (adversary : Adversary submission.sizes) (secretKey : SecretKey) (pk : PublicKey)
    (rounds : Nat) (state : adversary.State) (transcript : Transcript submission.sizes) (initial : Nat) :
    project initial <$> resolve secretKey (SecurityBudget.counted (SecurityExperiment.interact adversary pk rounds state transcript)) =
      interactWith referenceInterface adversary secretKey pk rounds state {transcript with hashCalls := initial} := by
  induction rounds generalizing state transcript initial with
  | zero => simp [SecurityExperiment.interact, interactWith, project]
  | succ rounds ih =>
    simp only [SecurityExperiment.interact, interactWith]
    cases action : adversary.step state <;> simp only
    case submit candidate => exact check secretKey pk transcript initial candidate
    case hash input resume =>
      rw [project_query]
      change ((liftM (HashSpec.query input) : OracleComp World _) >>= _) = _
      exact bind_congr (fun answer => ih (resume answer) transcript (initial+1))
    case sign request resume =>
      split
      · rw [project_bind, resolve_counted_split, SecurityExperiment.simulate_signWire]
        apply bind_congr
        intro result
        rw [ih]
        rfl
      · simp [project]
    case sample n resume =>
      rw [project_query]
      exact bind_congr (fun answer => ih (resume answer) transcript initial)
    case step next => exact ih next transcript initial

theorem secretKeyed_program (adversary : Adversary submission.sizes) (rounds : Nat) (secretKey : SecretKey) :
    project 0 <$> resolve secretKey (SecurityBudget.counted (SecurityExperiment.program KeygenFunctional.zeroCache adversary rounds)) =
      secretKeyedWith referenceInterface adversary rounds secretKey := by
  unfold SecurityExperiment.program
  rw [project_bind, resolve_counted_split, SecurityIdealKeygen.simulate_keygen]
  simp only [secretKeyedWith, referenceInterface, referenceKeygen, OracleComp.liftComp_bind,
    OracleComp.liftComp_pure, bind_assoc, pure_bind, Nat.zero_add]
  apply bind_congr
  intro result
  exact interaction adversary secretKey result.1 rounds (adversary.initial result.1 KeygenFunctional.zeroCache) {} result.2

theorem simulate_real {α : Type} (secretKey : SecretKey) (program : OracleComp GameWorld α) :
    simulateQ (realGameOracle secretKey) program = simulateQ SecurityCache.implementation (resolve secretKey program) := by
  have hash_query (query : Query) :
      simulateQ SecurityCache.implementation ((liftM (HashSpec.query query) : OracleComp HashSpec _).liftComp World) =
        (randomOracle (spec := HashSpec) query : StateT (QueryCache HashSpec) ProbComp _) := by
    rw [OracleComp.liftComp_query]
    change simulateQ SecurityCache.implementation (liftM (World.query (.inr query))) = _
    rw [simulateQ_spec_query]
    rfl
  have step (query : GameWorld.Domain) :
      simulateQ SecurityCache.implementation (translate secretKey query) = realGameOracle secretKey query := by
    cases query with
    | inl coin => rfl
    | inr query =>
      cases query with
      | inl slot => exact hash_query (input secretKey slot)
      | inr query => exact hash_query query
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
    simp only [resolve, simulateQ_bind, simulateQ_spec_query, step] at ih ⊢
    exact bind_congr ih

/-- The organizer-shaped reference interface is exactly the counted, secretKeyed reduction game. -/
theorem reference_experiment (adversary : Adversary submission.sizes) (rounds : Nat) :
    SecurityExperiment.realExperiment KeygenFunctional.zeroCache adversary rounds =
      experimentWith referenceInterface adversary rounds := by
  rw [experiment_secretKeyed]
  unfold SecurityExperiment.realExperiment
  apply bind_congr
  intro secretKey
  rw [simulate_real]
  calc
    _ = SecurityGraphHidden.observe
      (project 0 <$> resolve secretKey (SecurityBudget.counted (SecurityExperiment.program KeygenFunctional.zeroCache adversary rounds))) ∅ := by
        simp only [SecurityGraphHidden.observe, simulateQ_map, StateT.run'_eq,
          StateT.run_map, Functor.map_map, project, Nat.zero_add]
    _ = _ := congrArg (fun program => SecurityGraphHidden.observe program ∅) (secretKeyed_program adversary rounds secretKey)

/-- Exact security-game distribution for the actual four-program submission. -/
theorem experiment_equivalent (adversary : Adversary submission.sizes) (rounds : Nat) :
    𝒮[submission.securityExperiment adversary rounds] =
      𝒮[SecurityExperiment.realExperiment KeygenFunctional.zeroCache adversary rounds] := by
  rw [reference_experiment]
  exact SecurityBytecode.experiment_equivalent adversary rounds

theorem probability_eq (adversary : Adversary submission.sizes) (rounds : Nat) (event : AttackResult → Prop) :
    Pr[event | submission.securityExperiment adversary rounds] =
      Pr[event | SecurityExperiment.realExperiment KeygenFunctional.zeroCache adversary rounds] := by
  simp only [probEvent_def, experiment_equivalent]

/-- info: 'SigGolfCandidate.Hypertree.SecurityBytecodeAdapter.experiment_equivalent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms experiment_equivalent

end SigGolfCandidate.Hypertree.SecurityBytecodeAdapter
