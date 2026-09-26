import SigGolfCandidate.Hypertree.GroupedBalancedPlantedSecretKeyHop67
import SigGolfCandidate.Hypertree.SecurityGraphHidden
import SigGolfCandidate.Hypertree.SecurityVerifyCost
import SigGolfCandidate.Hypertree.SecurityBudget

/-! The graph organizer's GameWorld meter counts actual HashSpec queries
after translating its typed private derivation and public query ports. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityCounterCore67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGameWorld67 GroupedBalancedGraphViewWorld67
open scoped Classical

theorem resolve_bind {α β : Type} (secretKey : SecretKey)
    (program : OracleComp SecurityGameHop.GameWorld α)
    (next : α → OracleComp SecurityGameHop.GameWorld β) :
    resolve secretKey (program >>= next) =
      resolve secretKey program >>= fun answer =>
        resolve secretKey (next answer) := by
  simp only [resolve, simulateQ_bind]

theorem resolve_pure {α : Type} (secretKey : SecretKey)
    (value : α) :
    resolve secretKey (pure value) = pure value := by
  rfl

theorem counted_resolve {α : Type} (secretKey : SecretKey)
    (program : OracleComp SecurityGameHop.GameWorld α) :
    resolve secretKey (SecurityBudget.counted program) =
      GroupedBalancedGraphViewWorld67.counted (resolve secretKey program) := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      cases query with
      | inl n =>
          simp only [SecurityBudget.counted_query_bind, resolve_bind,
            resolve_pure, resolve_coin, SecurityBudget.charge]
          exact bind_congr (fun answer => by
            rw [ih answer]
            rfl)
      | inr query =>
          cases query with
          | inl slot =>
              cases slot with
              | chain address =>
                  simp only [SecurityBudget.counted_query_bind, resolve_bind,
                    resolve_pure, SecurityBudget.charge]
                  exact bind_congr (fun answer => by
                    rw [ih answer]
                    rfl)
              | randomizer message =>
                  simp only [SecurityBudget.counted_query_bind, resolve_bind,
                    resolve_pure, resolve_randomizer, SecurityBudget.charge]
                  exact bind_congr (fun answer => by
                    rw [ih answer]
                    rfl)
          | inr input =>
              simp only [SecurityBudget.counted_query_bind, resolve_bind,
                resolve_pure, resolve_public, SecurityBudget.charge]
              exact bind_congr (fun answer => by
                rw [ih answer]
                rfl)

#print axioms counted_resolve

/-- The legacy graph-game counter is exactly the number of World hash queries
in the translated organizer. This equality includes private randomizer and
index reads, attacker queries, and final verifier queries. -/
theorem organizer_counted_resolve (sizes : Sizes)
    (encode : GroupedBalancedScheme67.Signature → Bytes sizes.signature)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (secretKey : SecretKey) (adversary : Adversary sizes)
    (publicCache : Cache) (rounds : Nat)
    (table : GroupedBalancedGraphPassive67.PointTable) :
    resolve secretKey
      (SecurityBudget.counted
        (GroupedBalancedGameWorldBudget67.organizerProgram sizes
          encode decodeWitness decodeSignature adversary
          publicCache rounds table)) =
      GroupedBalancedGraphViewWorld67.counted
        (GroupedBalancedGraphViewWorld67.ofView table
          (GroupedBalancedGraphIndexJointOrganizerBound67.organizerView sizes
            encode decodeWitness decodeSignature secretKey adversary
            publicCache rounds
            (GroupedBalancedGraphMonitorSetup67.cache table))) := by
  rw [counted_resolve,
    GroupedBalancedGameWorldBudget67.resolve_organizerProgram]

#print axioms organizer_counted_resolve

private theorem simulate_real {α : Type} (secretKey : SecretKey)
    (program : OracleComp SecurityGameHop.GameWorld α) :
    simulateQ (SecurityGameHop.realGameOracle secretKey) program =
      simulateQ SecurityCache.implementation (resolve secretKey program) := by
  have hash_query (query : Query) :
      simulateQ SecurityCache.implementation
          ((liftM (HashSpec.query query) : OracleComp HashSpec _).liftComp World) =
        (randomOracle (spec := HashSpec) query :
          StateT (QueryCache HashSpec) ProbComp _) := by
    rw [OracleComp.liftComp_query]
    change simulateQ SecurityCache.implementation
      (liftM (World.query (.inr query))) = _
    rw [simulateQ_spec_query]
    rfl
  have step (query : SecurityGameHop.GameWorld.Domain) :
      simulateQ SecurityCache.implementation (translate secretKey query) =
        SecurityGameHop.realGameOracle secretKey query := by
    cases query with
    | inl coin => rfl
    | inr query =>
        cases query with
        | inl slot => exact hash_query (SecurityDerivation.input secretKey slot)
        | inr query => exact hash_query query
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
      simp only [resolve, simulateQ_bind, simulateQ_spec_query, step] at ih ⊢
      exact bind_congr ih

/-- Both counted organizer interpretations run against the same lazy H cache
and have exactly the same output distribution, including the counter. -/
theorem organizer_observe_counted (sizes : Sizes)
    (encode : GroupedBalancedScheme67.Signature → Bytes sizes.signature)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (secretKey : SecretKey) (adversary : Adversary sizes)
    (publicCache : Cache) (rounds : Nat)
    (table : GroupedBalancedGraphPassive67.PointTable)
    (cache : QueryCache HashSpec) :
    (simulateQ (SecurityGameHop.realGameOracle secretKey)
      (SecurityBudget.counted
        (GroupedBalancedGameWorldBudget67.organizerProgram sizes
          encode decodeWitness decodeSignature adversary
          publicCache rounds table))).run' cache =
      SecurityGraphHidden.observe
        (GroupedBalancedGraphViewWorld67.counted
          (GroupedBalancedGraphViewWorld67.ofView table
            (GroupedBalancedGraphIndexJointOrganizerBound67.organizerView sizes
              encode decodeWitness decodeSignature secretKey adversary
              publicCache rounds
              (GroupedBalancedGraphMonitorSetup67.cache table)))) cache := by
  rw [simulate_real]
  rw [organizer_counted_resolve]
  rfl

#print axioms organizer_observe_counted

/-- The organizer's final verification branch is an ordinary public oracle
program followed by the interaction continuation. Its graph meter therefore
charges exactly the verifier program's public hash queries. -/
theorem gameView_ofHash {α β : Type}
    (table : GroupedBalancedGraphPassive67.PointTable)
    (cache : QueryCache GroupedBalancedGraphPassive67.PointSpec)
    (program : OracleComp HashSpec α)
    (next : α → GroupedBalancedGraphInteraction67.Interaction β) :
    GroupedBalancedGameWorld67.gameView table cache
      (GroupedBalancedGraphInteractionGame67.ofHash program next) =
      program.liftComp SecurityGameHop.GameWorld >>= fun value =>
        GroupedBalancedGameWorld67.gameView table cache (next value) := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query resume ih =>
      rw [GroupedBalancedGraphInteractionGame67.ofHash_query]
      simp only [GroupedBalancedGameWorld67.gameView,
        OracleComp.liftComp_bind]
      exact bind_congr ih

#print axioms gameView_ofHash

/-- One organizer signing action consumes precisely two graph-game queries:
the H6 randomizer and the H5 index. -/
theorem counted_gameView_sign {α : Type}
    (table : GroupedBalancedGraphPassive67.PointTable)
    (cache : QueryCache GroupedBalancedGraphPassive67.PointSpec)
    (message : Message)
    (next : GroupedBalancedScheme67.Signature →
      GroupedBalancedGraphInteraction67.Interaction α) :
    SecurityBudget.counted
      (GroupedBalancedGameWorld67.gameView table cache
        (.sign message next)) =
      (do
        let randomizer ← liftM (SecurityGameHop.GameWorld.query
          (.inr (.inl (.randomizer message))))
        let indexAnswer ← liftM (SecurityGameHop.GameWorld.query
          (.inr (.inr (SecurityRandomOracle.indexInput message randomizer))))
        let index : BitVec 160 := indexAnswer.extractLsb' 0 160
        let signature := GroupedBalancedGraphHonestSignView67.signatureFromAnswers
          cache randomizer index (table (.inr (.inl index)))
        let result ← SecurityBudget.counted
          (GroupedBalancedGameWorld67.gameView table cache (next signature))
        pure (result.1, result.2 + 2)) := by
  simp only [GroupedBalancedGameWorld67.gameView,
    SecurityBudget.counted_query_bind, SecurityBudget.charge]
  simp only [bind_assoc, pure_bind]

#print axioms counted_gameView_sign

def worldAnswers (hash : Hash) (coins : ∀ n, Fin (n + 1)) :
    QueryImpl World Id
  | .inl n => coins n
  | .inr input => hash input

def gameAnswers (hash : Hash) (coins : ∀ n, Fin (n + 1))
    (secretKey : SecretKey) : QueryImpl SecurityGameHop.GameWorld Id
  | .inl n => coins n
  | .inr (.inl slot) => hash (SecurityDerivation.input secretKey slot)
  | .inr (.inr input) => hash input

/-- Fixing the same answers for all coins and H inputs makes the translated
organizer and the graph-game program compute exactly the same value. -/
theorem eval_resolve {α : Type} (hash : Hash)
    (coins : ∀ n, Fin (n + 1)) (secretKey : SecretKey)
    (program : OracleComp SecurityGameHop.GameWorld α) :
    evalWithAnswerFn (worldAnswers hash coins)
      (resolve secretKey program) =
    evalWithAnswerFn (gameAnswers hash coins secretKey) program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [resolve, simulateQ_bind, evalWithAnswerFn_bind]
      cases query with
      | inl n => exact ih (coins n)
      | inr query =>
          cases query with
          | inl slot => exact ih (hash (SecurityDerivation.input secretKey slot))
          | inr input => exact ih (hash input)

#print axioms eval_resolve

theorem counted_bind {α β : Type}
    (program : OracleComp SecurityGameHop.GameWorld α)
    (next : α → OracleComp SecurityGameHop.GameWorld β) :
    SecurityBudget.counted (program >>= next) = (do
      let first ← SecurityBudget.counted program
      let second ← SecurityBudget.counted (next first.1)
      pure (second.1, second.2 + first.2)) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query continuation ih =>
      rw [bind_assoc, SecurityBudget.counted_query_bind,
        SecurityBudget.counted_query_bind]
      simp only [bind_assoc]
      apply bind_congr
      intro answer
      rw [ih answer]
      simp only [bind_assoc, pure_bind]
      apply bind_congr
      intro first
      apply bind_congr
      intro second
      congr 1
      simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

#print axioms counted_bind

theorem eval_counted_ofHash {α β : Type}
    (hash : Hash) (coins : ∀ n, Fin (n + 1))
    (secretKey : SecretKey)
    (table : GroupedBalancedGraphPassive67.PointTable)
    (cache : QueryCache GroupedBalancedGraphPassive67.PointSpec)
    (program : OracleComp HashSpec α)
    (next : α → GroupedBalancedGraphInteraction67.Interaction β) :
    evalWithAnswerFn (gameAnswers hash coins secretKey)
      (SecurityBudget.counted
        (GroupedBalancedGameWorld67.gameView table cache
          (GroupedBalancedGraphInteractionGame67.ofHash program next))) =
    let value := evalWithAnswerFn hash program
    let result := evalWithAnswerFn (gameAnswers hash coins secretKey)
      (SecurityBudget.counted
        (GroupedBalancedGameWorld67.gameView table cache (next value)))
    (result.1, result.2 + SecurityVerifyCost.calls hash program) := by
  rw [gameView_ofHash, counted_bind]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  have publicAgree : ∀ input,
      gameAnswers hash coins secretKey (.inr (.inr input)) = hash input :=
    fun _ => rfl
  rw [SecurityVerifyCost.counted_lift hash
    (gameAnswers hash coins secretKey) publicAgree program]

#print axioms eval_counted_ofHash

theorem eval_world_lift {α : Type} (hash : Hash)
    (coins : ∀ n, Fin (n + 1))
    (program : OracleComp HashSpec α) :
    evalWithAnswerFn (worldAnswers hash coins)
      (program.liftComp World) =
      evalWithAnswerFn hash program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      rw [OracleComp.liftComp_bind]
      simp only [evalWithAnswerFn_bind]
      exact ih (hash query)

#print axioms eval_world_lift

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityCounterCore67
