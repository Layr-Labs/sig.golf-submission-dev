import SigGolfCandidate.Hypertree.GroupedBalancedSecurityCounterCore67
import SigGolfCandidate.Hypertree.GroupedBalancedSecurityOfficialHybrid67
import SigGolfCandidate.Hypertree.GroupedBalancedSecurityFullSemantic67

/-! A fixed-answer pairing of the public graph game and the submitted
semantic interaction. The last checker step is isolated as a local premise. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityCounterPaired67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedSecurityCounterCore67
open GroupedBalancedSecurityJointInteraction67
open GroupedBalancedSecurityOfficialHybrid67
open GroupedBalancedSecurityFullSemantic67
open scoped Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

private abbrev submission := GroupedBalancedProgram67ByteSign.submission
private abbrev GraphResult :=
  GroupedBalancedGraphOrganizerView67.Result submission.sizes

private noncomputable def graphOutcome (hash : Hash) (coins : ∀ n, Fin (n + 1))
    (secretKey : SecretKey) (table : GroupedBalancedGraphPassive67.PointTable)
    (pk : PublicKey) (adversary : Adversary submission.sizes)
    (rounds : Nat) (state : adversary.State)
    (transcript : Transcript submission.sizes) : GraphResult × Nat :=
  evalWithAnswerFn (gameAnswers hash coins secretKey)
    (SecurityBudget.counted
      (GroupedBalancedGameWorld67.gameView table
        (GroupedBalancedGraphMonitorSetup67.cache table)
        (GroupedBalancedGraphOrganizerView67.ofInteract submission.sizes
          GroupedBalancedWire67.wire
          GroupedBalancedWire67.decode GroupedBalancedWire67.decode
          adversary pk rounds state transcript)))

private noncomputable def officialOutcome (hash : Hash) (coins : ∀ n, Fin (n + 1))
    (secretKey : SecretKey) (table : GroupedBalancedGraphPassive67.PointTable)
    (pk : PublicKey) (adversary : Adversary submission.sizes)
    (rounds : Nat) (state : adversary.State)
    (transcript : Transcript submission.sizes) : AttackResult :=
  evalWithAnswerFn (worldAnswers hash coins)
    (interactWith (fullInterface table) adversary secretKey pk
      rounds state transcript)

private noncomputable def graphCheck (hash : Hash) (coins : ∀ n, Fin (n + 1))
    (secretKey : SecretKey) (table : GroupedBalancedGraphPassive67.PointTable)
    (pk : PublicKey) (transcript : Transcript submission.sizes)
    (forgery : Forgery submission.sizes) : GraphResult × Nat :=
  evalWithAnswerFn (gameAnswers hash coins secretKey)
    (SecurityBudget.counted
      (GroupedBalancedGameWorld67.gameView table
        (GroupedBalancedGraphMonitorSetup67.cache table)
        (GroupedBalancedGraphOrganizerView67.ofCheck submission.sizes
          GroupedBalancedWire67.decode GroupedBalancedWire67.decode
          pk transcript forgery)))

theorem resolve_counted_hash {α : Type} (secretKey : SecretKey)
    (program : OracleComp HashSpec α) :
    GroupedBalancedGameWorld67.resolve secretKey
      (SecurityBudget.counted
        (program.liftComp SecurityGameHop.GameWorld)) =
      (countHash program).liftComp World := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [OracleComp.liftComp_bind]
      change GroupedBalancedGameWorld67.resolve secretKey
        (SecurityBudget.counted
          (liftM (SecurityGameHop.GameWorld.query (.inr (.inr input))) >>=
            fun answer => (next answer).liftComp SecurityGameHop.GameWorld)) = _
      rw [SecurityBudget.counted_query_bind, countHash_query_bind,
        OracleComp.liftComp_bind]
      simp only [resolve_bind, resolve_pure,
        GroupedBalancedGameWorld67.resolve_public,
        SecurityBudget.charge]
      apply bind_congr
      intro answer
      rw [ih answer]
      rw [OracleComp.liftComp_bind]
      rfl

#print axioms resolve_counted_hash

theorem resolve_counted_ofHash {α β : Type}
    (secretKey : SecretKey)
    (table : GroupedBalancedGraphPassive67.PointTable)
    (cache : QueryCache GroupedBalancedGraphPassive67.PointSpec)
    (program : OracleComp HashSpec α)
    (next : α → GroupedBalancedGraphInteraction67.Interaction β) :
    GroupedBalancedGameWorld67.resolve secretKey
      (SecurityBudget.counted
        (GroupedBalancedGameWorld67.gameView table cache
          (GroupedBalancedGraphInteractionGame67.ofHash program next))) =
      (do
        let first ← (countHash program).liftComp World
        let second ← GroupedBalancedGameWorld67.resolve secretKey
          (SecurityBudget.counted
            (GroupedBalancedGameWorld67.gameView table cache (next first.1)))
        pure (second.1, second.2 + first.2)) := by
  rw [gameView_ofHash, counted_bind]
  simp only [resolve_bind, resolve_pure, resolve_counted_hash]

#print axioms resolve_counted_ofHash

def CheckComparison : Prop :=
  ∀ (hash : Hash) (coins : ∀ n, Fin (n + 1))
    (secretKey : SecretKey) (table : GroupedBalancedGraphPassive67.PointTable)
    (pk : PublicKey) (graphTranscript officialTranscript : Transcript submission.sizes)
    (forgery : Forgery submission.sizes),
    graphTranscript.signed = officialTranscript.signed →
    (graphCheck hash coins secretKey table pk graphTranscript forgery).1.won =
      (evalWithAnswerFn (worldAnswers hash coins)
        (((fullInterface table).check pk officialTranscript forgery).liftComp World)).won ∧
    (graphCheck hash coins secretKey table pk graphTranscript forgery).2 +
      officialTranscript.hashCalls ≤
      (evalWithAnswerFn (worldAnswers hash coins)
        (((fullInterface table).check pk officialTranscript forgery).liftComp World)).hashCalls

theorem check_comparison : CheckComparison := by
  intro hash coins secretKey table pk graphTranscript officialTranscript
    forgery signed
  cases forgery with
  | witness message wire =>
      simp only [graphCheck,
        GroupedBalancedGraphOrganizerView67.ofCheck,
        eval_counted_ofHash,
        GroupedBalancedGameWorld67.gameView,
        SecurityBudget.counted_pure,
        evalWithAnswerFn_pure,
        fullInterface,
        eval_world_lift,
        semanticCheck,
        evalWithAnswerFn_bind,
        eval_countHash]
      simp only [GroupedBalancedSecurityCheckConditional67.program,
        Transcript.freshMessage, signed, Nat.zero_add]
      simp [Nat.add_comm]
  | signature message wire =>
      simp only [graphCheck,
        GroupedBalancedGraphOrganizerView67.ofCheck,
        eval_counted_ofHash,
        GroupedBalancedGameWorld67.gameView,
        SecurityBudget.counted_pure,
        evalWithAnswerFn_pure,
        fullInterface,
        eval_world_lift,
        semanticCheck,
        evalWithAnswerFn_bind,
        eval_countHash]
      simp only [GroupedBalancedSecurityCheckConditional67.program,
        Transcript.freshSignature, signed, Nat.zero_add]
      simp [Nat.add_comm]

theorem interact_le (checkComparison : CheckComparison)
    (hash : Hash) (coins : ∀ n, Fin (n + 1))
    (secretKey : SecretKey) (table : GroupedBalancedGraphPassive67.PointTable)
    (pk : PublicKey) (adversary : Adversary submission.sizes)
    (rounds : Nat) (state : adversary.State)
    (graphTranscript officialTranscript : Transcript submission.sizes)
    (signed : graphTranscript.signed = officialTranscript.signed)
    (requests : graphTranscript.signingRequests = officialTranscript.signingRequests) :
    (graphOutcome hash coins secretKey table pk adversary rounds state
      graphTranscript).1.won =
      (officialOutcome hash coins secretKey table pk adversary rounds state
        officialTranscript).won ∧
    (graphOutcome hash coins secretKey table pk adversary rounds state
      graphTranscript).2 + officialTranscript.hashCalls ≤
      (officialOutcome hash coins secretKey table pk adversary rounds state
        officialTranscript).hashCalls := by
  induction rounds generalizing state graphTranscript officialTranscript with
  | zero =>
      simp [graphOutcome, officialOutcome,
        GroupedBalancedGraphOrganizerView67.ofInteract,
        interactWith, GroupedBalancedGameWorld67.gameView,
        SecurityBudget.counted]
  | succ rounds ih =>
      cases action : adversary.step state with
      | submit candidate =>
          simpa only [graphOutcome, officialOutcome, graphCheck,
            GroupedBalancedGraphOrganizerView67.ofInteract,
            interactWith, action] using
            checkComparison hash coins secretKey table pk
              graphTranscript officialTranscript candidate signed
      | hash input resume =>
          have next := ih (resume (hash input))
            { graphTranscript with hashCalls := graphTranscript.hashCalls + 1 }
            { officialTranscript with hashCalls := officialTranscript.hashCalls + 1 }
            (by simp [signed]) (by simp [requests])
          rcases next with ⟨win,cost⟩
          have graphQuery : evalWithAnswerFn
              (gameAnswers hash coins secretKey)
              (liftM (SecurityGameHop.GameWorld.query (.inr (.inr input)))) =
              hash input := rfl
          have worldQuery : evalWithAnswerFn
              (worldAnswers hash coins)
              (liftM (HashSpec.query input) : OracleComp World _) =
              hash input := rfl
          simp only [graphOutcome, officialOutcome,
            GroupedBalancedGraphOrganizerView67.ofInteract,
            interactWith, action,
            GroupedBalancedGameWorld67.gameView,
            SecurityBudget.counted_query_bind, SecurityBudget.charge,
            evalWithAnswerFn_bind, evalWithAnswerFn_pure,
            graphQuery, worldQuery] at win cost ⊢
          exact ⟨win, by omega⟩
      | sign request resume =>
          by_cases limit : graphTranscript.signingRequests < LIFETIME
          · have officialLimit : officialTranscript.signingRequests < LIFETIME := by
              simpa only [← requests] using limit
            let randomizer := hash
              (SecurityRandomOracle.randomizerInput secretKey request.message)
            let indexAnswer := hash
              (SecurityRandomOracle.indexInput request.message randomizer)
            let index : BitVec 160 := indexAnswer.extractLsb' 0 160
            let signature :=
              GroupedBalancedGraphHonestSignView67.signatureFromAnswers
                (GroupedBalancedGraphMonitorSetup67.cache table)
                randomizer index (table (.inr (.inl index)))
            let wire := GroupedBalancedWire67.wire signature
            let graphNext : Transcript submission.sizes :=
              { graphTranscript with
                signed := (request.message, wire) :: graphTranscript.signed
                signingRequests := graphTranscript.signingRequests + 1 }
            let officialNext := recordView officialTranscript request.message
              (some wire, 122548)
            have signedNext : graphNext.signed = officialNext.signed := by
              simp only [graphNext, officialNext, recordView, signed]
            have requestsNext : graphNext.signingRequests =
                officialNext.signingRequests := by
              simp only [graphNext, officialNext, recordView, requests]
            have next := ih (resume (some wire)) graphNext officialNext
              signedNext requestsNext
            have semanticSign :
                evalWithAnswerFn (worldAnswers hash coins)
                  (((fullInterface table).sign secretKey request).liftComp World) =
                (some wire, 122548) := by
              change evalWithAnswerFn (worldAnswers hash coins)
                ((GroupedBalancedSecurityJointContext67.semanticSign
                  secretKey table request).liftComp World) = _
              rw [eval_world_lift]
              simp only [GroupedBalancedSecurityJointContext67.semanticSign,
                evalWithAnswerFn_bind, evalWithAnswerFn_pure]
              rfl
            have graphSign :
                graphOutcome hash coins secretKey table pk adversary
                  (rounds + 1) state graphTranscript =
                let future := graphOutcome hash coins secretKey table pk
                  adversary rounds (resume (some wire)) graphNext
                (future.1, future.2 + 2) := by
              simp only [graphOutcome,
                GroupedBalancedGraphOrganizerView67.ofInteract,
                action, if_pos limit, counted_gameView_sign,
                evalWithAnswerFn_bind, evalWithAnswerFn_pure]
              rfl
            have officialSign :
                officialOutcome hash coins secretKey table pk adversary
                  (rounds + 1) state officialTranscript =
                officialOutcome hash coins secretKey table pk adversary
                  rounds (resume (some wire)) officialNext := by
              simp only [officialOutcome, interactWith, action,
                if_pos officialLimit, evalWithAnswerFn_bind,
                semanticSign]
              rfl
            rcases next with ⟨win, cost⟩
            rw [graphSign, officialSign]
            constructor
            · exact win
            · dsimp only
              simp only [officialNext, recordView] at cost ⊢
              omega
          · have officialLimit : ¬ officialTranscript.signingRequests < LIFETIME := by
              simpa only [← requests] using limit
            simp [graphOutcome, officialOutcome,
              GroupedBalancedGraphOrganizerView67.ofInteract,
              interactWith, action, limit, officialLimit,
              GroupedBalancedGameWorld67.gameView,
              SecurityBudget.counted]
      | sample n resume =>
          have next := ih (resume (coins n)) graphTranscript
            officialTranscript signed requests
          have graphCoin : evalWithAnswerFn
              (gameAnswers hash coins secretKey)
              (liftM (SecurityGameHop.GameWorld.query (.inl n))) =
              coins n := rfl
          have worldCoin : evalWithAnswerFn
              (worldAnswers hash coins)
              (liftM (unifSpec.query n) : OracleComp World _) =
              coins n := rfl
          simpa only [graphOutcome, officialOutcome,
            GroupedBalancedGraphOrganizerView67.ofInteract,
            interactWith, action,
            GroupedBalancedGameWorld67.gameView,
            SecurityBudget.counted_query_bind, SecurityBudget.charge,
            evalWithAnswerFn_bind, evalWithAnswerFn_pure,
            graphCoin, worldCoin, Nat.add_zero] using next
      | step next =>
          simpa only [graphOutcome, officialOutcome,
            GroupedBalancedGraphOrganizerView67.ofInteract,
            interactWith, action] using
            ih next graphTranscript officialTranscript signed requests

#print axioms check_comparison
#print axioms interact_le

/-- For each fixed complete sequence of oracle answers, the organizer's
winning bit agrees with the fully semantic game and its counted hash calls
fit within the official charge, including key generation. -/
theorem game_le_fixed (hash : Hash) (coins : ∀ n, Fin (n + 1))
    (secretKey : SecretKey) (table : GroupedBalancedGraphPassive67.PointTable)
    (adversary : Adversary submission.sizes) (rounds : Nat) :
    let graph := evalWithAnswerFn (gameAnswers hash coins secretKey)
      (SecurityBudget.counted
        (GroupedBalancedGameWorldBudget67.organizerProgram
          submission.sizes GroupedBalancedWire67.wire
          GroupedBalancedWire67.decode GroupedBalancedWire67.decode
          adversary (0 : Cache) rounds table))
    let official := evalWithAnswerFn (worldAnswers hash coins)
      (gameWith (fullInterface table) adversary rounds secretKey)
    graph.1.won = official.won ∧ graph.2 ≤ official.hashCalls := by
  let pk := GroupedBalancedGraphMonitorSetupBound67.rootPublic table
  have paired := interact_le check_comparison hash coins secretKey table pk
    adversary rounds (adversary.initial pk (0 : Cache))
    {} {hashCalls := 3983} rfl rfl
  unfold graphOutcome officialOutcome at paired
  simp only [pk, fullInterface, tableInterface] at paired
  simp only [GroupedBalancedGameWorldBudget67.organizerProgram,
    GroupedBalancedGraphMonitorSetupBound67.rootFrom_cache,
    gameWith, fullInterface, tableInterface,
    OracleComp.liftComp_pure, pure_bind]
  exact ⟨paired.1, by omega⟩

#print axioms game_le_fixed

abbrev JointResult := (GraphResult × Nat) × AttackResult

private def pairCheck (pk : PublicKey)
    (graphTranscript officialTranscript : Transcript submission.sizes) :
    Forgery submission.sizes → OracleComp World JointResult
  | .witness message wire => do
      let result ← (countHash
        (GroupedBalancedSecurityCheckConditional67.program pk message wire)).liftComp World
      pure ((⟨result.1 && graphTranscript.freshMessage message,
        some (message, GroupedBalancedWire67.decode wire), graphTranscript⟩,
        result.2),
        ⟨result.1 && officialTranscript.freshMessage message,
          officialTranscript.hashCalls + result.2⟩)
  | .signature message wire => do
      let result ← (countHash
        (GroupedBalancedSecurityCheckConditional67.program pk message wire)).liftComp World
      pure ((⟨result.1 && graphTranscript.freshSignature message wire,
        some (message, GroupedBalancedWire67.decode wire), graphTranscript⟩,
        result.2),
        ⟨result.1 && officialTranscript.freshSignature message wire,
          officialTranscript.hashCalls + result.2⟩)

noncomputable def pairInteract (table : GroupedBalancedGraphPassive67.PointTable)
    (secretKey : SecretKey) (pk : PublicKey)
    (adversary : Adversary submission.sizes) :
    Nat → adversary.State → Transcript submission.sizes →
      Transcript submission.sizes → OracleComp World JointResult
  | 0, _, graphTranscript, officialTranscript =>
      pure ((⟨false, none, graphTranscript⟩, 0),
        ⟨false, officialTranscript.hashCalls⟩)
  | rounds + 1, state, graphTranscript, officialTranscript =>
      match adversary.step state with
      | .submit forgery => pairCheck pk graphTranscript officialTranscript forgery
      | .hash input resume => do
          let answer ← (liftM (HashSpec.query input) : OracleComp World _)
          let result ← pairInteract table secretKey pk adversary rounds
            (resume answer)
            {graphTranscript with hashCalls := graphTranscript.hashCalls + 1}
            {officialTranscript with hashCalls := officialTranscript.hashCalls + 1}
          pure ((result.1.1, result.1.2 + 1), result.2)
      | .sign request resume =>
          if graphTranscript.signingRequests < LIFETIME then do
            let randomizer ← (liftM (HashSpec.query
              (SecurityRandomOracle.randomizerInput secretKey request.message)) :
              OracleComp World _)
            let indexAnswer ← (liftM (HashSpec.query
              (SecurityRandomOracle.indexInput request.message randomizer)) :
              OracleComp World _)
            let index : BitVec 160 := indexAnswer.extractLsb' 0 160
            let signature :=
              GroupedBalancedGraphHonestSignView67.signatureFromAnswers
                (GroupedBalancedGraphMonitorSetup67.cache table)
                randomizer index (table (.inr (.inl index)))
            let wire := GroupedBalancedWire67.wire signature
            let graphNext : Transcript submission.sizes :=
              { graphTranscript with
                signed := (request.message, wire) :: graphTranscript.signed
                signingRequests := graphTranscript.signingRequests + 1 }
            let officialNext := recordView officialTranscript request.message
              (some wire, 122548)
            let result ← pairInteract table secretKey pk adversary rounds
              (resume (some wire)) graphNext officialNext
            pure ((result.1.1, result.1.2 + 2), result.2)
          else pure ((⟨false, none, graphTranscript⟩, 0),
            ⟨false, officialTranscript.hashCalls⟩)
      | .sample n resume => do
          let answer ← liftM (unifSpec.query n)
          pairInteract table secretKey pk adversary rounds
            (resume answer) graphTranscript officialTranscript
      | .step next => pairInteract table secretKey pk adversary rounds
          next graphTranscript officialTranscript

theorem pair_official (table : GroupedBalancedGraphPassive67.PointTable)
    (secretKey : SecretKey) (pk : PublicKey)
    (adversary : Adversary submission.sizes) (rounds : Nat)
    (state : adversary.State)
    (graphTranscript officialTranscript : Transcript submission.sizes)
    (requests : graphTranscript.signingRequests =
      officialTranscript.signingRequests) :
    Prod.snd <$> pairInteract table secretKey pk adversary rounds
      state graphTranscript officialTranscript =
    interactWith (fullInterface table) adversary secretKey pk rounds
      state officialTranscript := by
  induction rounds generalizing state graphTranscript officialTranscript with
  | zero => rfl
  | succ rounds ih =>
      cases action : adversary.step state with
      | submit candidate =>
          cases candidate <;>
            simp [pairInteract, pairCheck, interactWith, action,
              fullInterface, semanticCheck]
      | hash input resume =>
          simp only [pairInteract, interactWith, action, map_bind]
          apply bind_congr
          intro answer
          rw [← ih (resume answer)
            {graphTranscript with hashCalls := graphTranscript.hashCalls + 1}
            {officialTranscript with hashCalls := officialTranscript.hashCalls + 1}
            (by simp [requests])]
          simp
      | sign request resume =>
          by_cases limit : graphTranscript.signingRequests < LIFETIME
          · have officialLimit : officialTranscript.signingRequests < LIFETIME := by
              simpa only [← requests] using limit
            simp only [pairInteract, interactWith, action,
              if_pos limit, if_pos officialLimit,
              fullInterface, tableInterface,
              GroupedBalancedSecurityJointContext67.semanticSign,
              map_bind, map_pure,
              OracleComp.liftComp_bind, OracleComp.liftComp_pure,
              pure_bind, bind_assoc]
            apply bind_congr
            intro randomizer
            apply bind_congr
            intro indexAnswer
            let index : BitVec 160 := indexAnswer.extractLsb' 0 160
            let wire := GroupedBalancedWire67.wire
              (GroupedBalancedGraphHonestSignView67.signatureFromAnswers
                (GroupedBalancedGraphMonitorSetup67.cache table)
                randomizer index (table (.inr (.inl index))))
            let graphNext : Transcript submission.sizes :=
              { graphTranscript with
                signed := (request.message, wire) :: graphTranscript.signed
                signingRequests := graphTranscript.signingRequests + 1 }
            let officialNext := recordView officialTranscript request.message
              (some wire, 122548)
            have nextRequests : graphNext.signingRequests =
                officialNext.signingRequests := by
              simp only [graphNext, officialNext, recordView, requests]
            simpa only [map_eq_pure_bind, graphNext, officialNext,
              fullInterface, tableInterface,
              GroupedBalancedSecurityJointContext67.semanticSign] using
              ih (resume (some wire)) graphNext officialNext nextRequests
          · have officialLimit : ¬ officialTranscript.signingRequests < LIFETIME := by
              simpa only [← requests] using limit
            simp [pairInteract, interactWith, action, limit, officialLimit]
      | sample n resume =>
          simp only [pairInteract, interactWith, action, map_bind]
          apply bind_congr
          intro answer
          exact ih (resume answer) graphTranscript officialTranscript requests
      | step next =>
          simpa only [pairInteract, interactWith, action] using
            ih next graphTranscript officialTranscript requests

#print axioms pair_official

theorem pair_graph (table : GroupedBalancedGraphPassive67.PointTable)
    (secretKey : SecretKey) (pk : PublicKey)
    (adversary : Adversary submission.sizes) (rounds : Nat)
    (state : adversary.State)
    (graphTranscript officialTranscript : Transcript submission.sizes) :
    Prod.fst <$> pairInteract table secretKey pk adversary rounds
      state graphTranscript officialTranscript =
    GroupedBalancedGameWorld67.resolve secretKey
      (SecurityBudget.counted
        (GroupedBalancedGameWorld67.gameView table
          (GroupedBalancedGraphMonitorSetup67.cache table)
          (GroupedBalancedGraphOrganizerView67.ofInteract submission.sizes
            GroupedBalancedWire67.wire
            GroupedBalancedWire67.decode GroupedBalancedWire67.decode
            adversary pk rounds state graphTranscript))) := by
  induction rounds generalizing state graphTranscript officialTranscript with
  | zero => rfl
  | succ rounds ih =>
      cases action : adversary.step state with
      | submit candidate =>
          cases candidate with
          | witness message wire =>
              simp only [pairInteract, pairCheck,
                GroupedBalancedGraphOrganizerView67.ofInteract, action,
                GroupedBalancedGraphOrganizerView67.ofCheck,
                resolve_counted_ofHash,
                GroupedBalancedGameWorld67.gameView,
                SecurityBudget.counted_pure, resolve_pure,
                map_bind, map_pure,
                GroupedBalancedSecurityCheckConditional67.program]
              simp only [pure_bind, Nat.zero_add]
          | signature message wire =>
              simp only [pairInteract, pairCheck,
                GroupedBalancedGraphOrganizerView67.ofInteract, action,
                GroupedBalancedGraphOrganizerView67.ofCheck,
                resolve_counted_ofHash,
                GroupedBalancedGameWorld67.gameView,
                SecurityBudget.counted_pure, resolve_pure,
                map_bind, map_pure,
                GroupedBalancedSecurityCheckConditional67.program]
              simp only [pure_bind, Nat.zero_add]
      | hash input resume =>
          simp only [pairInteract,
            GroupedBalancedGraphOrganizerView67.ofInteract, action,
            GroupedBalancedGameWorld67.gameView,
            SecurityBudget.counted_query_bind, SecurityBudget.charge,
            resolve_bind, resolve_pure,
            GroupedBalancedGameWorld67.resolve_public,
            map_bind]
          apply bind_congr
          intro answer
          have next := ih (resume answer)
            {graphTranscript with hashCalls := graphTranscript.hashCalls + 1}
            {officialTranscript with hashCalls := officialTranscript.hashCalls + 1}
          calc
            _ = (do
              let v ← Prod.fst <$> pairInteract table secretKey pk adversary
                rounds (resume answer)
                {graphTranscript with hashCalls := graphTranscript.hashCalls + 1}
                {officialTranscript with hashCalls := officialTranscript.hashCalls + 1}
              pure (v.1, v.2 + 1)) := by
                simp only [map_eq_pure_bind, bind_assoc, pure_bind]
            _ = _ := congrArg (fun m : OracleComp World (GraphResult × Nat) =>
              do let a ← m; pure (a.1, a.2 + 1)) next
      | sign request resume =>
          by_cases limit : graphTranscript.signingRequests < LIFETIME
          · simp only [pairInteract,
              GroupedBalancedGraphOrganizerView67.ofInteract, action,
              if_pos limit, counted_gameView_sign,
              resolve_bind, resolve_pure,
              GroupedBalancedGameWorld67.resolve_randomizer,
              GroupedBalancedGameWorld67.resolve_public, map_bind]
            apply bind_congr
            intro randomizer
            apply bind_congr
            intro indexAnswer
            let index : BitVec 160 := indexAnswer.extractLsb' 0 160
            let signature :=
              GroupedBalancedGraphHonestSignView67.signatureFromAnswers
                (GroupedBalancedGraphMonitorSetup67.cache table)
                randomizer index (table (.inr (.inl index)))
            let wire := GroupedBalancedWire67.wire signature
            let graphNext : Transcript submission.sizes :=
              { graphTranscript with
                signed := (request.message, wire) :: graphTranscript.signed
                signingRequests := graphTranscript.signingRequests + 1 }
            let officialNext := recordView officialTranscript request.message
              (some wire, 122548)
            have next := ih (resume (some wire)) graphNext officialNext
            calc
              _ = (do
                let v ← Prod.fst <$> pairInteract table secretKey pk adversary
                  rounds (resume (some wire)) graphNext officialNext
                pure (v.1, v.2 + 2)) := by
                  simp only [wire, signature, index, graphNext, officialNext,
                    map_eq_pure_bind, bind_assoc, pure_bind]
              _ = _ := congrArg (fun m : OracleComp World (GraphResult × Nat) =>
                do let a ← m; pure (a.1, a.2 + 2)) next
          · simp [pairInteract,
              GroupedBalancedGraphOrganizerView67.ofInteract, action,
              limit, GroupedBalancedGameWorld67.gameView,
              SecurityBudget.counted]
      | sample n resume =>
          simp only [pairInteract,
            GroupedBalancedGraphOrganizerView67.ofInteract, action,
            GroupedBalancedGameWorld67.gameView,
            SecurityBudget.counted_query_bind, SecurityBudget.charge,
            resolve_bind, resolve_pure,
            GroupedBalancedGameWorld67.resolve_coin,
            map_bind, Nat.add_zero]
          apply bind_congr
          intro answer
          simpa using ih (resume answer) graphTranscript officialTranscript
      | step next =>
          simpa only [pairInteract,
            GroupedBalancedGraphOrganizerView67.ofInteract, action] using
            ih next graphTranscript officialTranscript

#print axioms pair_graph

/-- The paired World execution preserves the organizer win bit and charges
every counted graph query within the official semantic hash budget. -/
theorem pair_le_fixed (hash : Hash) (coins : ∀ n, Fin (n + 1))
    (secretKey : SecretKey)
    (table : GroupedBalancedGraphPassive67.PointTable) (pk : PublicKey)
    (adversary : Adversary submission.sizes) (rounds : Nat)
    (state : adversary.State)
    (graphTranscript officialTranscript : Transcript submission.sizes)
    (signed : graphTranscript.signed = officialTranscript.signed)
    (requests : graphTranscript.signingRequests =
      officialTranscript.signingRequests) :
    let result := evalWithAnswerFn (worldAnswers hash coins)
      (pairInteract table secretKey pk adversary rounds state
        graphTranscript officialTranscript)
    result.1.1.won = result.2.won ∧
      result.1.2 + officialTranscript.hashCalls ≤ result.2.hashCalls := by
  have graph := congrArg (evalWithAnswerFn (worldAnswers hash coins))
    (pair_graph table secretKey pk adversary rounds state
      graphTranscript officialTranscript)
  have official := congrArg (evalWithAnswerFn (worldAnswers hash coins))
    (pair_official table secretKey pk adversary rounds state
      graphTranscript officialTranscript requests)
  simp only [evalWithAnswerFn_map] at graph official
  have bound := interact_le check_comparison hash coins secretKey table pk
    adversary rounds state graphTranscript officialTranscript signed requests
  unfold graphOutcome officialOutcome at bound
  rw [← eval_resolve] at bound
  rw [← graph, ← official] at bound
  exact bound

#print axioms pair_le_fixed

/-- The same win and cost relation holds for every possible sequence of coin
and hash answers, including repeated coin draws with different answers. -/
theorem pair_le_support
    (table : GroupedBalancedGraphPassive67.PointTable)
    (secretKey : SecretKey) (pk : PublicKey)
    (adversary : Adversary submission.sizes) (rounds : Nat)
    (state : adversary.State)
    (graphTranscript officialTranscript : Transcript submission.sizes)
    (result : JointResult)
    (signed : graphTranscript.signed = officialTranscript.signed)
    (requests : graphTranscript.signingRequests =
      officialTranscript.signingRequests)
    (member : result ∈ support
      (pairInteract table secretKey pk adversary rounds state
        graphTranscript officialTranscript)) :
    result.1.1.won = result.2.won ∧
      result.1.2 + officialTranscript.hashCalls ≤ result.2.hashCalls := by
  induction rounds generalizing state graphTranscript officialTranscript result with
  | zero =>
      simp only [pairInteract, mem_support_pure_iff] at member
      subst result
      simp
  | succ rounds ih =>
      cases action : adversary.step state with
      | submit candidate =>
          cases candidate with
          | witness message wire =>
              simp only [pairInteract, action, pairCheck,
                mem_support_bind_iff, mem_support_pure_iff] at member
              obtain ⟨check, _, eq⟩ := member
              subst result
              constructor
              · simp only [Transcript.freshMessage, signed]
              · change check.2 + officialTranscript.hashCalls ≤
                  officialTranscript.hashCalls + check.2
                omega
          | signature message wire =>
              simp only [pairInteract, action, pairCheck,
                mem_support_bind_iff, mem_support_pure_iff] at member
              obtain ⟨check, _, eq⟩ := member
              subst result
              constructor
              · simp only [Transcript.freshSignature, signed]
              · change check.2 + officialTranscript.hashCalls ≤
                  officialTranscript.hashCalls + check.2
                omega
      | hash input resume =>
          simp only [pairInteract, action,
            mem_support_bind_iff, mem_support_pure_iff] at member
          obtain ⟨answer, _, future, futureMember, eq⟩ := member
          subst result
          have next := ih (resume answer)
            {graphTranscript with hashCalls := graphTranscript.hashCalls + 1}
            {officialTranscript with hashCalls := officialTranscript.hashCalls + 1}
            future (by simpa only [signed]) (by simpa only [requests])
            futureMember
          constructor
          · exact next.1
          · have cost : future.1.2 + (officialTranscript.hashCalls + 1) ≤
                future.2.hashCalls := by simpa using next.2
            change future.1.2 + 1 + officialTranscript.hashCalls ≤
              future.2.hashCalls
            omega
      | sign request resume =>
          by_cases limit : graphTranscript.signingRequests < LIFETIME
          · simp only [pairInteract, action, if_pos limit,
              mem_support_bind_iff, mem_support_pure_iff] at member
            obtain ⟨randomizer, _, indexAnswer, _, future,
              futureMember, eq⟩ := member
            subst result
            let index : BitVec 160 := indexAnswer.extractLsb' 0 160
            let signature :=
              GroupedBalancedGraphHonestSignView67.signatureFromAnswers
                (GroupedBalancedGraphMonitorSetup67.cache table)
                randomizer index (table (.inr (.inl index)))
            let wire := GroupedBalancedWire67.wire signature
            let graphNext : Transcript submission.sizes :=
              { graphTranscript with
                signed := (request.message, wire) :: graphTranscript.signed
                signingRequests := graphTranscript.signingRequests + 1 }
            let officialNext := recordView officialTranscript request.message
              (some wire, 122548)
            have signedNext : graphNext.signed = officialNext.signed := by
              simp only [graphNext, officialNext, recordView, signed]
            have requestsNext : graphNext.signingRequests =
                officialNext.signingRequests := by
              simp only [graphNext, officialNext, recordView, requests]
            have next := ih (resume (some wire)) graphNext officialNext
              future signedNext requestsNext
              (by simpa only [wire, signature, index, graphNext, officialNext]
                using futureMember)
            constructor
            · exact next.1
            · have cost : future.1.2 +
                  (officialTranscript.hashCalls + 122548) ≤
                  future.2.hashCalls := by
                    simpa only [officialNext, recordView] using next.2
              change future.1.2 + 2 + officialTranscript.hashCalls ≤
                future.2.hashCalls
              omega
          · simp only [pairInteract, action, if_neg limit,
              mem_support_pure_iff] at member
            subst result
            simp
      | sample n resume =>
          simp only [pairInteract, action, mem_support_bind_iff] at member
          obtain ⟨answer, _, futureMember⟩ := member
          exact ih (resume answer) graphTranscript officialTranscript
            result signed requests futureMember
      | step next =>
          simp only [pairInteract, action] at member
          exact ih next graphTranscript officialTranscript result
            signed requests member

#print axioms pair_le_support

theorem pair_le_observed {σ : Type}
    (implementation : QueryImpl World (StateT σ ProbComp))
    (cache : σ)
    (table : GroupedBalancedGraphPassive67.PointTable)
    (secretKey : SecretKey) (pk : PublicKey)
    (adversary : Adversary submission.sizes) (rounds : Nat)
    (state : adversary.State)
    (graphTranscript officialTranscript : Transcript submission.sizes)
    (result : JointResult)
    (signed : graphTranscript.signed = officialTranscript.signed)
    (requests : graphTranscript.signingRequests =
      officialTranscript.signingRequests)
    (member : result ∈ support
      ((simulateQ implementation
        (pairInteract table secretKey pk adversary rounds state
          graphTranscript officialTranscript)).run' cache)) :
    result.1.1.won = result.2.won ∧
      result.1.2 + officialTranscript.hashCalls ≤ result.2.hashCalls := by
  exact pair_le_support table secretKey pk adversary rounds state
    graphTranscript officialTranscript result signed requests
    (OracleComp.support_simulateQ_run'_subset implementation _ cache member)

#print axioms pair_le_observed

/-- One shared adaptive execution from the exact organizer and official
initial transcripts. -/
noncomputable def pairGame
    (table : GroupedBalancedGraphPassive67.PointTable)
    (secretKey : SecretKey)
    (adversary : Adversary submission.sizes) (rounds : Nat) :
    OracleComp World JointResult :=
  let pk := GroupedBalancedGraphMonitorSetupBound67.rootPublic table
  pairInteract table secretKey pk adversary rounds
    (adversary.initial pk (0 : Cache)) {} {hashCalls := 3983}

theorem pairGame_official
    (table : GroupedBalancedGraphPassive67.PointTable)
    (secretKey : SecretKey)
    (adversary : Adversary submission.sizes) (rounds : Nat) :
    Prod.snd <$> pairGame table secretKey adversary rounds =
      gameWith (fullInterface table) adversary rounds secretKey := by
  unfold pairGame
  rw [pair_official]
  simp only [gameWith, fullInterface, tableInterface,
    OracleComp.liftComp_pure, pure_bind]
  rfl

theorem pairGame_graph
    (table : GroupedBalancedGraphPassive67.PointTable)
    (secretKey : SecretKey)
    (adversary : Adversary submission.sizes) (rounds : Nat) :
    Prod.fst <$> pairGame table secretKey adversary rounds =
      GroupedBalancedGameWorld67.resolve secretKey
        (SecurityBudget.counted
          (GroupedBalancedGameWorldBudget67.organizerProgram
            submission.sizes GroupedBalancedWire67.wire
            GroupedBalancedWire67.decode GroupedBalancedWire67.decode
            adversary (0 : Cache) rounds table)) := by
  unfold pairGame
  rw [pair_graph]
  simp only [GroupedBalancedGameWorldBudget67.organizerProgram,
    GroupedBalancedGraphMonitorSetupBound67.rootFrom_cache]

theorem pairGame_le_observed {σ : Type}
    (implementation : QueryImpl World (StateT σ ProbComp))
    (cache : σ)
    (table : GroupedBalancedGraphPassive67.PointTable)
    (secretKey : SecretKey)
    (adversary : Adversary submission.sizes) (rounds : Nat)
    (result : JointResult)
    (member : result ∈ support
      ((simulateQ implementation
        (pairGame table secretKey adversary rounds)).run' cache)) :
    result.1.1.won = result.2.won ∧
      result.1.2 ≤ result.2.hashCalls := by
  let pk := GroupedBalancedGraphMonitorSetupBound67.rootPublic table
  have bound := pair_le_observed implementation cache table secretKey
    pk adversary rounds (adversary.initial pk (0 : Cache))
    {} {hashCalls := 3983} result rfl rfl
    (by simpa only [pairGame, pk] using member)
  exact ⟨bound.1, by omega⟩

#print axioms pairGame_official
#print axioms pairGame_graph
#print axioms pairGame_le_observed

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityCounterPaired67
