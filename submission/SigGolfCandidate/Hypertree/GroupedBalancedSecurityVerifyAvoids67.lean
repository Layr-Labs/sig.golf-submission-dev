import SigGolfCandidate.Hypertree.GroupedBalancedSecurityFullSemantic67
import SigGolfCandidate.Hypertree.SecurityVerifyTrace
import SigGolfCandidate.Hypertree.SecuritySecretKeyStoppedTrace
import SigGolfCandidate.Hypertree.GroupedBalancedSecurityCounterPaired67

/-! Structural H1-source exclusion for the counted reference checker. The
counter transformer preserves the exact verifier query sequence. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityVerifyAvoids67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedSecuritySourceHybrid67
open GroupedBalancedSecurityVerifySourceFree67
open GroupedBalancedSecurityFullSemantic67
open GroupedBalancedSecurityOfficialHybrid67
open GroupedBalancedSecurityCounterPaired67
open GroupedBalancedSecurityJointInteraction67
open scoped Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def Avoids (secretKey : SecretKey) {α : Type}
    (program : OracleComp HashSpec α) : Prop :=
  OracleComp.construct (fun _ => True)
    (fun query _ after =>
      ¬ SourceHit secretKey query ∧ ∀ answer, after answer) program

@[simp] theorem avoids_pure {α : Type} (secretKey : SecretKey)
    (value : α) :
    Avoids secretKey (pure value : OracleComp HashSpec α) := trivial

theorem avoids_query_bind {α : Type} (secretKey : SecretKey)
    (query : Query) (next : BitVec 256 → OracleComp HashSpec α) :
    Avoids secretKey (liftM (HashSpec.query query) >>= next) ↔
      ¬ SourceHit secretKey query ∧ ∀ answer, Avoids secretKey (next answer) :=
  Iff.rfl

theorem avoids_bind {α β : Type} (secretKey : SecretKey)
    (first : OracleComp HashSpec α)
    (next : α → OracleComp HashSpec β)
    (firstAvoids : Avoids secretKey first)
    (nextAvoids : ∀ value, Avoids secretKey (next value)) :
    Avoids secretKey (first >>= next) := by
  induction first using OracleComp.inductionOn with
  | pure value => exact nextAvoids value
  | query_bind query continuation ih =>
      have head := (avoids_query_bind secretKey query continuation).mp firstAvoids
      apply (avoids_query_bind secretKey query
        (fun answer => continuation answer >>= next)).mpr
      exact ⟨head.1,fun answer => ih answer (head.2 answer)⟩

theorem avoids_map {α β : Type} (secretKey : SecretKey)
    (program : OracleComp HashSpec α) (f : α → β)
    (avoids : Avoids secretKey program) :
    Avoids secretKey (f <$> program) := by
  rw [map_eq_bind_pure_comp]
  exact avoids_bind secretKey program (fun value => pure (f value))
    avoids (fun value => avoids_pure secretKey (f value))

theorem avoids_countHash {α : Type} (secretKey : SecretKey)
    (program : OracleComp HashSpec α)
    (avoids : Avoids secretKey program) :
    Avoids secretKey (countHash program) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact avoids_pure secretKey (value,0)
  | query_bind query continuation ih =>
      have head := (avoids_query_bind secretKey query continuation).mp avoids
      rw [countHash_query_bind]
      apply (avoids_query_bind secretKey query _).mpr
      refine ⟨head.1,fun answer => ?_⟩
      exact avoids_bind secretKey (countHash (continuation answer))
        (fun result => pure (result.1,result.2+1))
        (ih answer (head.2 answer))
        (fun result => avoids_pure secretKey (result.1,result.2+1))

attribute [irreducible] Avoids

theorem avoids_ask (secretKey : SecretKey)
    (tag level tree leaf chain step : Nat) (payload : List Byte)
    (notOne : tag % 256 ≠ 1) (notSix : tag % 256 ≠ 6) :
    Avoids secretKey
      (SecurityReference.ask tag level tree leaf chain step payload) := by
  change Avoids secretKey
    (liftM (HashSpec.query
      (SecurityRandomOracle.addressedInput
        tag level tree leaf chain step payload)))
  unfold Avoids
  simp only [OracleComp.construct_query,
    source_hit_not_addressed secretKey tag level tree leaf chain step
      payload notOne notSix,not_false_eq_true]
  exact ⟨trivial,fun _ => trivial⟩

theorem bottomLeaf_avoids (secretKey : SecretKey)
    (address : Nat) (seed : Reference.Digest) :
    Avoids secretKey
      (GroupedBalancedVerifyOracle67.bottomLeaf address seed) := by
  unfold GroupedBalancedVerifyOracle67.bottomLeaf
  exact avoids_map secretKey _ _
    (avoids_ask secretKey 2 0 address 0 0 0 (bytes seed)
      (by norm_num) (by norm_num))

theorem node_avoids (secretKey : SecretKey)
    (level address : Nat) (left right : Reference.Digest) :
    Avoids secretKey
      (GroupedBalancedVerifyOracle67.node level address left right) := by
  unfold GroupedBalancedVerifyOracle67.node
  exact avoids_map secretKey _ _
    (avoids_ask secretKey 4 level address 0 0 0
      (bytes left ++ bytes right) (by norm_num) (by norm_num))

theorem chainHash_avoids (secretKey : SecretKey)
    (base leaf : Nat) (chain : Fin 67)
    (step : Nat) (value : Reference.Digest) :
    Avoids secretKey
      (GroupedBalancedVerifyOracle67.chainHash base leaf chain step value) := by
  unfold GroupedBalancedVerifyOracle67.chainHash
  exact avoids_map secretKey _ _
    (avoids_ask secretKey 2 base leaf 0 chain.val step
      (bytes value) (by norm_num) (by norm_num))

theorem compressLeaf_avoids (secretKey : SecretKey)
    (base leaf : Nat) (values : Fin 67 → Reference.Digest) :
    Avoids secretKey
      (GroupedBalancedVerifyOracle67.compressLeaf base leaf values) := by
  unfold GroupedBalancedVerifyOracle67.compressLeaf
  exact avoids_map secretKey _ _
    (avoids_ask secretKey 3 base leaf 0 0 0
      ((List.ofFn values).flatMap bytes) (by norm_num) (by norm_num))

theorem walk_avoids {α : Type} (secretKey : SecretKey)
    (body : Nat → α → OracleComp HashSpec α)
    (bodyAvoids : ∀ step value,
      Avoids secretKey (body step value))
    (start count : Nat) (value : α) :
    Avoids secretKey
      (SecurityReference.walk body start count value) := by
  induction count generalizing start value with
  | zero => exact avoids_pure secretKey value
  | succ count ih =>
      simp only [SecurityReference.walk]
      exact avoids_bind secretKey _ _ (bodyAvoids start value)
        (fun next => ih (start + 1) next)

theorem sequenceFin_avoids {α : Type} (secretKey : SecretKey)
    (n : Nat) (body : Fin n → OracleComp HashSpec α)
    (bodyAvoids : ∀ i, Avoids secretKey (body i)) :
    Avoids secretKey (SecurityReference.sequenceFin n body) := by
  induction n with
  | zero => exact avoids_pure secretKey Fin.elim0
  | succ n ih =>
      simp only [SecurityReference.sequenceFin]
      apply avoids_bind secretKey _ _ (bodyAvoids 0)
      intro head
      apply avoids_bind secretKey _ _
        (ih (fun i => body i.succ) (fun i => bodyAvoids i.succ))
      intro tail
      exact avoids_pure secretKey
        (Fin.cases head tail : Fin (n + 1) → α)

theorem recoverBottom_avoids (secretKey : SecretKey)
    (height address index : Nat)
    (witness : GroupedBottomTree.Witness height) :
    Avoids secretKey
      (GroupedBalancedVerifyOracle67.recoverBottom
        height address index witness) := by
  induction witness generalizing address index with
  | seed seed => exact bottomLeaf_avoids secretKey address seed
  | @step height inner sibling ih =>
      simp only [GroupedBalancedVerifyOracle67.recoverBottom]
      split
      · exact avoids_bind secretKey _ _ (ih (2 * address) index)
          (fun current => node_avoids secretKey height address current sibling)
      · exact avoids_bind secretKey _ _ (ih (2 * address + 1) index)
          (fun current => node_avoids secretKey height address sibling current)

theorem recoverLeaf_avoids (secretKey : SecretKey)
    (base leaf : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest) :
    Avoids secretKey
      (GroupedBalancedVerifyOracle67.recoverLeaf
        base leaf message values) := by
  simp only [GroupedBalancedVerifyOracle67.recoverLeaf]
  apply avoids_bind secretKey _ _
  · apply sequenceFin_avoids
    intro chain
    exact walk_avoids secretKey
      (GroupedBalancedVerifyOracle67.chainHash base leaf chain)
      (fun step value => chainHash_avoids secretKey base leaf chain step value)
      (GroupedBalancedUpperTree67.digit message chain).val
      (GroupedBalancedUpperTree67.maxDigit chain -
        (GroupedBalancedUpperTree67.digit message chain).val)
      (values chain)
  · intro endpoints
    exact compressLeaf_avoids secretKey base leaf endpoints

theorem recoverUpper_avoids (secretKey : SecretKey)
    (base height address index : Nat)
    (message : Reference.Digest)
    (witness : GroupedBalancedUpperTree67.Witness height) :
    Avoids secretKey
      (GroupedBalancedVerifyOracle67.recoverUpper
        base height address index message witness) := by
  induction witness generalizing address index message with
  | leaf values => exact recoverLeaf_avoids secretKey base address message values
  | @step height inner sibling ih =>
      simp only [GroupedBalancedVerifyOracle67.recoverUpper]
      split
      · exact avoids_bind secretKey _ _
          (ih (2 * address) index message)
          (fun current => node_avoids secretKey (base + height) address
            current sibling)
      · exact avoids_bind secretKey _ _
          (ih (2 * address + 1) index message)
          (fun current => node_avoids secretKey (base + height) address
            sibling current)

theorem recoverLayers_avoids (secretKey : SecretKey)
    (heights : List Nat) (base index : Nat)
    (message : Reference.Digest)
    (witnesses : GroupedBalancedScheme67.UpperWitnesses heights) :
    Avoids secretKey
      (GroupedBalancedVerifyOracle67.recoverLayers
        heights base index message witnesses) := by
  induction witnesses generalizing base index message with
  | nil => exact avoids_pure secretKey message
  | @cons height rest head tail ih =>
      simp only [GroupedBalancedVerifyOracle67.recoverLayers]
      exact avoids_bind secretKey _ _
        (recoverUpper_avoids secretKey base height
          (index / 2 ^ height) index message head)
        (fun current => ih (base + height) (index / 2 ^ height) current)

theorem verify_avoids (secretKey : SecretKey)
    (pk : PublicKey) (message : Message)
    (signature : GroupedBalancedScheme67.Signature) :
    Avoids secretKey
      (GroupedBalancedVerifyOracle67.verify pk message signature) := by
  simp only [GroupedBalancedVerifyOracle67.verify]
  apply avoids_bind secretKey _ _
    (avoids_ask secretKey 5 0 0 0 0 0
      (bytes (0 : Bytes 16) ++ bytes message ++ bytes signature.randomizer)
      (by norm_num) (by norm_num))
  intro answer
  apply avoids_bind secretKey _ _
    (recoverBottom_avoids secretKey 10
      (GroupedMixedIndex.bottomTree (answer.extractLsb' 0 160))
      (answer.extractLsb' 0 160).toNat signature.bottom)
  intro bottom
  apply avoids_bind secretKey _ _
    (recoverLayers_avoids secretKey GroupedBalancedScheme67.Heights 10
      (GroupedMixedIndex.bottomTree (answer.extractLsb' 0 160))
      bottom signature.upper)
  intro root
  exact avoids_pure secretKey (decide (root = pk))

theorem sourceFree_lift_of_avoids {α : Type}
    (secretKey : SecretKey) (program : OracleComp HashSpec α)
    (avoids : Avoids secretKey program) :
    SourceFree secretKey (program.liftComp World) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact sourceFree_pure secretKey value
  | query_bind query next ih =>
      have head := (avoids_query_bind secretKey query next).mp avoids
      simp only [OracleComp.liftComp_bind]
      exact sourceFree_bind secretKey _ _
        (sourceFree_query secretKey query head.1)
        (fun answer => ih answer (head.2 answer))

theorem countHash_verify_source_free (secretKey : SecretKey)
    (pk : PublicKey) (message : Message)
    (signature : GroupedBalancedScheme67.Signature) :
    SourceFree secretKey
      ((countHash (GroupedBalancedVerifyOracle67.verify
        pk message signature)).liftComp World) := by
  exact sourceFree_lift_of_avoids secretKey _
    (avoids_countHash secretKey _
      (verify_avoids secretKey pk message signature))

theorem semanticCheck_source_free (secretKey : SecretKey)
    (pk : PublicKey)
    (transcript : Transcript GroupedBalancedProgram67ByteSign.submission.sizes)
    (forgery : Forgery GroupedBalancedProgram67ByteSign.submission.sizes) :
    SourceFree secretKey
      ((semanticCheck pk transcript forgery).liftComp World) := by
  cases forgery with
  | witness message wire =>
      simp only [semanticCheck,OracleComp.liftComp_bind]
      apply sourceFree_bind secretKey _ _
      · exact countHash_verify_source_free secretKey pk message
          (GroupedBalancedWire67.decode wire)
      · intro result
        exact sourceFree_pure secretKey _
  | signature message wire =>
      simp only [semanticCheck,OracleComp.liftComp_bind]
      apply sourceFree_bind secretKey _ _
      · exact countHash_verify_source_free secretKey pk message
          (GroupedBalancedWire67.decode wire)
      · intro result
        exact sourceFree_pure secretKey _

/-- The stopped semantic interaction exposes the stopping point at a public
adversary hash query. Signing and checking run in full before recursion. -/
noncomputable def monitorInteract
    (table : GroupedBalancedGraphPassive67.PointTable)
    (adversary : Adversary GroupedBalancedProgram67ByteSign.submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey) :
    Nat → adversary.State →
      Transcript GroupedBalancedProgram67ByteSign.submission.sizes →
      OracleComp World (Option AttackResult)
  | 0, _, transcript => pure (some ⟨false, transcript.hashCalls⟩)
  | rounds + 1, state, transcript =>
      match adversary.step state with
      | .submit candidate =>
          some <$> (semanticCheck pk transcript candidate).liftComp World
      | .hash input resume =>
          if SourceHit secretKey input then pure none else do
            let answer ← liftM (HashSpec.query input)
            monitorInteract table adversary secretKey pk rounds (resume answer)
              { transcript with hashCalls := transcript.hashCalls + 1 }
      | .sign request resume =>
          if transcript.signingRequests < LIFETIME then do
            let result ←
              (GroupedBalancedSecurityJointContext67.semanticSign
                secretKey table request).liftComp World
            monitorInteract table adversary secretKey pk rounds
              (resume result.1)
              (GroupedBalancedSecurityJointInteraction67.recordView
                transcript request.message result)
          else pure (some ⟨false, transcript.hashCalls⟩)
      | .sample n resume => do
          let answer ← liftM (unifSpec.query n)
          monitorInteract table adversary secretKey pk rounds
            (resume answer) transcript
      | .step next =>
          monitorInteract table adversary secretKey pk rounds next transcript

theorem coin_source_free (secretKey : SecretKey) (n : Nat) :
    SourceFree secretKey
      (liftM (unifSpec.query n) : OracleComp World (Fin (n + 1))) := by
  rfl

theorem monitorInteract_eq_stopBefore
    (table : GroupedBalancedGraphPassive67.PointTable)
    (adversary : Adversary GroupedBalancedProgram67ByteSign.submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey)
    (rounds : Nat) (state : adversary.State)
    (transcript : Transcript GroupedBalancedProgram67ByteSign.submission.sizes) :
    monitorInteract table adversary secretKey pk rounds state transcript =
      SecurityCache.stopBefore (SourceHit secretKey)
        (GroupedBalancedSecurityJointInteraction67.interactWith
          (fullInterface table) adversary secretKey pk
          rounds state transcript) := by
  induction rounds generalizing state transcript with
  | zero => rfl
  | succ rounds ih =>
      simp only [monitorInteract,
        GroupedBalancedSecurityJointInteraction67.interactWith]
      cases action : adversary.step state with
      | submit candidate =>
          dsimp only
          exact (semanticCheck_source_free secretKey pk transcript candidate).symm
      | hash input resume =>
          dsimp only
          change _ = SecurityCache.stopBefore (SourceHit secretKey)
            (liftM (World.query (.inr input)) >>= fun answer =>
              GroupedBalancedSecurityJointInteraction67.interactWith
                (fullInterface table) adversary secretKey pk rounds
                (resume answer)
                { transcript with hashCalls := transcript.hashCalls + 1 })
          rw [SecurityCache.stopBefore_query_bind]
          by_cases hit : SourceHit secretKey input
          · simp [SecurityCache.hashBad, hit]
          · simp only [SecurityCache.hashBad, hit, if_false]
            apply bind_congr
            intro answer
            exact ih (resume answer) _
      | sign request resume =>
          dsimp only
          by_cases allowed : transcript.signingRequests < LIFETIME
          · simp only [if_pos allowed, fullInterface]
            rw [stopBefore_bind_free secretKey]
            · apply bind_congr
              intro result
              exact ih (resume result.1) _
            · exact semanticSign_source_free secretKey table request
          · simp only [if_neg allowed]
            rfl
      | sample n resume =>
          dsimp only
          rw [stopBefore_bind_free secretKey]
          · apply bind_congr
            intro answer
            exact ih (resume answer) transcript
          · exact coin_source_free secretKey n
      | step next =>
          dsimp only
          exact ih next transcript

noncomputable def monitorGame
    (table : GroupedBalancedGraphPassive67.PointTable)
    (adversary : Adversary GroupedBalancedProgram67ByteSign.submission.sizes)
    (rounds : Nat) (secretKey : SecretKey) :
    OracleComp World (Option AttackResult) :=
  let pk := GroupedBalancedGraphMonitorSetupBound67.rootPublic table
  monitorInteract table adversary secretKey pk rounds
    (adversary.initial pk (0 : Cache)) { hashCalls := 3983 }

theorem monitorGame_eq_stopBefore
    (table : GroupedBalancedGraphPassive67.PointTable)
    (adversary : Adversary GroupedBalancedProgram67ByteSign.submission.sizes)
    (rounds : Nat) (secretKey : SecretKey) :
    monitorGame table adversary rounds secretKey =
      SecurityCache.stopBefore (SourceHit secretKey)
        (GroupedBalancedSecurityJointInteraction67.gameWith
          (fullInterface table) adversary rounds secretKey) := by
  simp only [monitorGame,
    GroupedBalancedSecurityJointInteraction67.gameWith,
    fullInterface, GroupedBalancedSecurityOfficialHybrid67.tableInterface,
    OracleComp.liftComp_pure, pure_bind]
  exact monitorInteract_eq_stopBefore table adversary secretKey
    (GroupedBalancedGraphMonitorSetupBound67.rootPublic table) rounds _ _

/-- A stopped source probe is already one of the public inputs in the same
unstopped semantic execution. It therefore falls under the existing
secret-key-query trace event, without an additional risk term. -/
theorem monitor_none_le_secretKey_trace
    (table : GroupedBalancedGraphPassive67.PointTable)
    (adversary : Adversary GroupedBalancedProgram67ByteSign.submission.sizes)
    (rounds : Nat) (secretKey : SecretKey) :
    Pr[= none | SecurityGraphHidden.observe
      (monitorGame table adversary rounds secretKey)
      (GroupedBalancedPlantedCache67.planted table)] ≤
    Pr[fun result =>
      SecuritySecretKey.SecretKeyHitTrace result.2 secretKey |
      SecurityGraphHidden.observe
        (SecurityTrace.traceHashes
          (GroupedBalancedSecurityJointInteraction67.gameWith
            (fullInterface table) adversary rounds secretKey))
        (GroupedBalancedPlantedCache67.planted table)] := by
  rw [monitorGame_eq_stopBefore]
  change Pr[= none | (simulateQ SecurityCache.implementation
      (SecurityCache.stopBefore (SourceHit secretKey)
        (GroupedBalancedSecurityJointInteraction67.gameWith
          (fullInterface table) adversary rounds secretKey))).run'
      (GroupedBalancedPlantedCache67.planted table)] ≤ _
  rw [SecurityTrace.prob_stop_eq_traceHits]
  apply probEvent_mono
  intro result _ hit
  obtain ⟨input, member, source⟩ := hit
  exact source_hit_in_trace secretKey result.2 input member source

noncomputable def keepSource {α : Type} (secretKey : SecretKey)
    (result : α × List Query) : Option α :=
  if SecurityTrace.TraceHits (SourceHit secretKey) result.2 then
    none else some result.1

private theorem run_query {α : Type} (input : World.Domain)
    (next : World.Range input → OracleComp World α)
    (cache : QueryCache HashSpec) :
    (simulateQ SecurityCache.implementation
      (liftM (World.query input) >>= next)).run' cache =
      ((SecurityCache.implementation input).run cache >>= fun result =>
        (simulateQ SecurityCache.implementation
          (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run'_eq, StateT.run_bind,
    map_bind]

private theorem run_map {α β : Type}
    (program : OracleComp World α) (f : α → β)
    (cache : QueryCache HashSpec) :
    (simulateQ SecurityCache.implementation (f <$> program)).run' cache =
      f <$> (simulateQ SecurityCache.implementation program).run' cache := by
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map]

private theorem map_const {α β : Type} (program : ProbComp α) (value : β) :
    𝒮[(fun _ => value) <$> program] =
      𝒮[(pure value : ProbComp β)] := by
  classical
  let : DecidableEq β := Classical.decEq β
  apply evalSPMF_ext
  intro output
  simp only [map_eq_pure_bind, probOutput_bind_const]
  simp

/-- The complete stopped output has the same law as the full hash-query log
with the first source-hit event erased. This keeps the win bit and exact
hash-call counter on every surviving path. -/
theorem stopped_eq_source_trace {α : Type}
    (secretKey : SecretKey) (program : OracleComp World α)
    (cache : QueryCache HashSpec) :
    𝒮[SecurityGraphHidden.observe
      (SecurityCache.stopBefore (SourceHit secretKey) program) cache] =
    𝒮[keepSource secretKey <$>
      SecurityGraphHidden.observe (SecurityTrace.traceHashes program) cache] := by
  unfold SecurityGraphHidden.observe
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value => simp [keepSource, SecurityTrace.TraceHits]
  | query_bind input next ih =>
      rw [SecurityCache.stopBefore_query_bind,
        SecurityTrace.traceHashes_query_bind]
      by_cases hit : SecurityCache.hashBad (SourceHit secretKey) input
      · rw [if_pos hit, run_query]
        simp only [bind_pure_comp, run_map, map_bind, Functor.map_map]
        have constant :
            (fun result : α × List Query =>
              keepSource secretKey
                (result.1, SecurityTrace.prependHash input result.2)) =
              fun _ => (none : Option α) := by
          funext result
          simp only [keepSource, SecurityTrace.traceHits_prepend,
            hit, true_or, if_true]
        rw [constant]
        simpa only [map_bind, simulateQ_pure, StateT.run'_eq,
          StateT.run_pure, map_pure] using
          (map_const ((SecurityCache.implementation input).run cache >>= fun result =>
            (simulateQ SecurityCache.implementation
              (SecurityTrace.traceHashes (next result.1))).run' result.2)
            (none : Option α)).symm
      · rw [if_neg hit, run_query, run_query]
        simp only [bind_pure_comp, run_map, map_bind, Functor.map_map]
        apply evalSPMF_bind_congr
        intro result _
        rw [ih result.1 result.2]
        congr 1
        congr 1
        funext tail
        simp only [keepSource, SecurityTrace.traceHits_prepend,
          hit, false_or]

/-- Hash-query logging commutes with projecting an output. In particular,
logging the official component of a paired run keeps the paired run's exact
public hash-input list. -/
theorem traceHashes_map {α β : Type}
    (program : OracleComp World α) (f : α → β) :
    SecurityTrace.traceHashes (f <$> program) =
      (fun result => (f result.1, result.2)) <$>
        SecurityTrace.traceHashes program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [map_bind, SecurityTrace.traceHashes_query_bind]
      apply bind_congr
      intro answer
      rw [ih answer]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]

theorem stopBefore_map {α β : Type}
    (secretKey : SecretKey) (program : OracleComp World α)
    (f : α → β) :
    SecurityCache.stopBefore (SourceHit secretKey) (f <$> program) =
      Option.map f <$>
        SecurityCache.stopBefore (SourceHit secretKey) program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [map_bind, SecurityCache.stopBefore_query_bind,
        SecurityCache.stopBefore_query_bind]
      by_cases hit : SecurityCache.hashBad (SourceHit secretKey) input
      · simp [hit]
      · simp only [if_neg hit, map_bind]
        apply bind_congr
        intro answer
        exact ih answer

theorem cutoffWithRemaining_map {α β : Type}
    (program : OracleComp World α) (f : α → β)
    (budget : Nat) :
    GroupedBalancedGraphViewWorld67.cutoffWithRemaining
      (f <$> program) budget =
    (fun result => (Option.map f result.1, result.2)) <$>
      GroupedBalancedGraphViewWorld67.cutoffWithRemaining
        program budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => rfl
  | query_bind input next ih =>
      rw [map_bind,
        GroupedBalancedGraphViewWorld67.cutoff_query_bind,
        GroupedBalancedGraphViewWorld67.cutoff_query_bind]
      by_cases allowed :
          GroupedBalancedGraphViewWorld67.hashCharge input ≤ budget
      · simp only [if_pos allowed, map_bind]
        apply bind_congr
        intro answer
        rw [ih answer]
      · simp [if_neg allowed]

theorem budget_cutoff_map {α β : Type}
    (program : OracleComp SecurityGameHop.GameWorld α)
    (f : α → β) (budget : Nat) :
    SecurityBudget.cutoff (f <$> program) budget =
      Option.map f <$> SecurityBudget.cutoff program budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => rfl
  | query_bind input next ih =>
      rw [map_bind, SecurityBudget.cutoff_query_bind,
        SecurityBudget.cutoff_query_bind]
      by_cases allowed : SecurityBudget.charge input ≤ budget
      · simp only [if_pos allowed, map_bind]
        apply bind_congr
        intro answer
        exact ih answer _
      · simp [if_neg allowed]

/-- Cutting off the metered game and discarding its counter gives precisely the
cut off original game. This holds as a program identity, before interpreting
either game with a random oracle. -/
theorem cutoff_counted_fst {α : Type}
    (program : OracleComp SecurityGameHop.GameWorld α)
    (budget : Nat) :
    Option.map Prod.fst <$>
      SecurityBudget.cutoff (SecurityBudget.counted program) budget =
    SecurityBudget.cutoff program budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => rfl
  | query_bind input next ih =>
      rw [SecurityBudget.counted_query_bind]
      rw [SecurityBudget.cutoff_query_bind, SecurityBudget.cutoff_query_bind]
      by_cases allowed : SecurityBudget.charge input ≤ budget
      · simp only [if_pos allowed, map_bind]
        apply bind_congr
        intro answer
        have hmap :
            (do
              let result ← SecurityBudget.counted (next answer)
              pure (result.1, result.2 + SecurityBudget.charge input)) =
            (fun result => (result.1, result.2 + SecurityBudget.charge input)) <$>
              SecurityBudget.counted (next answer) := by
          simp only [map_eq_bind_pure_comp, Function.comp_def]
        rw [hmap]
        rw [budget_cutoff_map]
        simp only [Functor.map_map, Function.comp_def, Option.map_map]
        exact ih answer _
      · simp [if_neg allowed]

/-- The single stopped win-or-hit event is bounded by one union event on the
same unstopped random-oracle trace. -/
theorem stopped_risk_le_source_trace {α : Type}
    (secretKey : SecretKey) (program : OracleComp World α)
    (cache : QueryCache HashSpec) (event : α → Prop) :
    Pr[GroupedBalancedSecurityOfficialHybrid67.StoppedRisk event |
      SecurityGraphHidden.observe
        (SecurityCache.stopBefore (SourceHit secretKey) program) cache] ≤
    Pr[fun result : α × List Query =>
      event result.1 ∨
        SecuritySecretKey.SecretKeyHitTrace result.2 secretKey |
      SecurityGraphHidden.observe
        (SecurityTrace.traceHashes program) cache] := by
  rw [probEvent_congr'
    (fun _ _ => Iff.rfl)
    (stopped_eq_source_trace secretKey program cache)]
  rw [probEvent_map]
  apply probEvent_mono
  intro result _ risk
  by_cases hit : SecurityTrace.TraceHits (SourceHit secretKey) result.2
  · right
    obtain ⟨input, member, source⟩ := hit
    exact source_hit_in_trace secretKey result.2 input member source
  · left
    simpa only [Function.comp_apply, keepSource, hit, if_false,
      GroupedBalancedSecurityOfficialHybrid67.StoppedRisk] using risk

noncomputable def fullTraceRisk
    (adversary : Adversary GroupedBalancedProgram67ByteSign.submission.sizes)
    (rounds : Nat) :
    ProbComp (SecretKey × (AttackResult × List Query)) := do
  let table ← $ᵗ GroupedBalancedGraphPassive67.PointTable
  let secretKey ← sampleSecretKey
  let result ← SecurityGraphHidden.observe
    (SecurityTrace.traceHashes
      (GroupedBalancedSecurityJointInteraction67.gameWith
        (fullInterface table) adversary rounds secretKey))
    (GroupedBalancedPlantedCache67.planted table)
  pure (secretKey, result)

/-- The submitted win probability is charged to one planted, fully semantic
hash-query trace event. The source hit is in the same trace as the win. -/
theorem official_le_full_trace_risk
    (refinement : GroupedBalancedSecurityCheckConditional67.VerifierRefinement)
    (adversary : Adversary GroupedBalancedProgram67ByteSign.submission.sizes)
    (rounds : Nat) (event : AttackResult → Prop) :
    Pr[event |
      GroupedBalancedProgram67ByteSign.submission.securityExperiment
        adversary rounds] ≤
    Pr[fun pair : SecretKey × (AttackResult × List Query) =>
      event pair.2.1 ∨
        SecuritySecretKey.SecretKeyHitTrace pair.2.2 pair.1 |
      fullTraceRisk adversary rounds] := by
  have first :=
    GroupedBalancedSecurityFullSemantic67.official_le_full_stopped_risk
      refinement adversary rounds event
  apply first.trans
  unfold GroupedBalancedSecurityFullSemantic67.fullStoppedRisk
    fullTraceRisk
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
  simpa only [bind_pure_comp, probEvent_map, Function.comp_def,
    probEvent_pure] using
    (stopped_risk_le_source_trace secretKey
      (GroupedBalancedSecurityJointInteraction67.gameWith
        (fullInterface table) adversary rounds secretKey)
      (GroupedBalancedPlantedCache67.planted table) event)

def translatedQuery (secretKey : SecretKey) :
    SecurityGameHop.GameWorld.Domain → World.Domain
  | .inl n => .inl n
  | .inr (.inl slot) => .inr (SecurityDerivation.input secretKey slot)
  | .inr (.inr input) => .inr input

def SourceCoveredQuery (secretKey : SecretKey)
    (query : SecurityGameHop.GameWorld.Domain) : Prop :=
  SecurityCache.hashBad (SourceHit secretKey)
    (translatedQuery secretKey query) →
    SecurityGameHop.isBad secretKey query

def SourceCovered (secretKey : SecretKey) {α : Type}
    (program : OracleComp SecurityGameHop.GameWorld α) : Prop :=
  OracleComp.construct (fun _ => True)
    (fun query _ next =>
      SourceCoveredQuery secretKey query ∧ ∀ answer, next answer)
    program

theorem covered_query_bind {α : Type}
    (secretKey : SecretKey)
    (query : SecurityGameHop.GameWorld.Domain)
    (next : SecurityGameHop.GameWorld.Range query →
      OracleComp SecurityGameHop.GameWorld α) :
    SourceCovered secretKey
      (liftM (SecurityGameHop.GameWorld.query query) >>= next) ↔
      SourceCoveredQuery secretKey query ∧
        ∀ answer, SourceCovered secretKey (next answer) := Iff.rfl

theorem covered_private_randomizer (secretKey : SecretKey)
    (message : Message) :
    SourceCoveredQuery secretKey
      (.inr (.inl (.randomizer message))) := by
  intro hit
  exact (GroupedBalancedSecurityOfficialHybrid67.source_hit_not_randomizer
    secretKey message) hit

theorem covered_public (secretKey : SecretKey)
    (input : Query) :
    SourceCoveredQuery secretKey (.inr (.inr input)) :=
  GroupedBalancedSecuritySourceHybrid67.source_hit_public_secretKey
    secretKey input

theorem covered_coin (secretKey : SecretKey) (n : Nat) :
    SourceCoveredQuery secretKey (.inl n) := by
  intro hit
  cases hit

theorem covered_pure {α : Type} (secretKey : SecretKey)
    (value : α) :
    SourceCovered secretKey
      (pure value : OracleComp SecurityGameHop.GameWorld α) := trivial

theorem covered_bind {α β : Type} (secretKey : SecretKey)
    (first : OracleComp SecurityGameHop.GameWorld α)
    (next : α → OracleComp SecurityGameHop.GameWorld β)
    (firstCovered : SourceCovered secretKey first)
    (nextCovered : ∀ value, SourceCovered secretKey (next value)) :
    SourceCovered secretKey (first >>= next) := by
  induction first using OracleComp.inductionOn with
  | pure value => exact nextCovered value
  | query_bind query continuation ih =>
      have head :=
        (covered_query_bind secretKey query continuation).mp firstCovered
      apply (covered_query_bind secretKey query
        (fun answer => continuation answer >>= next)).mpr
      exact ⟨head.1, fun answer => ih answer (head.2 answer)⟩

theorem covered_counted {α : Type} (secretKey : SecretKey)
    (program : OracleComp SecurityGameHop.GameWorld α)
    (covered : SourceCovered secretKey program) :
    SourceCovered secretKey (SecurityBudget.counted program) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact covered_pure secretKey (value, 0)
  | query_bind query next ih =>
      have head := (covered_query_bind secretKey query next).mp covered
      rw [SecurityBudget.counted_query_bind]
      apply (covered_query_bind secretKey query _).mpr
      refine ⟨head.1, fun answer => ?_⟩
      exact covered_bind secretKey (SecurityBudget.counted (next answer))
        (fun result => pure (result.1,
          result.2 + SecurityBudget.charge query))
        (ih answer (head.2 answer))
        (fun result => covered_pure secretKey _)

theorem covered_gameView {α : Type}
    (secretKey : SecretKey)
    (table : GroupedBalancedGraphPassive67.PointTable)
    (cache : QueryCache GroupedBalancedGraphPassive67.PointSpec)
    (interaction : GroupedBalancedGraphInteraction67.Interaction α) :
    SourceCovered secretKey
      (GroupedBalancedGameWorld67.gameView table cache interaction) := by
  induction interaction with
  | done value => exact covered_pure secretKey value
  | coin n next ih =>
      simp only [GroupedBalancedGameWorld67.gameView]
      apply (covered_query_bind secretKey (.inl n) _).mpr
      exact ⟨covered_coin secretKey n, fun answer => ih answer⟩
  | hash input next ih =>
      simp only [GroupedBalancedGameWorld67.gameView]
      apply (covered_query_bind secretKey (.inr (.inr input)) _).mpr
      exact ⟨covered_public secretKey input, fun answer => ih answer⟩
  | sign message next ih =>
      simp only [GroupedBalancedGameWorld67.gameView]
      apply (covered_query_bind secretKey
        (.inr (.inl (.randomizer message))) _).mpr
      refine ⟨covered_private_randomizer secretKey message, fun randomizer => ?_⟩
      apply (covered_query_bind secretKey
        (.inr (.inr
          (SecurityRandomOracle.indexInput message randomizer))) _).mpr
      refine ⟨covered_public secretKey
        (SecurityRandomOracle.indexInput message randomizer), fun indexAnswer => ?_⟩
      exact ih _

theorem covered_cutoff {α : Type} (secretKey : SecretKey)
    (program : OracleComp SecurityGameHop.GameWorld α)
    (covered : SourceCovered secretKey program)
    (budget : Nat) :
    SourceCovered secretKey (SecurityBudget.cutoff program budget) := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => exact covered_pure secretKey (some value)
  | query_bind query next ih =>
      have head := (covered_query_bind secretKey query next).mp covered
      rw [SecurityBudget.cutoff_query_bind]
      by_cases allowed : SecurityBudget.charge query ≤ budget
      · rw [if_pos allowed]
        apply (covered_query_bind secretKey query _).mpr
        exact ⟨head.1, fun answer =>
          ih answer (head.2 answer) (budget - SecurityBudget.charge query)⟩
      · rw [if_neg allowed]
        exact covered_pure secretKey none

theorem source_stop_le {α : Type} (secretKey : SecretKey)
    (program : OracleComp SecurityGameHop.GameWorld α)
    (covered : SourceCovered secretKey program)
    (cache : QueryCache HashSpec) (event : α → Prop) :
    Pr[StoppedRisk event | SecurityGraphHidden.observe
      (SecurityCache.stopBefore (SourceHit secretKey)
        (GroupedBalancedGameWorld67.resolve secretKey program)) cache] ≤
    Pr[StoppedRisk event | SecurityGraphHidden.observe
      (GroupedBalancedGameWorld67.resolve secretKey
        (SecurityGameHop.stop secretKey program)) cache] := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp [SecurityGameHop.stop, GroupedBalancedGameWorld67.resolve]
  | query_bind query next ih =>
      have head := (covered_query_bind secretKey query next).mp covered
      cases query with
      | inl n =>
          rw [SecurityGameHop.stop_query_bind]
          rw [if_neg (by simp [SecurityGameHop.isBad])]
          simp only [GroupedBalancedGameWorld67.resolve,
            simulateQ_bind, simulateQ_spec_query]
          change Pr[StoppedRisk event | SecurityGraphHidden.observe
            (SecurityCache.stopBefore (SourceHit secretKey)
              (GroupedBalancedGameWorld67.translate secretKey (.inl n) >>= fun answer =>
                GroupedBalancedGameWorld67.resolve secretKey (next answer))) cache] ≤
            Pr[StoppedRisk event | SecurityGraphHidden.observe
              (GroupedBalancedGameWorld67.translate secretKey (.inl n) >>= fun answer =>
                GroupedBalancedGameWorld67.resolve secretKey
                  (SecurityGameHop.stop secretKey (next answer))) cache]
          change Pr[StoppedRisk event | SecurityGraphHidden.observe
            (SecurityCache.stopBefore (SourceHit secretKey)
              (liftM (World.query (.inl n)) >>= fun answer =>
                GroupedBalancedGameWorld67.resolve secretKey (next answer))) cache] ≤
            Pr[StoppedRisk event | SecurityGraphHidden.observe
              (liftM (World.query (.inl n)) >>= fun answer =>
                GroupedBalancedGameWorld67.resolve secretKey
                  (SecurityGameHop.stop secretKey (next answer))) cache]
          rw [SecurityCache.stopBefore_query_bind]
          rw [if_neg (by simp [SecurityCache.hashBad])]
          unfold SecurityGraphHidden.observe
          rw [SecurityCache.run'_query_bind,
            SecurityCache.run'_query_bind]
          simp only [probEvent_bind_eq_tsum]
          apply ENNReal.tsum_le_tsum
          intro result
          exact mul_le_mul' le_rfl
            (ih result.1 (head.2 result.1) result.2)
      | inr query =>
          cases query with
          | inl slot =>
              have noSource :
                  ¬ SourceHit secretKey
                    (SecurityDerivation.input secretKey slot) := by
                intro source
                exact head.1 source
              rw [SecurityGameHop.stop_query_bind]
              rw [if_neg (by simp [SecurityGameHop.isBad,
                SecuritySeparation.publicSecretKeyHit])]
              simp only [GroupedBalancedGameWorld67.resolve,
                simulateQ_bind, simulateQ_spec_query]
              change Pr[StoppedRisk event | SecurityGraphHidden.observe
                (SecurityCache.stopBefore (SourceHit secretKey)
                  (GroupedBalancedGameWorld67.translate secretKey
                    (.inr (.inl slot)) >>= fun answer =>
                    GroupedBalancedGameWorld67.resolve secretKey (next answer))) cache] ≤
                Pr[StoppedRisk event | SecurityGraphHidden.observe
                  (GroupedBalancedGameWorld67.translate secretKey
                    (.inr (.inl slot)) >>= fun answer =>
                    GroupedBalancedGameWorld67.resolve secretKey
                      (SecurityGameHop.stop secretKey (next answer))) cache]
              change Pr[StoppedRisk event | SecurityGraphHidden.observe
                (SecurityCache.stopBefore (SourceHit secretKey)
                  (liftM (World.query
                    (.inr (SecurityDerivation.input secretKey slot))) >>= fun answer =>
                    GroupedBalancedGameWorld67.resolve secretKey (next answer))) cache] ≤
                Pr[StoppedRisk event | SecurityGraphHidden.observe
                  (liftM (World.query
                    (.inr (SecurityDerivation.input secretKey slot))) >>= fun answer =>
                    GroupedBalancedGameWorld67.resolve secretKey
                      (SecurityGameHop.stop secretKey (next answer))) cache]
              rw [SecurityCache.stopBefore_query_bind]
              rw [if_neg (by simpa [SecurityCache.hashBad] using noSource)]
              unfold SecurityGraphHidden.observe
              rw [SecurityCache.run'_query_bind,
                SecurityCache.run'_query_bind]
              simp only [probEvent_bind_eq_tsum]
              apply ENNReal.tsum_le_tsum
              intro result
              exact mul_le_mul' le_rfl
                (ih result.1 (head.2 result.1) result.2)
          | inr input =>
              by_cases graphBad :
                  SecurityGameHop.isBad secretKey (.inr (.inr input))
              · rw [SecurityGameHop.stop_query_bind, if_pos graphBad]
                have rhs :
                    Pr[StoppedRisk event | SecurityGraphHidden.observe
                      (GroupedBalancedGameWorld67.resolve secretKey
                        (pure none : OracleComp SecurityGameHop.GameWorld
                          (Option α))) cache] = 1 := by
                  simp [GroupedBalancedGameWorld67.resolve,
                    SecurityGraphHidden.observe, StoppedRisk]
                rw [rhs]
                exact probEvent_le_one
              · have noSource : ¬ SourceHit secretKey input := by
                  intro source
                  exact graphBad (head.1 source)
                rw [SecurityGameHop.stop_query_bind, if_neg graphBad]
                simp only [GroupedBalancedGameWorld67.resolve,
                  simulateQ_bind, simulateQ_spec_query]
                change Pr[StoppedRisk event | SecurityGraphHidden.observe
                  (SecurityCache.stopBefore (SourceHit secretKey)
                    (GroupedBalancedGameWorld67.translate secretKey
                      (.inr (.inr input)) >>= fun answer =>
                      GroupedBalancedGameWorld67.resolve secretKey (next answer))) cache] ≤
                  Pr[StoppedRisk event | SecurityGraphHidden.observe
                    (GroupedBalancedGameWorld67.translate secretKey
                      (.inr (.inr input)) >>= fun answer =>
                      GroupedBalancedGameWorld67.resolve secretKey
                        (SecurityGameHop.stop secretKey (next answer))) cache]
                change Pr[StoppedRisk event | SecurityGraphHidden.observe
                  (SecurityCache.stopBefore (SourceHit secretKey)
                    (liftM (World.query (.inr input)) >>= fun answer =>
                      GroupedBalancedGameWorld67.resolve secretKey (next answer))) cache] ≤
                  Pr[StoppedRisk event | SecurityGraphHidden.observe
                    (liftM (World.query (.inr input)) >>= fun answer =>
                      GroupedBalancedGameWorld67.resolve secretKey
                        (SecurityGameHop.stop secretKey (next answer))) cache]
                rw [SecurityCache.stopBefore_query_bind]
                rw [if_neg (by simpa [SecurityCache.hashBad] using noSource)]
                unfold SecurityGraphHidden.observe
                rw [SecurityCache.run'_query_bind,
                  SecurityCache.run'_query_bind]
                simp only [probEvent_bind_eq_tsum]
                apply ENNReal.tsum_le_tsum
                intro result
                exact mul_le_mul' le_rfl
                  (ih result.1 (head.2 result.1) result.2)

theorem simulate_real_resolve {α : Type} (secretKey : SecretKey)
    (program : OracleComp SecurityGameHop.GameWorld α) :
    simulateQ (SecurityGameHop.realGameOracle secretKey) program =
      simulateQ SecurityCache.implementation
        (GroupedBalancedGameWorld67.resolve secretKey program) := by
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
      simulateQ SecurityCache.implementation
        (GroupedBalancedGameWorld67.translate secretKey query) =
        SecurityGameHop.realGameOracle secretKey query := by
    cases query with
    | inl coin => rfl
    | inr query =>
        cases query with
        | inl slot =>
            exact hash_query (SecurityDerivation.input secretKey slot)
        | inr query => exact hash_query query
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
      simp only [GroupedBalancedGameWorld67.resolve,
        simulateQ_bind, simulateQ_spec_query, step] at ih ⊢
      exact bind_congr ih

theorem source_stop_le_secret_trace {α : Type}
    (secretKey : SecretKey)
    (program : OracleComp SecurityGameHop.GameWorld α)
    (covered : SourceCovered secretKey program)
    (cache : QueryCache HashSpec) (event : α → Prop) :
    Pr[StoppedRisk event | SecurityGraphHidden.observe
      (SecurityCache.stopBefore (SourceHit secretKey)
        (GroupedBalancedGameWorld67.resolve secretKey program)) cache] ≤
    Pr[fun result : α × List Query =>
      event result.1 ∨
        SecuritySecretKey.SecretKeyHitTrace result.2 secretKey |
      (simulateQ (SecurityGameHop.realGameOracle secretKey)
        (SecurityGameHop.tracePublic program)).run' cache] := by
  have first := source_stop_le secretKey program covered cache event
  have same :
      𝒮[SecurityGraphHidden.observe
        (GroupedBalancedGameWorld67.resolve secretKey
          (SecurityGameHop.stop secretKey program)) cache] =
      𝒮[SecuritySecretKeyStoppedTrace.keep secretKey <$>
        (simulateQ (SecurityGameHop.realGameOracle secretKey)
          (SecurityGameHop.tracePublic program)).run' cache] := by
    rw [SecurityGraphHidden.observe,
      ← simulate_real_resolve secretKey
        (SecurityGameHop.stop secretKey program)]
    exact SecuritySecretKeyStoppedTrace.stopped_eq_trace
      (SecurityGameHop.realGameOracle secretKey)
      secretKey program cache
  have events := probEvent_congr'
    (p := StoppedRisk event) (q := StoppedRisk event)
    (fun _ _ => Iff.rfl) same
  rw [probEvent_map] at events
  calc
    _ ≤ _ := first
    _ = _ := events
    _ = _ := by
      apply probEvent_congr' _ rfl
      intro result _
      simp only [Function.comp_apply,
        SecuritySecretKeyStoppedTrace.keep]
      split <;> simp_all [StoppedRisk]

theorem source_union_any {α : Type}
    (secretKey : SecretKey)
    (answers : GroupedBalancedPrivateFactors67.PrivateTable)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable)
    (program : OracleComp World α) (event : α → Prop) :
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

noncomputable def jointProgram {α : Type}
    (program : SecretKey → GroupedBalancedGraphPassive67.PointTable →
      OracleComp World α) : ProbComp α := do
  let secretKey ← sampleSecretKey
  let answers ← $ᵗ GroupedBalancedPrivateFactors67.PrivateTable
  let labels ← $ᵗ GroupedBalancedSecurityGraph67.Labels
  let ghosts ← $ᵗ GroupedBalancedGlobalPaired67.GhostTable
  SecurityGraphHidden.observe
    (program secretKey
      (GroupedBalancedSecurityJointTable67.tableOf answers labels ghosts))
    (jointCache secretKey answers labels)

noncomputable def plantedStoppedProgram {α : Type}
    (program : SecretKey → GroupedBalancedGraphPassive67.PointTable →
      OracleComp World α) : ProbComp (Option α) := do
  let table ← $ᵗ GroupedBalancedGraphPassive67.PointTable
  let secretKey ← sampleSecretKey
  SecurityGraphHidden.observe
    (SecurityCache.stopBefore (SourceHit secretKey)
      (program secretKey table))
    (GroupedBalancedPlantedCache67.planted table)

/-- Uniform-table source replacement for any World program, including a
graph-budget cutoff. A cutoff result of `none` stays a completed value and is
therefore excluded by events that require successful completion. -/
theorem joint_le_planted_stopped {α : Type}
    (program : SecretKey → GroupedBalancedGraphPassive67.PointTable →
      OracleComp World α) (event : α → Prop) :
    Pr[event | jointProgram program] ≤
      Pr[StoppedRisk event | plantedStoppedProgram program] := by
  have raw :
      Pr[event | jointProgram program] ≤
      Pr[StoppedRisk event | do
        let secretKey ← sampleSecretKey
        let answers ← $ᵗ GroupedBalancedPrivateFactors67.PrivateTable
        let labels ← $ᵗ GroupedBalancedSecurityGraph67.Labels
        let ghosts ← $ᵗ GroupedBalancedGlobalPaired67.GhostTable
        SecurityGraphHidden.observe
          (SecurityCache.stopBefore (SourceHit secretKey)
            (program secretKey
              (GroupedBalancedSecurityJointTable67.tableOf
                answers labels ghosts)))
          (plantedCache answers labels ghosts)] := by
    unfold jointProgram
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
    exact source_union_any secretKey answers labels ghosts
      (program secretKey
        (GroupedBalancedSecurityJointTable67.tableOf answers labels ghosts))
      event
  apply raw.trans_eq
  apply probEvent_congr' (fun _ _ => Iff.rfl)
  unfold plantedStoppedProgram
  calc
    𝒮[do
      let secretKey ← sampleSecretKey
      let answers ← $ᵗ GroupedBalancedPrivateFactors67.PrivateTable
      let labels ← $ᵗ GroupedBalancedSecurityGraph67.Labels
      let ghosts ← $ᵗ GroupedBalancedGlobalPaired67.GhostTable
      SecurityGraphHidden.observe
        (SecurityCache.stopBefore (SourceHit secretKey)
          (program secretKey
            (GroupedBalancedSecurityJointTable67.tableOf
              answers labels ghosts)))
        (plantedCache answers labels ghosts)] =
      𝒮[do
        let secretKey ← sampleSecretKey
        let table ← $ᵗ GroupedBalancedGraphPassive67.PointTable
        SecurityGraphHidden.observe
          (SecurityCache.stopBefore (SourceHit secretKey)
            (program secretKey table))
          (GroupedBalancedPlantedCache67.planted table)] := by
      apply evalSPMF_bind_congr
      intro secretKey _
      simpa only [plantedCache] using
        (GroupedBalancedSecurityJointTable67.uniform_table
          (fun table => SecurityGraphHidden.observe
            (SecurityCache.stopBefore (SourceHit secretKey)
              (program secretKey table))
            (GroupedBalancedPlantedCache67.planted table)))
    _ = _ := evalSPMF_bind_bind_swap _ _ _

noncomputable def plantedRealTraceProgram {α : Type}
    (program : SecretKey → GroupedBalancedGraphPassive67.PointTable →
      OracleComp SecurityGameHop.GameWorld α) :
    ProbComp (SecretKey × (α × List Query)) := do
  let table ← $ᵗ GroupedBalancedGraphPassive67.PointTable
  let secretKey ← sampleSecretKey
  let result ← (simulateQ
    (SecurityGameHop.realGameOracle secretKey)
    (SecurityGameHop.tracePublic (program secretKey table))).run'
      (GroupedBalancedPlantedCache67.planted table)
  pure (secretKey, result)

/-- Generic source-cache hybrid into the legacy typed graph trace. Supplying
the graph's query-budget cutoff as `program` confines both the source stop and
the secret-key hit trace to the same bounded prefix. -/
theorem joint_le_planted_real_trace {α : Type}
    (program : SecretKey → GroupedBalancedGraphPassive67.PointTable →
      OracleComp SecurityGameHop.GameWorld α)
    (covered : ∀ secretKey table,
      SourceCovered secretKey (program secretKey table))
    (event : α → Prop) :
    Pr[event | jointProgram (fun secretKey table =>
      GroupedBalancedGameWorld67.resolve secretKey
        (program secretKey table))] ≤
    Pr[fun pair : SecretKey × (α × List Query) =>
      event pair.2.1 ∨
        SecuritySecretKey.SecretKeyHitTrace pair.2.2 pair.1 |
      plantedRealTraceProgram program] := by
  have first := joint_le_planted_stopped
    (fun secretKey table =>
      GroupedBalancedGameWorld67.resolve secretKey
        (program secretKey table)) event
  apply first.trans
  unfold plantedStoppedProgram plantedRealTraceProgram
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
    Function.comp_def, probEvent_pure] using
    (source_stop_le_secret_trace secretKey
      (program secretKey table) (covered secretKey table)
      (GroupedBalancedPlantedCache67.planted table) event)

/-- The source hybrid for the actual graph game stops at the graph's total H
budget. Thus its secret-input trace charges only observations made before the
budget was exhausted. -/
theorem joint_graph_cutoff_le_planted_trace {α : Type}
    (interaction : QueryCache GroupedBalancedGraphPassive67.PointSpec →
      GroupedBalancedGraphInteraction67.Interaction α)
    (budget : Nat) (event : Option α → Prop) :
    Pr[event | jointProgram (fun secretKey table =>
      GroupedBalancedGameWorld67.resolve secretKey
        (SecurityBudget.cutoff
          (GroupedBalancedGameWorld67.gameView table
            (GroupedBalancedGraphMonitorSetup67.cache table)
            (interaction (GroupedBalancedGraphMonitorSetup67.cache table)))
          budget))] ≤
    Pr[fun pair : SecretKey × (Option α × List Query) =>
      event pair.2.1 ∨
        SecuritySecretKey.SecretKeyHitTrace pair.2.2 pair.1 |
      plantedRealTraceProgram (fun _ table =>
        SecurityBudget.cutoff
          (GroupedBalancedGameWorld67.gameView table
            (GroupedBalancedGraphMonitorSetup67.cache table)
            (interaction (GroupedBalancedGraphMonitorSetup67.cache table)))
          budget)] := by
  apply joint_le_planted_real_trace
  intro secretKey table
  exact covered_cutoff secretKey _
    (covered_gameView secretKey table _ _) budget

theorem resolve_cutoff {α : Type} (secretKey : SecretKey)
    (program : OracleComp SecurityGameHop.GameWorld α)
    (budget : Nat) :
    GroupedBalancedGameWorld67.resolve secretKey
      (SecurityBudget.cutoff program budget) =
    Prod.fst <$>
      GroupedBalancedGraphViewWorld67.cutoffWithRemaining
        (GroupedBalancedGameWorld67.resolve secretKey program) budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => rfl
  | query_bind query next ih =>
      cases query with
      | inl n =>
          rw [SecurityBudget.cutoff_query_bind]
          rw [if_pos (by simp [SecurityBudget.charge])]
          simp only [SecurityBudget.charge, Nat.sub_zero,
            GroupedBalancedGameWorld67.resolve,
            simulateQ_bind, simulateQ_spec_query]
          change (GroupedBalancedGameWorld67.translate secretKey (.inl n) >>= fun answer =>
            GroupedBalancedGameWorld67.resolve secretKey
              (SecurityBudget.cutoff (next answer) budget)) =
            Prod.fst <$>
              GroupedBalancedGraphViewWorld67.cutoffWithRemaining
                (GroupedBalancedGameWorld67.translate secretKey (.inl n) >>= fun answer =>
                  GroupedBalancedGameWorld67.resolve secretKey (next answer)) budget
          change (liftM (World.query (.inl n)) >>= fun answer =>
            GroupedBalancedGameWorld67.resolve secretKey
              (SecurityBudget.cutoff (next answer) budget)) =
            Prod.fst <$>
              GroupedBalancedGraphViewWorld67.cutoffWithRemaining
                (liftM (World.query (.inl n)) >>= fun answer =>
                  GroupedBalancedGameWorld67.resolve secretKey (next answer)) budget
          rw [GroupedBalancedGraphViewWorld67.cutoff_query_bind]
          simp only [GroupedBalancedGraphViewWorld67.hashCharge,
            Nat.zero_le, if_pos, Nat.sub_zero, map_bind]
          apply bind_congr
          intro answer
          exact ih answer budget
      | inr query =>
          cases query with
          | inl slot =>
              cases budget with
              | zero =>
                  rw [SecurityBudget.cutoff_query_bind]
                  rw [if_neg (by simp [SecurityBudget.charge])]
                  simp only [GroupedBalancedGameWorld67.resolve,
                    simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
                  change (pure none : OracleComp World (Option α)) =
                    Prod.fst <$>
                      GroupedBalancedGraphViewWorld67.cutoffWithRemaining
                        (GroupedBalancedGameWorld67.translate secretKey
                          (.inr (.inl slot)) >>= fun answer =>
                          GroupedBalancedGameWorld67.resolve secretKey (next answer)) 0
                  change (pure none : OracleComp World (Option α)) =
                    Prod.fst <$>
                      GroupedBalancedGraphViewWorld67.cutoffWithRemaining
                        (liftM (World.query
                          (.inr (SecurityDerivation.input secretKey slot))) >>= fun answer =>
                          GroupedBalancedGameWorld67.resolve secretKey (next answer)) 0
                  rw [GroupedBalancedGraphViewWorld67.cutoff_query_bind]
                  simp [GroupedBalancedGraphViewWorld67.hashCharge]
              | succ budget =>
                  rw [SecurityBudget.cutoff_query_bind]
                  rw [if_pos (by simp [SecurityBudget.charge])]
                  simp only [SecurityBudget.charge,
                    Nat.add_sub_cancel_right,
                    GroupedBalancedGameWorld67.resolve,
                    simulateQ_bind, simulateQ_spec_query]
                  change (GroupedBalancedGameWorld67.translate secretKey
                    (.inr (.inl slot)) >>= fun answer =>
                    GroupedBalancedGameWorld67.resolve secretKey
                      (SecurityBudget.cutoff (next answer) budget)) =
                    Prod.fst <$>
                      GroupedBalancedGraphViewWorld67.cutoffWithRemaining
                        (GroupedBalancedGameWorld67.translate secretKey
                          (.inr (.inl slot)) >>= fun answer =>
                          GroupedBalancedGameWorld67.resolve secretKey (next answer))
                        (budget + 1)
                  change (liftM (World.query
                    (.inr (SecurityDerivation.input secretKey slot))) >>= fun answer =>
                    GroupedBalancedGameWorld67.resolve secretKey
                      (SecurityBudget.cutoff (next answer) budget)) =
                    Prod.fst <$>
                      GroupedBalancedGraphViewWorld67.cutoffWithRemaining
                        (liftM (World.query
                          (.inr (SecurityDerivation.input secretKey slot))) >>= fun answer =>
                          GroupedBalancedGameWorld67.resolve secretKey (next answer))
                        (budget + 1)
                  rw [GroupedBalancedGraphViewWorld67.cutoff_query_bind]
                  rw [if_pos (by simp [GroupedBalancedGraphViewWorld67.hashCharge])]
                  simp only [GroupedBalancedGraphViewWorld67.hashCharge,
                    Nat.add_sub_cancel_right, map_bind]
                  apply bind_congr
                  intro answer
                  exact ih answer budget
          | inr input =>
              cases budget with
              | zero =>
                  rw [SecurityBudget.cutoff_query_bind]
                  rw [if_neg (by simp [SecurityBudget.charge])]
                  simp only [GroupedBalancedGameWorld67.resolve,
                    simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
                  change (pure none : OracleComp World (Option α)) =
                    Prod.fst <$>
                      GroupedBalancedGraphViewWorld67.cutoffWithRemaining
                        (GroupedBalancedGameWorld67.translate secretKey
                          (.inr (.inr input)) >>= fun answer =>
                          GroupedBalancedGameWorld67.resolve secretKey (next answer)) 0
                  change (pure none : OracleComp World (Option α)) =
                    Prod.fst <$>
                      GroupedBalancedGraphViewWorld67.cutoffWithRemaining
                        (liftM (World.query
                          (.inr (input))) >>= fun answer =>
                          GroupedBalancedGameWorld67.resolve secretKey (next answer)) 0
                  rw [GroupedBalancedGraphViewWorld67.cutoff_query_bind]
                  simp [GroupedBalancedGraphViewWorld67.hashCharge]
              | succ budget =>
                  rw [SecurityBudget.cutoff_query_bind]
                  rw [if_pos (by simp [SecurityBudget.charge])]
                  simp only [SecurityBudget.charge,
                    Nat.add_sub_cancel_right,
                    GroupedBalancedGameWorld67.resolve,
                    simulateQ_bind, simulateQ_spec_query]
                  change (GroupedBalancedGameWorld67.translate secretKey
                    (.inr (.inr input)) >>= fun answer =>
                    GroupedBalancedGameWorld67.resolve secretKey
                      (SecurityBudget.cutoff (next answer) budget)) =
                    Prod.fst <$>
                      GroupedBalancedGraphViewWorld67.cutoffWithRemaining
                        (GroupedBalancedGameWorld67.translate secretKey
                          (.inr (.inr input)) >>= fun answer =>
                          GroupedBalancedGameWorld67.resolve secretKey (next answer))
                        (budget + 1)
                  change (liftM (World.query
                    (.inr (input))) >>= fun answer =>
                    GroupedBalancedGameWorld67.resolve secretKey
                      (SecurityBudget.cutoff (next answer) budget)) =
                    Prod.fst <$>
                      GroupedBalancedGraphViewWorld67.cutoffWithRemaining
                        (liftM (World.query
                          (.inr (input))) >>= fun answer =>
                          GroupedBalancedGameWorld67.resolve secretKey (next answer))
                        (budget + 1)
                  rw [GroupedBalancedGraphViewWorld67.cutoff_query_bind]
                  rw [if_pos (by simp [GroupedBalancedGraphViewWorld67.hashCharge])]
                  simp only [GroupedBalancedGraphViewWorld67.hashCharge,
                    Nat.add_sub_cancel_right, map_bind]
                  apply bind_congr
                  intro answer
                  exact ih answer budget

private abbrev submission := GroupedBalancedProgram67ByteSign.submission

theorem per_table (table : GroupedBalancedGraphPassive67.PointTable)
    (secretKey : SecretKey) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) (cache : QueryCache HashSpec) :
    Pr[fun result : AttackResult => result.won = true ∧ result.hashCalls ≤ budget |
      SecurityGraphHidden.observe
        (gameWith (fullInterface table) adversary rounds secretKey) cache] ≤
    Pr[fun result : Option (GroupedBalancedGraphOrganizerView67.Result submission.sizes) =>
      ∃ value, result = some value ∧ value.won = true |
      SecurityGraphHidden.observe
        (GroupedBalancedGameWorld67.resolve secretKey
          (SecurityBudget.cutoff
            (GroupedBalancedGameWorldBudget67.organizerProgram
              submission.sizes GroupedBalancedWire67.wire
              GroupedBalancedWire67.decode GroupedBalancedWire67.decode
              adversary (0 : Cache) rounds table) budget)) cache] := by
  let pk := GroupedBalancedGraphMonitorSetupBound67.rootPublic table
  let paired := pairInteract table secretKey pk adversary rounds
    (adversary.initial pk (0 : Cache)) {} { hashCalls := 3983 }
  have official_program :
      gameWith (fullInterface table) adversary rounds secretKey =
        Prod.snd <$> paired := by
    simp only [gameWith, fullInterface,
      GroupedBalancedSecurityOfficialHybrid67.tableInterface,
      OracleComp.liftComp_pure,pure_bind]
    exact (pair_official table secretKey pk adversary rounds
      (adversary.initial pk (0 : Cache)) {} {hashCalls := 3983} rfl).symm
  have graph_program :
      GroupedBalancedGameWorld67.resolve secretKey
        (SecurityBudget.counted
          (GroupedBalancedGameWorldBudget67.organizerProgram
            submission.sizes GroupedBalancedWire67.wire
            GroupedBalancedWire67.decode GroupedBalancedWire67.decode
            adversary (0 : Cache) rounds table)) =
        Prod.fst <$> paired := by
    simp only [GroupedBalancedGameWorldBudget67.organizerProgram,
      GroupedBalancedGraphMonitorSetupBound67.rootFrom_cache]
    exact (pair_graph table secretKey pk adversary rounds
      (adversary.initial pk (0 : Cache)) {} {hashCalls := 3983}).symm
  have official_eq :
      Pr[fun result : AttackResult => result.won = true ∧ result.hashCalls ≤ budget |
        SecurityGraphHidden.observe
          (gameWith (fullInterface table) adversary rounds secretKey) cache] =
      Pr[fun result : JointResult => result.2.won = true ∧
        result.2.hashCalls ≤ budget |
        SecurityGraphHidden.observe paired cache] := by
    rw [official_program]
    simp only [SecurityGraphHidden.observe, simulateQ_map,
      StateT.run'_eq, StateT.run_map, Functor.map_map,
      probEvent_map, Function.comp_def]
  have graph_eq :
      Pr[fun result : GroupedBalancedGraphOrganizerView67.Result submission.sizes × Nat =>
        result.1.won = true ∧ result.2 ≤ budget |
        SecurityGraphHidden.observe
          (GroupedBalancedGameWorld67.resolve secretKey
            (SecurityBudget.counted
              (GroupedBalancedGameWorldBudget67.organizerProgram
                submission.sizes GroupedBalancedWire67.wire
                GroupedBalancedWire67.decode GroupedBalancedWire67.decode
                adversary (0 : Cache) rounds table))) cache] =
      Pr[fun result : JointResult => result.1.1.won = true ∧
        result.1.2 ≤ budget |
        SecurityGraphHidden.observe paired cache] := by
    rw [graph_program]
    simp only [SecurityGraphHidden.observe, simulateQ_map,
      StateT.run'_eq, StateT.run_map, Functor.map_map,
      probEvent_map, Function.comp_def]
  have cutoff_eq := SecurityBudget.prob_cutoff_eq_counted
    (SecurityGameHop.realGameOracle secretKey)
    (GroupedBalancedGameWorldBudget67.organizerProgram
      submission.sizes GroupedBalancedWire67.wire
      GroupedBalancedWire67.decode GroupedBalancedWire67.decode
      adversary (0 : Cache) rounds table) cache budget
    (fun result => result.won = true)
  rw [simulate_real_resolve, simulate_real_resolve] at cutoff_eq
  rw [official_eq]
  simp only [SecurityGraphHidden.observe] at graph_eq ⊢
  rw [cutoff_eq, graph_eq]
  apply probEvent_mono
  intro result member winning
  have relation := pair_le_observed SecurityCache.implementation cache
    table secretKey pk adversary rounds
    (adversary.initial pk (0 : Cache)) {} { hashCalls := 3983 }
    result rfl rfl member
  exact ⟨relation.1 ▸ winning.1, by omega⟩

#print axioms per_table

theorem official_bounded_le_joint_cutoff
    (refinement : GroupedBalancedSecurityCheckConditional67.VerifierRefinement)
    (adversary : Adversary submission.sizes)
    (rounds budget : Nat) :
    Pr[fun result : AttackResult => result.won = true ∧ result.hashCalls ≤ budget |
      submission.securityExperiment adversary rounds] ≤
    Pr[fun result : Option (GroupedBalancedGraphOrganizerView67.Result submission.sizes) =>
      ∃ value, result = some value ∧ value.won = true |
      jointProgram (fun secretKey table =>
        GroupedBalancedGameWorld67.resolve secretKey
          (SecurityBudget.cutoff
            (GroupedBalancedGameWorldBudget67.organizerProgram
              submission.sizes GroupedBalancedWire67.wire
              GroupedBalancedWire67.decode GroupedBalancedWire67.decode
              adversary (0 : Cache) rounds table) budget))] := by
  have same := official_full_joint refinement adversary rounds
  have eqProb :
      Pr[fun result : AttackResult => result.won = true ∧ result.hashCalls ≤ budget |
        submission.securityExperiment adversary rounds] =
      Pr[fun result : AttackResult => result.won = true ∧ result.hashCalls ≤ budget |
        jointFull adversary rounds] :=
    probEvent_congr' (fun _ _ => Iff.rfl) same
  rw [eqProb]
  unfold jointFull jointProgram
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
  exact per_table (GroupedBalancedSecurityJointTable67.tableOf
    answers labels ghosts) secretKey adversary rounds budget
    (jointCache secretKey answers labels)

#print axioms official_bounded_le_joint_cutoff

#print axioms avoids_countHash
#print axioms verify_avoids
#print axioms countHash_verify_source_free
#print axioms semanticCheck_source_free
#print axioms monitorInteract_eq_stopBefore
#print axioms monitorGame_eq_stopBefore
#print axioms monitor_none_le_secretKey_trace
#print axioms stopped_eq_source_trace
#print axioms traceHashes_map
#print axioms stopBefore_map
#print axioms cutoffWithRemaining_map
#print axioms budget_cutoff_map
#print axioms cutoff_counted_fst
#print axioms resolve_cutoff
#print axioms stopped_risk_le_source_trace
#print axioms official_le_full_trace_risk
#print axioms covered_counted
#print axioms covered_gameView
#print axioms covered_cutoff
#print axioms source_stop_le
#print axioms simulate_real_resolve
#print axioms source_stop_le_secret_trace
#print axioms source_union_any
#print axioms joint_le_planted_stopped
#print axioms joint_le_planted_real_trace
#print axioms joint_graph_cutoff_le_planted_trace

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityVerifyAvoids67
