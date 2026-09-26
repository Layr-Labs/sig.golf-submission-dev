import SigGolfCandidate.Hypertree.SecuritySecretKey
import SigGolfCandidate.Hypertree.SecurityGraphExtraction
import SigGolfCandidate.Hypertree.SecurityVerifyCost

/-! Inlined from SigGolfCandidate.Hypertree.SecurityTrace; its only importer was SigGolfCandidate.Hypertree.SecurityVerifyTrace. -/
section
namespace SigGolfCandidate.Hypertree.SecurityTrace
open SigGolf OracleComp OracleSpec SecurityCache SecuritySecretKey
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Record hash inputs only, exactly the resource counted by the security game.
Private uniform queries are deliberately omitted from this log. -/
def prependHash (input : World.Domain) (inputs : List Query) : List Query :=
  match input with
  | .inl _ => inputs
  | .inr input => input :: inputs

noncomputable def traceHashes {α : Type} (computation : OracleComp World α) :
    OracleComp World (α × List Query) :=
  OracleComp.construct (fun value => pure (value, []))
    (fun input _ next => do
      let answer ← liftM (World.query input)
      let result ← next answer
      return (result.1, prependHash input result.2)) computation

@[simp] theorem traceHashes_pure {α : Type} (value : α) :
    traceHashes (pure value) = pure (value, []) := rfl

theorem traceHashes_query_bind {α : Type} (input : World.Domain)
    (next : World.Range input → OracleComp World α) :
    traceHashes (liftM (World.query input) >>= next) = (do
      let answer ← liftM (World.query input)
      let result ← traceHashes (next answer)
      return (result.1, prependHash input result.2)) := rfl

/-- Instrumentation preserves the exact adaptive computation. -/
theorem traceHashes_fst {α : Type} (computation : OracleComp World α) :
    Prod.fst <$> traceHashes computation = computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
    rw [traceHashes_query_bind]
    simp only [map_bind, bind_pure_comp]
    apply bind_congr
    intro answer
    simpa only [Functor.map_map, Function.comp_def] using ih answer

def TraceHits (bad : Query → Prop) (inputs : List Query) : Prop :=
  ∃ input ∈ inputs, bad input

theorem traceHits_prepend (bad : Query → Prop) (input : World.Domain) (inputs : List Query) :
    TraceHits bad (prependHash input inputs) ↔ hashBad bad input ∨ TraceHits bad inputs := by
  cases input <;> simp [TraceHits, prependHash, hashBad]

/-- The stopping probability equals the event in the unmodified adaptive query log. -/
theorem prob_stop_eq_traceHits {α : Type} (bad : Query → Prop) [DecidablePred bad]
    (computation : OracleComp World α) (cache : QueryCache HashSpec) :
    Pr[= none | (simulateQ implementation (stopBefore bad computation)).run' cache] =
      Pr[fun result => TraceHits bad result.2 |
        (simulateQ implementation (traceHashes computation)).run' cache] := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [TraceHits]
  | query_bind input next ih =>
    rw [stopBefore_query_bind, traceHashes_query_bind]
    by_cases hit : hashBad bad input
    · rw [if_pos hit, run'_query_bind]
      simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
        Functor.map_map, probEvent_map, Function.comp_def, traceHits_prepend, hit, true_or,
        probEvent_const, NeverFail.probFailure_eq_zero, tsub_zero,
        simulateQ_pure, StateT.run_pure, map_pure, probOutput_pure, ite_true,
        probEvent_bind_of_const, one_mul]
    · rw [if_neg hit, run'_query_bind, run'_query_bind]
      simp only [probOutput_bind_eq_tsum, probEvent_bind_eq_tsum]
      apply tsum_congr
      intro result
      rw [ih result.1 result.2]
      simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
        Functor.map_map, probEvent_map, Function.comp_def, traceHits_prepend, hit, false_or]

/-- The bound is on the actual shared-RO trace from the replacement cache. -/
def HashTraceBound {α : Type} (computation : OracleComp World α)
    (cache : QueryCache HashSpec) (limit : Nat) : Prop :=
  ∀ result ∈ support ((simulateQ implementation (traceHashes computation)).run' cache),
    result.2.length ≤ limit

/-- Adaptive hash queries in a secret key-independent replacement world guess the secret key
with probability at most Q/2^128. The computation may use unlimited private coins. -/
theorem prob_stop_secretKey_le {α : Type} (computation : OracleComp World α)
    (cache : QueryCache HashSpec) (limit : Nat) (bounded : HashTraceBound computation cache limit) :
    Pr[= none | sampleSecretKey >>= fun secretKey =>
      (simulateQ implementation (stopBefore (SecretKeyAt · secretKey) computation)).run' cache] ≤
        limit / (2 : ENNReal) ^ 128 := by
  classical
  let trace := (simulateQ implementation (traceHashes computation)).run' cache
  calc
    _ = Pr[= true | sampleSecretKey >>= fun secretKey =>
        (fun result => decide (SecretKeyHitTrace result.2 secretKey)) <$> trace] := by
      simp only [probOutput_bind_eq_tsum, prob_stop_eq_traceHits, probOutput_map,
        decide_eq_true_eq]
      rfl
    _ = Pr[= true | trace >>= fun result =>
        (fun secretKey => decide (SecretKeyHitTrace result.2 secretKey)) <$> sampleSecretKey] := by
      simp only [← bind_pure_comp]
      exact probOutput_bind_bind_swap _ _ _ _
    _ ≤ _ := by
      rw [← probEvent_eq_eq_probOutput]
      apply probEvent_bind_le_of_forall_le
      intro result hr
      simp only [probEvent_map, Function.comp_def, decide_eq_true_eq]
      exact (prob_secretKeyHitTrace_le result.2).trans
        (ENNReal.div_le_div (by exact_mod_cast bounded result hr) le_rfl)

/-- Erasing secret key-dependent cache entries from an independent reference world costs
at most Q/2^128. The dependence and query-bound obligations are explicit; this is
one game-hop lemma, not the full hypertree security certificate. -/
theorem prob_secretKey_cache_change_le {α : Type} (computation : OracleComp World α)
    (initial : SecretKey → QueryCache HashSpec) (cache : QueryCache HashSpec)
    (agree : ∀ secretKey, AgreeOutside (SecretKeyAt · secretKey) (initial secretKey) cache)
    (limit : Nat) (bounded : HashTraceBound computation cache limit) (event : α → Prop) :
    Pr[event | sampleSecretKey >>= fun secretKey =>
      (simulateQ implementation computation).run' (initial secretKey)] ≤
      Pr[event | (simulateQ implementation computation).run' cache] + limit / (2 : ENNReal) ^ 128 := by
  classical
  let stopped := fun secretKey =>
    (simulateQ implementation (stopBefore (SecretKeyAt · secretKey) computation)).run' cache
  calc
    _ ≤ Pr[event | sampleSecretKey >>= fun _ =>
        (simulateQ implementation computation).run' cache] + Pr[= none | sampleSecretKey >>= stopped] := by
      simp only [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum fun secretKey =>
        (mul_le_mul' le_rfl (prob_cache_change_le (SecretKeyAt · secretKey)
          computation (initial secretKey) cache (agree secretKey) event)).trans_eq (mul_add ..)
    _ ≤ _ := by
      simpa [stopped] using add_le_add
        (le_refl (Pr[event | (simulateQ implementation computation).run' cache]))
        (prob_stop_secretKey_le computation cache limit bounded)

end SigGolfCandidate.Hypertree.SecurityTrace

end

namespace SigGolfCandidate.Hypertree.SecurityVerifyTrace
open SigGolf OracleComp OracleSpec Reference SecurityRandomOracle
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Exact deterministic hash-input trace, including repeated and cached queries.
Answers are the values of the same total oracle controlling execution. -/
def queries {α : Type} (hash : Hash) (program : OracleComp HashSpec α) : List Query :=
  OracleComp.construct (fun _ => []) (fun input _ next => input :: next (hash input)) program

@[simp] theorem queries_pure {α : Type} (hash : Hash) (value : α) : queries hash (pure value) = [] := rfl

theorem queries_query_bind {α : Type} (hash : Hash) (input : Query)
    (next : BitVec 256 → OracleComp HashSpec α) :
    queries hash (liftM (HashSpec.query input) >>= next) = input :: queries hash (next (hash input)) := rfl

theorem queries_bind {α β : Type} (hash : Hash) (program : OracleComp HashSpec α)
    (next : α → OracleComp HashSpec β) :
    queries hash (program >>= next) = queries hash program ++ queries hash (next (evalWithAnswerFn hash program)) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input continuation ih =>
    simp only [bind_assoc, queries_query_bind, evalWithAnswerFn_bind]
    change input :: queries hash (continuation (hash input) >>= next) =
      (input :: queries hash (continuation (hash input))) ++
        queries hash (next (evalWithAnswerFn hash (continuation (hash input))))
    rw [ih]
    rfl

@[simp] theorem queries_map {α β : Type} (hash : Hash) (f : α → β) (program : OracleComp HashSpec α) :
    queries hash (f <$> program) = queries hash program := by
  rw [map_eq_pure_bind, queries_bind]
  simp

theorem queries_length {α : Type} (hash : Hash) (program : OracleComp HashSpec α) :
    (queries hash program).length = SecurityVerifyCost.calls hash program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
    rw [queries_query_bind, List.length_cons, SecurityVerifyCost.calls_query_bind, ih]

@[simp] theorem queries_ask (hash : Hash) (tag level tree leaf chain step : Nat) (payload : List Byte) :
    queries hash (SecurityReference.ask tag level tree leaf chain step payload) =
      [addressedInput tag level tree leaf chain step payload] := rfl

@[simp] theorem queries_chainHash (hash : Hash) (level tree : Nat) (side : Bool)
    (chain : Chain) (step : Nat) (value : Digest) :
    queries hash (SecurityReference.chainHash level tree side chain step value) =
      [addressedInput 2 level tree (sideNumber side) chain.val step (bytes value)] := by
  simp [SecurityReference.chainHash]

@[simp] theorem queries_compressLeaf (hash : Hash) (level tree : Nat) (side : Bool) (values : Chain → Digest) :
    queries hash (SecurityReference.compressLeaf level tree side values) =
      [addressedInput 3 level tree (sideNumber side) 0 0 ((List.ofFn values).flatMap bytes)] := by
  simp [SecurityReference.compressLeaf]

@[simp] theorem queries_node (hash : Hash) (level tree : Nat) (left right : Digest) :
    queries hash (SecurityReference.node level tree left right) =
      [addressedInput 4 level tree 0 0 0 (bytes left ++ bytes right)] := by
  simp [SecurityReference.node]

theorem mem_sequenceFin {α : Type} (hash : Hash) (n : Nat) (body : Fin n → OracleComp HashSpec α)
    (i : Fin n) (query : Query) (member : query ∈ queries hash (body i)) :
    query ∈ queries hash (SecurityReference.sequenceFin n body) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp only [SecurityReference.sequenceFin, queries_bind, queries_pure, List.append_nil, List.mem_append]
    refine Fin.cases ?_ (fun j => ?_) i member
    · exact fun h => Or.inl h
    · exact fun h => Or.inr (ih (fun j => body j.succ) j h)

/-- The exact intermediate chain input occurs at every executed suffix offset. -/
theorem mem_walk (hash : Hash) (level tree : Nat) (side : Bool) (chain : Chain)
    (start count offset : Nat) (value : Digest) (within : offset < count) :
    addressedInput 2 level tree (sideNumber side) chain.val (start + offset)
      (bytes (Hypertree.walk (chainHash hash level tree side chain) start offset value)) ∈
    queries hash (SecurityReference.walk (SecurityReference.chainHash level tree side chain) start count value) := by
  induction count generalizing start offset value with
  | zero => omega
  | succ count ih =>
    simp only [SecurityReference.walk, queries_bind, queries_chainHash, SecurityReference.eval_chainHash,
      List.mem_append, List.mem_singleton]
    cases offset with
    | zero => exact Or.inl (by simp [Hypertree.walk])
    | succ offset =>
      right
      simpa only [Hypertree.walk, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (start + 1) offset (chainHash hash level tree side chain start value) (by omega)

theorem mem_recoverLeaf_bottom (hash : Hash) (tree : Nat) (side : Bool)
    (message : Digest) (signature : LayerSignature) :
    addressedInput 2 0 tree (sideNumber side) 0 0 (bytes (signature.values 0)) ∈
      queries hash (SecurityVerify.recoverLeaf 0 tree side message signature) := by
  simp [SecurityVerify.recoverLeaf]

theorem mem_recoverLeaf_compress (hash : Hash) (level tree : Nat) (side : Bool)
    (message : Digest) (signature : LayerSignature) (upper : level ≠ 0) :
    addressedInput 3 level tree (sideNumber side) 0 0
      ((List.ofFn fun chain => Hypertree.walk (chainHash hash level tree side chain) (digit message chain).val
        (7 - (digit message chain).val) (signature.values chain)).flatMap bytes) ∈
      queries hash (SecurityVerify.recoverLeaf level tree side message signature) := by
  simp only [SecurityVerify.recoverLeaf, upper, if_false, queries_bind,
    SecurityReference.eval_sequenceFin, SecurityReference.eval_walk, SecurityReference.eval_chainHash,
    queries_compressLeaf, List.mem_append, List.mem_singleton, or_true]

theorem mem_recoverLeaf_chain (hash : Hash) (level tree : Nat) (side : Bool)
    (message : Digest) (signature : LayerSignature) (upper : level ≠ 0) (chain : Chain)
    (offset : Nat) (within : offset < 7 - (digit message chain).val) :
    addressedInput 2 level tree (sideNumber side) chain.val ((digit message chain).val + offset)
      (bytes (Hypertree.walk (chainHash hash level tree side chain) (digit message chain).val offset
        (signature.values chain))) ∈ queries hash (SecurityVerify.recoverLeaf level tree side message signature) := by
  simp only [SecurityVerify.recoverLeaf, upper, if_false, queries_bind, List.mem_append]
  exact Or.inl (mem_sequenceFin hash 46 _ chain _ (mem_walk hash level tree side chain _ _ offset _ within))

theorem mem_recoverLayer_leaf (hash : Hash) (level tree : Nat) (side : Bool)
    (message : Digest) (signature : LayerSignature) (query : Query)
    (member : query ∈ queries hash (SecurityVerify.recoverLeaf level tree side message signature)) :
    query ∈ queries hash (SecurityVerify.recoverLayer level tree side message signature) := by
  simp only [SecurityVerify.recoverLayer, queries_bind, List.mem_append]
  exact Or.inl member

theorem mem_recoverLayer_node (hash : Hash) (level tree : Nat) (side : Bool)
    (message : Digest) (signature : LayerSignature) :
    addressedInput 4 level tree 0 0 0
      (if side then bytes signature.sibling ++ bytes (recoverLeaf hash level tree side message signature)
        else bytes (recoverLeaf hash level tree side message signature) ++ bytes signature.sibling) ∈
      queries hash (SecurityVerify.recoverLayer level tree side message signature) := by
  cases side <;> simp [SecurityVerify.recoverLayer, queries_bind]

/-- The deterministic list is exactly the existing oracle instrumentation,
including its unchanged returned value. Public answers are shared, not resampled. -/
theorem traceHashes_lift {α : Type} (hash : Hash) (answers : QueryImpl World Id)
    (agree : ∀ input, answers (.inr input) = hash input) (program : OracleComp HashSpec α) :
    evalWithAnswerFn answers (SecurityTrace.traceHashes (program.liftComp World)) =
      (evalWithAnswerFn hash program, queries hash program) := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
    have lifted : (liftM (HashSpec.query input) >>= next).liftComp World =
        (do let answer ← liftM (World.query (.inr input))
            (next answer).liftComp World) := by
      rw [OracleComp.liftComp_bind]
      rfl
    rw [lifted, SecurityTrace.traceHashes_query_bind]
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, queries_query_bind]
    have queried : evalWithAnswerFn answers (liftM (World.query (.inr input))) = hash input := agree input
    rw [queried, ih]
    rfl

end SigGolfCandidate.Hypertree.SecurityVerifyTrace
