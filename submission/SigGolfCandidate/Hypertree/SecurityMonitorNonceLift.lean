import SigGolfCandidate.Hypertree.SecurityNonceMonitorCost
import SigGolfCandidate.Hypertree.SecurityMonitorGraphView

/-! Inlined from SigGolfCandidate.Hypertree.SecurityNonceProgram; its only importer was SigGolfCandidate.Hypertree.SecurityMonitorNonceLift. -/
section
namespace SigGolfCandidate.Hypertree.SecurityNonceProgram
open SigGolf OracleComp OracleSpec OracleComp.EvalDist SecurityGraphFactor
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Output-retaining passive nonce syntax. The accumulated success flag and
prereveal count are unavailable to the continuation. -/
inductive Program (α : Type) where
  | pure (value : α)
  | reveal (message : Message) (next : BitVec 256 → Program α)
  | guess (message : Message) (nonce : BitVec 256) (next : Program α)
  | coin (n : Nat) (next : Fin (n + 1) → Program α)
  | bits (next : BitVec 256 → Program α)

def erase {α : Type} : Program α → SecurityNonceMonitor.Strategy
  | .pure _ => .done
  | .reveal message next => .reveal message (fun nonce => erase (next nonce))
  | .guess message nonce next => .guess message nonce (erase next)
  | .coin n next => .coin n (fun value => erase (next value))
  | .bits next => .bits (fun value => erase (next value))

structure Outcome (α : Type) where
  value : α
  bad : Bool
  guesses : Nat

def Outcome.monitor {α : Type} (result : Outcome α) : Bool × Nat := (result.bad, result.guesses)

def addGuess {α : Type} (hidden hit : Bool) (result : Outcome α) : Outcome α :=
  ⟨result.value, (hidden && hit) || result.bad, (if hidden then 1 else 0) + result.guesses⟩

noncomputable def run {α : Type} (table : NonceTable) :
    SecurityNonceMonitor.NonceCache → Program α → ProbComp (Outcome α)
  | _, .pure value => pure ⟨value, false, 0⟩
  | cache, .reveal message next => run table (cache.cacheQuery message (table message)) (next (table message))
  | cache, .guess message nonce next =>
      addGuess (decide (cache message = none)) (decide (table message = nonce)) <$> run table cache next
  | cache, .coin n next => do
      let answer ← $ᵗ Fin (n + 1)
      run table cache (next answer)
  | cache, .bits next => do
      let answer ← $ᵗ BitVec 256
      run table cache (next answer)

/-- The exact joint flag/count projection is the existing nonce monitor; the
relation preserves their correlation, not just their separate marginals. -/
theorem run_projection {α : Type} (table : NonceTable) (cache : SecurityNonceMonitor.NonceCache)
    (program : Program α) :
    Outcome.monitor <$> run table cache program = SecurityNonceMonitor.play table cache (erase program) := by
  induction program generalizing cache with
  | pure value => rfl
  | reveal message next ih => exact ih (table message) _
  | coin n next ih | bits next ih =>
    simp only [run, erase, SecurityNonceMonitor.play, map_bind, ih]
  | guess message nonce next ih =>
    simp only [run, erase, SecurityNonceMonitor.play, ← ih cache]
    simp only [map_eq_pure_bind, bind_assoc, pure_bind, addGuess, Outcome.monitor,
      Bool.decide_and, decide_eq_true_eq]

noncomputable def execute {α : Type} (program : Program α) (cache : SecurityNonceMonitor.NonceCache) :
    ProbComp (Outcome α) := do
  let table ← $ᵗ NonceTable
  run (SecurityNonceMonitor.complete cache table) cache program

/-- Exact output-forgetting law for eager uniform nonce-table sampling. -/
theorem execute_projection {α : Type} (program : Program α) (cache : SecurityNonceMonitor.NonceCache) :
    Outcome.monitor <$> execute program cache = SecurityNonceMonitor.experiment (erase program) cache := by
  simp only [execute, SecurityNonceMonitor.experiment, map_bind, run_projection]

/-- Retaining final attacker outputs and charged counters does not change the
passive nonce bound, which charges only the expected prereveal guess count. -/
theorem prob_bad_le_expected {α : Type} (program : Program α) (cache : SecurityNonceMonitor.NonceCache) :
    Pr[fun result => result.bad = true | execute program cache] ≤
      expectedValue (execute program cache) (fun result => (result.guesses : ENNReal)) / (2 : ENNReal)^256 := by
  have bound := SecurityNonceMonitor.risk_le_expected (erase program) cache
  rw [← execute_projection, probEvent_map, expectedValue_map] at bound
  exact bound

/-- The sampled counter is exactly the nonce monitor's deferred-sampling cost. -/
theorem expected_guesses {α : Type} (program : Program α) (cache : SecurityNonceMonitor.NonceCache) :
    expectedValue (execute program cache) (fun result => (result.guesses : ENNReal)) =
      SecurityNonceMonitor.cost cache (erase program) := by
  have same := SecurityNonceMonitor.expected_guesses (erase program) cache
  rw [← execute_projection, expectedValue_map] at same
  exact same

/-- The same joint-output estimate survives an arbitrary randomized initial view. -/
theorem mixed_prob_bad_le_expected {α β : Type} (draw : ProbComp β) (program : β → Program α)
    (cache : β → SecurityNonceMonitor.NonceCache) :
    Pr[fun result => result.bad = true | (do let view ← draw; execute (program view) (cache view))] ≤
      expectedValue (do let view ← draw; execute (program view) (cache view))
        (fun result => (result.guesses : ENNReal)) / (2 : ENNReal)^256 := by
  rw [probEvent_bind_eq_expectedValue, expectedValue_bind]
  calc
    _ ≤ expectedValue draw (fun view => expectedValue (execute (program view) (cache view))
        (fun result => (result.guesses : ENNReal)) / (2 : ENNReal)^256) :=
      expectedValue_mono _ (fun view => prob_bad_le_expected (program view) (cache view))
    _ = _ := by simp only [div_eq_mul_inv, expectedValue_mul_const]

end SigGolfCandidate.Hypertree.SecurityNonceProgram

end

namespace SigGolfCandidate.Hypertree.SecurityMonitorNonceLift
open SigGolf OracleComp OracleSpec Reference SecurityGraphPassive SecurityGraphFactor
  SecurityGraphMonitorProgram
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev NP := SecurityNonceProgram.Program
abbrev NO := SecurityNonceProgram.Outcome

/-- Translate a graph operation with its full passive outcome retained. The
fixed graph table is independent of the nonce table; no nonce is read here. -/
noncomputable def liftGraph {α β : Type} (points : PointTable) :
    QueryCache PointSpec → Program α → (Outcome α → NP β) → NP β
  | _, .done value, next => next ⟨value, false, 0⟩
  | cache, .reveal point continuation, next =>
      liftGraph points (cache.cacheQuery point (points point)) (continuation (points point)) next
  | cache, .guess point value continuation, next =>
      liftGraph points cache continuation (fun result =>
        next (addTest (decide (cache point = none ∧ truncate (points point) = value)) result))
  | cache, .coin n continuation, next => .coin n (fun answer =>
      liftGraph points cache (continuation answer) next)
  | cache, .bits continuation, next => .bits (fun answer =>
      liftGraph points cache (continuation answer) next)
  | cache, .collision target continuation, next => .bits (fun answer =>
      liftGraph points cache (continuation answer) (fun result =>
        next (addTest (decide (truncate answer = target)) result)))

/-- Exact joint law, including any nonce flags/counters generated by the
continuation and all graph flags/counters passed to it. -/
theorem run_liftGraph {α β : Type} (points : PointTable) (nonces : NonceTable)
    (exposed : QueryCache PointSpec) (nonceCache : SecurityNonceMonitor.NonceCache)
    (program : Program α) (next : Outcome α → NP β) :
    SecurityNonceProgram.run nonces nonceCache (liftGraph points exposed program next) =
      (run points exposed program >>= fun result => SecurityNonceProgram.run nonces nonceCache (next result)) := by
  induction program generalizing exposed next with
  | done value => simp only [liftGraph, run, pure_bind]
  | reveal point continuation ih => exact ih (points point) _ _
  | guess point value continuation ih =>
    simp only [liftGraph, run, bind_map_left]
    exact ih exposed _
  | coin n continuation ih | bits continuation ih =>
    simp only [liftGraph, run, SecurityNonceProgram.run, bind_assoc]
    apply bind_congr
    intro answer
    exact ih answer exposed _
  | collision target continuation ih =>
    simp only [liftGraph, run, SecurityNonceProgram.run, bind_assoc, bind_map_left]
    apply bind_congr
    intro answer
    exact ih answer exposed _

/-- Map only the retained value, leaving the passive nonce state untouched. -/
def map {α β : Type} (f : α → β) : NP α → NP β
  | .pure value => .pure (f value)
  | .reveal message next => .reveal message (fun answer => map f (next answer))
  | .guess message nonce next => .guess message nonce (map f next)
  | .coin n next => .coin n (fun answer => map f (next answer))
  | .bits next => .bits (fun answer => map f (next answer))

def mapOutcome {α β : Type} (f : α → β) (result : NO α) : NO β :=
  ⟨f result.value, result.bad, result.guesses⟩

theorem run_map {α β : Type} (f : α → β) (table : NonceTable)
    (cache : SecurityNonceMonitor.NonceCache) (program : NP α) :
    SecurityNonceProgram.run table cache (map f program) =
      mapOutcome f <$> SecurityNonceProgram.run table cache program := by
  induction program generalizing cache with
  | pure value => rfl
  | reveal message next ih => exact ih (table message) _
  | guess message nonce next ih =>
    simp only [map, SecurityNonceProgram.run, ih, Functor.map_map]
    rfl
  | coin n next ih | bits next ih =>
    simp only [map, SecurityNonceProgram.run, ih, map_bind]

/-- Lift a graph macro while retaining its ordinary result. Nonce annotations
remain separate, and the full public history is part of the retained result. -/
noncomputable def liftValue {α β : Type} (points : PointTable) (exposed : QueryCache PointSpec)
    (program : Program α) (next : α → NP β) : NP β :=
  liftGraph points exposed program (fun result => next result.value)

noncomputable def observe {α : Type} (nonces : NonceTable)
    (cache : SecurityNonceMonitor.NonceCache) (program : NP α) : ProbComp α :=
  SecurityNonceProgram.Outcome.value <$> SecurityNonceProgram.run nonces cache program

theorem run_liftValue {α β : Type} (points : PointTable) (nonces : NonceTable)
    (exposed : QueryCache PointSpec) (nonceCache : SecurityNonceMonitor.NonceCache)
    (program : Program α) (next : α → NP β) :
    SecurityNonceProgram.run nonces nonceCache (liftValue points exposed program next) =
      (Outcome.value <$> run points exposed program >>= fun value =>
        SecurityNonceProgram.run nonces nonceCache (next value)) := by
  rw [liftValue, run_liftGraph, bind_map_left]

theorem observe_liftValue {α β : Type} (points : PointTable) (nonces : NonceTable)
    (exposed : QueryCache PointSpec) (nonceCache : SecurityNonceMonitor.NonceCache)
    (program : Program α) (next : α → NP β) :
    observe nonces nonceCache (liftValue points exposed program next) =
      (Outcome.value <$> run points exposed program >>= fun value => observe nonces nonceCache (next value)) := by
  rw [observe, run_liftValue, map_bind]
  rfl

end SigGolfCandidate.Hypertree.SecurityMonitorNonceLift
