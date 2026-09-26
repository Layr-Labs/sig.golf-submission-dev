import SigGolfCandidate.Hypertree.SecurityGraphMonitorProgram
import SigGolfCandidate.Hypertree.SecurityIndexProgram
import SigGolfCandidate.Hypertree.SecurityMonitorGraphView
import SigGolfCandidate.Hypertree.SecurityGraphMonitorObserve

/-! Inlined from SigGolfCandidate.Hypertree.SecurityMonitorIndexLift; its only importer was SigGolfCandidate.Hypertree.SecurityMonitorIndexView. -/
section
namespace SigGolfCandidate.Hypertree.SecurityMonitorIndexLift
open SigGolf OracleComp OracleSpec Reference SecurityGraphFactor SecurityGraphPassive
  SecurityGraphMonitorProgram
set_option backward.isDefEq.respectTransparency false

/-- Ordinary randomness does not create an H5 index observation. -/
def unmarked {α β : Type} (program : ProbComp α)
    (next : α → SecurityIndexProgram.Program β) : SecurityIndexProgram.Program β :=
  OracleComp.construct next (fun n _ continuation => .coin n continuation) program

@[simp] theorem unmarked_pure {α β : Type} (value : α)
    (next : α → SecurityIndexProgram.Program β) : unmarked (pure value) next = next value := rfl

theorem unmarked_query {α β : Type} (n : Nat) (resume : Fin (n+1) → ProbComp α)
    (next : α → SecurityIndexProgram.Program β) :
    unmarked (liftM (unifSpec.query n) >>= resume) next =
      .coin n (fun answer => unmarked (resume answer) next) := rfl

theorem execute_unmarked {α β : Type} (program : ProbComp α)
    (next : α → SecurityIndexProgram.Program β) :
    SecurityIndexProgram.execute (unmarked program next) =
      program >>= fun value => SecurityIndexProgram.execute (next value) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp only [unmarked_pure, pure_bind]
  | query_bind n resume ih =>
    rw [unmarked_query]
    change (ProbComp.uniformFin n >>= fun answer => SecurityIndexProgram.execute (unmarked (resume answer) next)) = _
    simp only [bind_assoc]
    exact bind_congr ih

/-- Forget passive graph tests while preserving every ordinary answer, reveal,
and continuation. This inserts no marked or unmarked index draws. -/
noncomputable def ofGraph {α β : Type} (table : PointTable) :
    QueryCache PointSpec → Program α → (α → SecurityIndexProgram.Program β) → SecurityIndexProgram.Program β
  | _, .done value, next => next value
  | cache, .reveal point resume, next =>
      ofGraph table (cache.cacheQuery point (table point)) (resume (table point)) next
  | cache, .guess _ _ resume, next => ofGraph table cache resume next
  | cache, .coin n resume, next =>
      .coin n (fun answer => ofGraph table cache (resume answer) next)
  | cache, .bits resume, next =>
      unmarked ($ᵗ BitVec 256) (fun answer => ofGraph table cache (resume answer) next)
  | cache, .collision _ resume, next =>
      unmarked ($ᵗ BitVec 256) (fun answer => ofGraph table cache (resume answer) next)

/-- Exact joint-output equality: graph flags and test counters alone disappear. -/
theorem execute_ofGraph {α β : Type} (table : PointTable) (cache : QueryCache PointSpec)
    (program : Program α) (next : α → SecurityIndexProgram.Program β) :
    SecurityIndexProgram.execute (ofGraph table cache program next) =
      run table cache program >>= fun result => SecurityIndexProgram.execute (next result.value) := by
  induction program generalizing cache with
  | done value => simp only [ofGraph, run, pure_bind]
  | reveal point resume ih => exact ih (table point) _
  | guess point value resume ih =>
    simp only [ofGraph, run, map_eq_pure_bind, bind_assoc, pure_bind, addTest]
    exact ih cache
  | coin n resume ih =>
    simp only [ofGraph, SecurityIndexProgram.execute, run, bind_assoc]
    exact bind_congr (fun answer => ih answer cache)
  | bits resume ih =>
    simp only [ofGraph, execute_unmarked, run, bind_assoc]
    exact bind_congr (fun answer => ih answer cache)
  | collision target resume ih =>
    simp only [ofGraph, execute_unmarked, run, bind_assoc, map_eq_pure_bind, pure_bind, addTest]
    exact bind_congr (fun answer => ih answer cache)

#print axioms execute_ofGraph
end SigGolfCandidate.Hypertree.SecurityMonitorIndexLift

end

namespace SigGolfCandidate.Hypertree.SecurityMonitorIndexView
open SigGolf OracleComp OracleSpec Reference SecurityGraphFactor SecurityGraphPassive
  SecurityGraphMonitorSign SecurityMonitorView SecurityMonitorIndexState
  SecurityMonitorGraphView SecurityMonitorIndexLift SecurityGraphPublicMonitor
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

noncomputable def observe {α : Type} (program : SecurityIndexProgram.Program α) : ProbComp α :=
  Prod.fst <$> SecurityIndexProgram.execute program

@[simp] theorem observe_pure {α : Type} (value : α) : observe (.pure value) = pure value := by
  simp [observe, SecurityIndexProgram.execute]

@[simp] theorem observe_coin {α : Type} (n : Nat) (next : Fin (n+1) → SecurityIndexProgram.Program α) :
    observe (.coin n next) = (($ᵗ Fin (n+1)) >>= fun answer => observe (next answer)) := by
  simp only [observe, SecurityIndexProgram.execute, map_bind]

@[simp] theorem observe_draw {α : Type} (mark : Bool) (next : BitVec 256 → SecurityIndexProgram.Program α) :
    observe (.draw mark next) = (($ᵗ BitVec 256) >>= fun answer => observe (next answer)) := by
  simp only [observe, SecurityIndexProgram.execute, map_bind, Functor.map_map]

@[simp] theorem observe_ofGraph {α β : Type} (table : PointTable) (cache : QueryCache PointSpec)
    (program : SecurityGraphMonitorProgram.Program α) (next : α → SecurityIndexProgram.Program β) :
    observe (ofGraph table cache program next) =
      SecurityGraphMonitorObserve.observe table cache program >>= fun value => observe (next value) := by
  simp only [observe, execute_ofGraph, map_bind, SecurityGraphMonitorObserve.observe,
    map_eq_pure_bind, bind_assoc, pure_bind]

noncomputable def drawCached {α : Type} (cache : QueryCache HashSpec) (input : Query)
    (mark : Bool) (next : BitVec 256 → QueryCache HashSpec → SecurityIndexProgram.Program α) : SecurityIndexProgram.Program α :=
  match cache input with
  | some answer => next answer cache
  | none => .draw mark (fun answer => next answer (cache.cacheQuery input answer))

@[simp] theorem observe_drawCached {α : Type} (cache : QueryCache HashSpec) (input : Query)
    (mark : Bool) (next : BitVec 256 → QueryCache HashSpec → SecurityIndexProgram.Program α) :
    observe (drawCached cache input mark next) =
      ((randomOracle (spec := HashSpec) input).run cache >>= fun result => observe (next result.1 result.2)) := by
  cases found : cache input <;>
    simp only [drawCached, found, observe_draw, randomOracle.run_eq, pure_bind, bind_assoc]

/-- Same actual view and shared budget as the graph simulation; only fresh H5
answers create index-trace entries. All other random choices remain unmarked. -/
noncomputable def compile {α : Type} (table : PointTable) (nonces : NonceTable) (metadata : MetadataTable) :
    View α → Nat → QueryCache PointSpec → QueryCache HashSpec → History → SecurityIndexProgram.Program (Result α)
  | .done value, remaining, exposed, residual, history => .pure ⟨some value,remaining,exposed,residual,history⟩
  | .coin n next, remaining, exposed, residual, history =>
      .coin n (fun answer => compile table nonces metadata (next answer) remaining exposed residual history)
  | .hash input next, remaining, exposed, residual, history =>
      match remaining with
      | 0 => .pure ⟨none,0,exposed,residual,history⟩
      | remaining+1 =>
          if (SecurityIndexQuery.parse input).isSome then
            drawCached residual input false (fun answer cache =>
              compile table nonces metadata (next answer) remaining exposed cache
                (recordPublic history input (residual input).isSome answer))
          else ofGraph table exposed
            (SecurityGraphMonitorOracle.publicStep metadata exposed residual input
              (fun answer opened cache => .done (answer,opened,cache)))
            (fun result => compile table nonces metadata (next result.1) remaining result.2.1 result.2.2
              (recordPublic history input (residual input).isSome result.1))
  | .sign message next, remaining, exposed, residual, history =>
      if 117508 ≤ remaining then
        let nonce := nonces message
        let input := SecurityRandomOracle.indexInput message nonce
        drawCached residual input (decide (message ∉ history.signedMessages)) (fun answer cache =>
          let index := answer.extractLsb' 0 160
          let opened := SecurityGraphDisclosure.revealCache table (needed metadata exposed index) exposed
          let factors := viewFactors opened metadata
          let signature := SecurityGraphSigner.signature (privateTable factors) (labels factors) nonce index
          compile table nonces metadata (next (SecurityExperiment.serialize signature)) (remaining-117508)
            opened cache (recordSign history message (residual input).isSome answer))
      else .pure ⟨none,remaining,exposed,residual,history⟩

theorem publicStep_index {α : Type} (table : PointTable) (metadata : MetadataTable)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (input : Query)
    (parsed : (SecurityIndexQuery.parse input).isSome = true)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → SecurityGraphMonitorProgram.Program α) :
    SecurityGraphMonitorObserve.observe table exposed (SecurityGraphMonitorOracle.publicStep metadata exposed cache input next) =
      ((randomOracle (spec := HashSpec) input).run cache >>= fun result =>
        SecurityGraphMonitorObserve.observe table exposed (next result.1 exposed result.2)) := by
  have outside : SecurityGraphQuery.locate input = none := by
    cases found : SecurityIndexQuery.parse input with
    | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at parsed
    | some pair =>
      have same := (SecurityIndexQuery.parse_some_iff input pair).1 found
      rw [← same, SecurityIndexQuery.locate_index]
  simp only [SecurityGraphMonitorOracle.publicStep, outside, SecurityGraphMonitorOracle.knownResidual]
  cases found : cache input <;>
    simp only [found, SecurityGraphMonitorObserve.observe_bits, randomOracle.run_eq, pure_bind, bind_assoc]

/-- Exact result/history law for the actual budgeted compiler. -/
theorem observe_compile {α : Type} (table : PointTable) (nonces : NonceTable) (metadata : MetadataTable)
    (view : View α) (remaining : Nat) (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec) (history : History) :
    observe (compile table nonces metadata view remaining exposed residual history) =
      SecurityGraphMonitorObserve.observe table exposed
        (SecurityMonitorGraphView.compile nonces metadata view remaining exposed residual history) := by
  induction view generalizing remaining exposed residual history with
  | done value => simp only [compile, SecurityMonitorGraphView.compile, observe_pure, SecurityGraphMonitorObserve.observe_done]
  | coin n next ih =>
    simp only [compile, SecurityMonitorGraphView.compile, observe_coin, SecurityGraphMonitorObserve.observe_coin]
    exact bind_congr (fun answer => ih answer _ _ _ _)
  | hash input next ih =>
    cases remaining with
    | zero => simp only [compile, SecurityMonitorGraphView.compile, observe_pure, SecurityGraphMonitorObserve.observe_done]
    | succ remaining =>
      rw [compile, SecurityMonitorGraphView.compile]
      split
      next parsed =>
        rw [observe_drawCached, publicStep_index table metadata exposed residual input parsed]
        exact bind_congr (fun result => ih result.1 _ _ _ _)
      next absent =>
        rw [observe_ofGraph]
        conv_rhs => rw [SecurityGraphMonitorObserve.observe_publicStep_bind]
        exact bind_congr (fun result => ih result.1 _ _ _ _)
  | sign message next ih =>
    rw [compile, SecurityMonitorGraphView.compile]
    split
    next enough =>
      dsimp only
      rw [observe_drawCached, SecurityGraphMonitorObserve.observe_indexStep_bind]
      apply bind_congr
      intro result
      rw [SecurityGraphMonitorObserve.observe_disclose]
      exact ih _ _ _ _ _
    next insufficient =>
      simp only [observe_pure, SecurityGraphMonitorObserve.observe_done]

noncomputable def start {α : Type} (table : PointTable) (nonces : NonceTable) (metadata : MetadataTable)
    (view : View α) (budget : Nat) : SecurityIndexProgram.Program (Result α) :=
  if 739 ≤ budget then
    compile table nonces metadata view (budget-739) (SecurityGraphMonitorSetup.cache table metadata) ∅ (recordKeygen {})
  else .pure ⟨none,budget,∅,∅,{}⟩

theorem observe_start {α : Type} (table : PointTable) (nonces : NonceTable) (metadata : MetadataTable)
    (view : View α) (budget : Nat) :
    observe (start table nonces metadata view budget) =
      SecurityGraphMonitorObserve.observe table ∅ (SecurityMonitorGraphView.start nonces metadata view budget) := by
  rw [start, SecurityMonitorGraphView.start]
  split
  · rw [observe_compile]
    unfold SecurityGraphMonitorObserve.observe
    rw [SecurityGraphMonitorSetup.run_setup]
  · rfl

#print axioms observe_compile
end SigGolfCandidate.Hypertree.SecurityMonitorIndexView
