import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorProgram67
import SigGolfCandidate.Hypertree.SecurityIndexProgram

/-! Erase the direct67 passive graph monitor into the H5 index program while
retaining every sampled answer and continuation. Graph contact flags and test
counters remain on the graph side; no index draw is created by this erasure. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexLift67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
set_option backward.isDefEq.respectTransparency false

def unmarked {α β : Type} (program : ProbComp α)
    (next : α → SecurityIndexProgram.Program β) :
    SecurityIndexProgram.Program β :=
  OracleComp.construct next (fun n _ continuation => .coin n continuation) program

@[simp] theorem unmarked_pure {α β : Type} (value : α)
    (next : α → SecurityIndexProgram.Program β) :
    unmarked (pure value) next = next value := rfl

theorem unmarked_query {α β : Type} (n : Nat)
    (resume : Fin (n + 1) → ProbComp α)
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
      change (ProbComp.uniformFin n >>= fun answer =>
        SecurityIndexProgram.execute (unmarked (resume answer) next)) = _
      simp only [bind_assoc]
      exact bind_congr ih

noncomputable def ofGraph {α β : Type} (table : PointTable) :
    QueryCache PointSpec → Program α →
      (α → SecurityIndexProgram.Program β) → SecurityIndexProgram.Program β
  | _, .done value, next => next value
  | cache, .reveal point resume, next =>
      ofGraph table (cache.cacheQuery point (table point))
        (resume (table point)) next
  | cache, .guess _ _ resume, next => ofGraph table cache resume next
  | cache, .coin n resume, next =>
      .coin n (fun answer => ofGraph table cache (resume answer) next)
  | cache, .bits resume, next =>
      unmarked ($ᵗ BitVec 256)
        (fun answer => ofGraph table cache (resume answer) next)
  | cache, .collision _ resume, next =>
      unmarked ($ᵗ BitVec 256)
        (fun answer => ofGraph table cache (resume answer) next)

theorem execute_ofGraph {α β : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (program : Program α)
    (next : α → SecurityIndexProgram.Program β) :
    SecurityIndexProgram.execute (ofGraph table cache program next) =
      run table cache program >>= fun result =>
        SecurityIndexProgram.execute (next result.value) := by
  induction program generalizing cache with
  | done value => simp only [ofGraph, run, pure_bind]
  | reveal point resume ih => exact ih (table point) _
  | guess point value resume ih =>
      simp only [ofGraph, run, map_eq_pure_bind, bind_assoc,
        pure_bind, addTest]
      exact ih cache
  | coin n resume ih =>
      simp only [ofGraph, SecurityIndexProgram.execute, run, bind_assoc]
      exact bind_congr (fun answer => ih answer cache)
  | bits resume ih =>
      simp only [ofGraph, execute_unmarked, run, bind_assoc]
      exact bind_congr (fun answer => ih answer cache)
  | collision target resume ih =>
      simp only [ofGraph, execute_unmarked, run, bind_assoc,
        map_eq_pure_bind, pure_bind, addTest]
      exact bind_congr (fun answer => ih answer cache)

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexLift67
