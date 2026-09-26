import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexLift67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMetered67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphHonestSignView67
import SigGolfCandidate.Hypertree.SecurityIndexQuery


/-! Lift a passive graph-monitor program into the H5 trace language while
retaining its value, contact flag, and test count. Every graph sampling draw
becomes an unmarked independent draw. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexKeep67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphIndexLift67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable def ofGraphKeep {α β : Type} (table : PointTable) :
    QueryCache PointSpec → Program α →
      (Outcome α → SecurityIndexProgram.Program β) →
      SecurityIndexProgram.Program β
  | _, .done value, next => next ⟨value, false, 0⟩
  | cache, .reveal point resume, next =>
      ofGraphKeep table (cache.cacheQuery point (table point))
        (resume (table point)) next
  | cache, .guess point value resume, next =>
      ofGraphKeep table cache resume (fun result =>
        next (addTest
          (decide (cache point = none ∧ truncate (table point) = value)) result))
  | cache, .coin n resume, next =>
      .coin n (fun answer => ofGraphKeep table cache (resume answer) next)
  | cache, .bits resume, next =>
      unmarked ($ᵗ BitVec 256)
        (fun answer => ofGraphKeep table cache (resume answer) next)
  | cache, .collision target resume, next =>
      unmarked ($ᵗ BitVec 256)
        (fun answer => ofGraphKeep table cache (resume answer)
          (fun result => next
            (addTest (decide (truncate answer = target)) result)))

theorem execute_ofGraphKeep {α β : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (program : Program α)
    (next : Outcome α → SecurityIndexProgram.Program β) :
    SecurityIndexProgram.execute (ofGraphKeep table cache program next) =
      run table cache program >>= fun result =>
        SecurityIndexProgram.execute (next result) := by
  induction program generalizing cache next with
  | done value => simp only [ofGraphKeep, run, pure_bind]
  | reveal point resume ih => exact ih (table point) _ next
  | guess point value resume ih =>
      simp only [ofGraphKeep, run, map_eq_pure_bind, bind_assoc,
        pure_bind, addTest]
      exact ih cache _
  | coin n resume ih =>
      simp only [ofGraphKeep, SecurityIndexProgram.execute, run, bind_assoc]
      exact bind_congr (fun answer => ih answer cache next)
  | bits resume ih =>
      simp only [ofGraphKeep, execute_unmarked, run, bind_assoc]
      exact bind_congr (fun answer => ih answer cache next)
  | collision target resume ih =>
      simp only [ofGraphKeep, execute_unmarked, run, bind_assoc,
        map_eq_pure_bind, pure_bind, addTest]
      exact bind_congr (fun answer => ih answer cache _)

#print axioms execute_ofGraphKeep

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexKeep67


/-! One passive execution carrying grouped-graph contact tests and an
input-labelled H5 trace. Public H5 reads are unmarked; a fresh honest private
H5 read is marked. The same residual cache serves both classes. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJoint67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexLift67
open GroupedBalancedGraphIndexKeep67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

abbrev JointOutcome (α : Type) :=
  Outcome (GroupedBalancedGraphMetered67.Result α)

def accumulate {α : Type} (bad : Bool) (tests : Nat)
    (result : Outcome α) : Outcome α :=
  ⟨result.value, bad || result.bad, tests + result.tests⟩

noncomputable def cachedDraw {α : Type}
    (residual : QueryCache HashSpec) (input : Query) (mark : Bool)
    (next : BitVec 256 → QueryCache HashSpec →
      SecurityIndexProgram.Program α) : SecurityIndexProgram.Program α :=
  match residual input with
  | some answer => next answer residual
  | none => .draw mark (fun answer =>
      next answer (residual.cacheQuery input answer))

noncomputable def privateHashStepOn {α : Type}
    (parsed : Option (Message × Bytes 32))
    (state : State) (input : Query)
    (signedMessages : Finset Message)
    (next : BitVec 256 → State → Finset Message →
      SecurityIndexProgram.Program α) :
    SecurityIndexProgram.Program α :=
  match parsed with
  | some pair =>
      cachedDraw state.residual input (decide (pair.1 ∉ signedMessages))
        (fun answer residual =>
          next answer { state with residual := residual }
            (insert pair.1 signedMessages))
  | none =>
      unmarked ((randomOracle (spec := HashSpec) input).run state.residual)
        (fun result =>
          next result.1 { state with residual := result.2 } signedMessages)

noncomputable def publicHashStepOn {α : Type}
    (parsed : Option (Message × Bytes 32))
    (table : PointTable) (state : State) (input : Query)
    (graphCalls : Nat) (bad : Bool) (tests : Nat)
    (next : BitVec 256 → State → Nat → Bool → Nat →
      SecurityIndexProgram.Program α) :
    SecurityIndexProgram.Program α :=
  match parsed with
  | some _ =>
      cachedDraw state.residual input false (fun answer residual =>
        next answer { state with residual := residual }
          graphCalls bad tests)
  | none =>
      ofGraphKeep table state.exposed
        (GroupedBalancedGraphMonitorOracle67.publicStep
          state.exposed state.residual input
          (fun answer exposed residual =>
            .done (answer, exposed, residual)))
        (fun result =>
          let graphCalls' := graphCalls +
            if (GroupedBalancedGraphQuery67.locate input).isSome
            then 1 else 0
          next result.value.1
            (opened state result.value.2.1 result.value.2.2)
            graphCalls' (bad || result.bad) (tests + result.tests))

noncomputable def compile {α : Type} (table : PointTable) :
    View α → Nat → State → Nat → Finset Message → Bool → Nat →
      SecurityIndexProgram.Program (JointOutcome α)
  | .done value, remaining, state, graphCalls, _, bad, tests =>
      .pure ⟨⟨some value, remaining, state, graphCalls⟩, bad, tests⟩
  | .coin n next, remaining, state, graphCalls, signedMessages, bad, tests =>
      .coin n (fun answer => compile table (next answer) remaining state
        graphCalls signedMessages bad tests)
  | .sign index next, remaining, state, graphCalls, signedMessages, bad, tests =>
      let answer := table (.inr (.inl index))
      compile table (next answer) remaining (signed state index answer)
        graphCalls signedMessages bad tests
  | .privateHash input _ next, remaining, state, graphCalls,
      signedMessages, bad, tests =>
      privateHashStepOn (SecurityIndexQuery.parse input) state input
        signedMessages (fun answer updated signedMessages =>
          compile table (next answer) remaining updated graphCalls
            signedMessages bad tests)
  | .hash input next, remaining, state, graphCalls,
      signedMessages, bad, tests =>
      match remaining with
      | 0 => .pure ⟨⟨none, 0, state, graphCalls⟩, bad, tests⟩
      | remaining + 1 =>
          publicHashStepOn (SecurityIndexQuery.parse input) table state input
            graphCalls bad tests
            (fun answer updated graphCalls bad tests =>
              compile table (next answer) remaining updated graphCalls
                signedMessages bad tests)

noncomputable def start {α : Type} (table : PointTable)
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    SecurityIndexProgram.Program (JointOutcome α) :=
  compile table (view (GroupedBalancedGraphMonitorSetup67.cache table))
    remaining
    (GroupedBalancedGraphMonitorSignBound67.initial
      (GroupedBalancedGraphMonitorSetup67.cache table))
    0 ∅ false 0


end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJoint67
