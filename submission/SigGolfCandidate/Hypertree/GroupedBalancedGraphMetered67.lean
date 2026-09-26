import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCredit67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphHonestSignView67
import SigGolfCandidate.Hypertree.SecurityIndexQuery
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSignCompiler67


/-! A public H5 read cannot spend a graph contact test: tag 5 does not name
any public grouped-graph position. This is the class-sensitive credit fact
needed to combine the 160-bit index monitor with the graph monitor. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorOutsideCredit67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorCredit67
open GroupedBalancedGraphMonitorOracle67
set_option backward.isDefEq.respectTransparency false

theorem publicStep_credit_outside {α : Type} (allowance : α → Nat)
    (spent : Nat) (exposed : QueryCache PointSpec)
    (residual : QueryCache HashSpec) (query : Query)
    (outside : GroupedBalancedGraphQuery67.locate query = none)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (credit : ∀ answer opened cache,
      Credit allowance spent (next answer opened cache)) :
    Credit allowance spent (publicStep exposed residual query next) := by
  unfold publicStep
  simp only [outside]
  cases cached : residual query with
  | some answer =>
      simp only [cached]
      exact credit answer exposed residual
  | none =>
      simp only [cached]
      exact fun answer => credit answer exposed _

theorem publicStep_credit_index {α : Type} (allowance : α → Nat)
    (spent : Nat) (exposed : QueryCache PointSpec)
    (residual : QueryCache HashSpec) (message : Message)
    (randomizer : Bytes 32)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (credit : ∀ answer opened cache,
      Credit allowance spent (next answer opened cache)) :
    Credit allowance spent
      (publicStep exposed residual
        (SecurityRandomOracle.indexInput message randomizer) next) := by
  apply publicStep_credit_outside allowance spent exposed residual _
    (GroupedBalancedGraphHonestSignView67.locate_index_none message randomizer)
    next credit

theorem publicStep_credit_parsed_index {α : Type} (allowance : α → Nat)
    (spent : Nat) (exposed : QueryCache PointSpec)
    (residual : QueryCache HashSpec) (query : Query)
    (pair : Message × Bytes 32)
    (parsed : SecurityIndexQuery.parse query = some pair)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (credit : ∀ answer opened cache,
      Credit allowance spent (next answer opened cache)) :
    Credit allowance spent (publicStep exposed residual query next) := by
  have queryEq := (SecurityIndexQuery.parse_some_iff query pair).1 parsed
  rw [← queryEq]
  exact publicStep_credit_index allowance spent exposed residual
    pair.1 pair.2 next credit

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorOutsideCredit67


/-! A class-sensitive graph ledger. Public reads outside the grouped graph
spend zero graph tests; each located graph read spends at most two. The result
retains the executed graph-read count for a joint H5/graph budget proof. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMetered67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorCredit67
open GroupedBalancedGraphMonitorSignCompiler67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

structure Result (α : Type) where
  value : Option α
  remaining : Nat
  state : State
  graphCalls : Nat

noncomputable def limited {α : Type} : View α →
    Nat → State → Nat → Program (Result α)
  | .done value, remaining, state, graphCalls =>
      .done ⟨some value, remaining, state, graphCalls⟩
  | .coin n next, remaining, state, graphCalls =>
      .coin n (fun answer => limited (next answer) remaining state graphCalls)
  | .sign index next, remaining, state, graphCalls =>
      .reveal (.inr (.inl index)) (fun answer =>
        limited (next answer) remaining (signed state index answer) graphCalls)
  | .privateHash input _ next, remaining, state, graphCalls =>
      match state.residual input with
      | some answer => limited (next answer) remaining state graphCalls
      | none => .bits (fun answer =>
          limited (next answer) remaining
            (privateOpened state input answer) graphCalls)
  | .hash input next, remaining, state, graphCalls =>
      match remaining with
      | 0 => .done ⟨none, 0, state, graphCalls⟩
      | remaining + 1 =>
          match GroupedBalancedGraphQuery67.locate input with
          | none =>
              GroupedBalancedGraphMonitorOracle67.publicStep
                state.exposed state.residual input
                (fun answer exposed residual =>
                  limited (next answer) remaining
                    (opened state exposed residual) graphCalls)
          | some _ =>
              GroupedBalancedGraphMonitorOracle67.publicStep
                state.exposed state.residual input
                (fun answer exposed residual =>
                  limited (next answer) remaining
                    (opened state exposed residual) (graphCalls + 1))

theorem limited_credit {α : Type} (view : View α)
    (remaining : Nat) (state : State) (graphCalls spent : Nat)
    (bound : spent ≤ 2 * graphCalls) :
    Credit (fun result : Result α => 2 * result.graphCalls) spent
      (limited view remaining state graphCalls) := by
  induction view generalizing remaining state graphCalls spent with
  | done value => exact bound
  | coin n next ih =>
      exact fun answer => ih answer remaining state graphCalls spent bound
  | sign index next ih =>
      exact fun answer => ih answer remaining (signed state index answer)
        graphCalls spent bound
  | privateHash input outside next ih =>
      cases cached : state.residual input with
      | some answer =>
          simp only [limited, cached]
          exact ih answer remaining state graphCalls spent bound
      | none =>
          simp only [limited, cached]
          exact fun answer => ih answer remaining
            (privateOpened state input answer) graphCalls spent bound
  | hash input next ih =>
      cases remaining with
      | zero => exact bound
      | succ remaining =>
          cases located : GroupedBalancedGraphQuery67.locate input with
          | none =>
              simp only [limited, located]
              change Credit (fun result : Result α => 2 * result.graphCalls)
                spent (GroupedBalancedGraphMonitorOracle67.publicStep
                  state.exposed state.residual input
                  (fun answer exposed residual =>
                    limited (next answer) remaining
                      (opened state exposed residual) graphCalls))
              apply GroupedBalancedGraphMonitorOutsideCredit67.publicStep_credit_outside
                _ spent state.exposed state.residual input located
              intro answer exposed residual
              exact ih answer remaining (opened state exposed residual)
                graphCalls spent bound
          | some position =>
              simp only [limited, located]
              change Credit (fun result : Result α => 2 * result.graphCalls)
                spent (GroupedBalancedGraphMonitorOracle67.publicStep
                  state.exposed state.residual input
                  (fun answer exposed residual =>
                    limited (next answer) remaining
                      (opened state exposed residual) (graphCalls + 1)))
              apply GroupedBalancedGraphMonitorCredit67.publicStep_credit
              intro answer exposed residual
              exact ih answer remaining (opened state exposed residual)
                (graphCalls + 1) (spent + 2) (by omega)

#print axioms limited_credit

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMetered67
