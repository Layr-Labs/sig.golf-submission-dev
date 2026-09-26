import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointViewBudget67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexMarks67

/-! Structural marked-draw accounting for the joint graph/H5 interpreter. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointMarkHelpers67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedGraphIndexKeep67
open GroupedBalancedGraphIndexMarks67
open GroupedBalancedGraphIndexLift67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem credit_weaken {α : Type} (cost : α → Nat)
    (small large : Nat) (less : small ≤ large)
    (program : SecurityIndexProgram.Program α)
    (credit : MarkedCredit cost large program) :
    MarkedCredit cost small program := by
  induction program generalizing small large with
  | pure value =>
      change large ≤ cost value at credit
      change small ≤ cost value
      omega
  | coin n next ih =>
      change ∀ answer, MarkedCredit cost large (next answer) at credit
      exact fun answer => ih answer small large less (credit answer)
  | draw mark next ih =>
      change ∀ answer, MarkedCredit cost
        (large + if mark then 1 else 0) (next answer) at credit
      exact fun answer => ih answer
        (small + if mark then 1 else 0)
        (large + if mark then 1 else 0) (by omega) (credit answer)

theorem cached_draw_same {α : Type}
    (residual : QueryCache HashSpec) (input : Query)
    (next : BitVec 256 → QueryCache HashSpec →
      SecurityIndexProgram.Program α)
    (cost : α → Nat) (spent : Nat)
    (continuation : ∀ answer updated,
      MarkedCredit cost spent (next answer updated)) :
    MarkedCredit cost spent
      (cachedDraw residual input false next) := by
  cases present : residual input with
  | some answer =>
      simpa only [cachedDraw, present] using continuation answer residual
  | none =>
      simp only [cachedDraw, present, MarkedCredit,
        Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact fun answer => continuation answer _

theorem cached_draw_one {α : Type}
    (residual : QueryCache HashSpec) (input : Query) (mark : Bool)
    (next : BitVec 256 → QueryCache HashSpec →
      SecurityIndexProgram.Program α)
    (cost : α → Nat) (spent : Nat)
    (continuation : ∀ answer updated,
      MarkedCredit cost (spent + 1) (next answer updated)) :
    MarkedCredit cost spent
      (cachedDraw residual input mark next) := by
  cases present : residual input with
  | some answer =>
      simpa only [cachedDraw, present] using
        credit_weaken cost spent (spent + 1) (by omega) _
          (continuation answer residual)
  | none =>
      simp only [cachedDraw, present, MarkedCredit]
      intro answer
      exact credit_weaken cost _ (spent + 1)
        (by cases mark <;> simp <;> omega)
        _ (continuation answer _)

theorem of_graph_keep_credit {α β : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (program : Program α)
    (next : Outcome α → SecurityIndexProgram.Program β)
    (cost : β → Nat) (spent : Nat)
    (continuation : ∀ result, MarkedCredit cost spent (next result)) :
    MarkedCredit cost spent (ofGraphKeep table cache program next) := by
  induction program generalizing cache next with
  | done value => exact continuation ⟨value, false, 0⟩
  | reveal point resume ih =>
      exact ih (table point) _ next continuation
  | guess point value resume ih =>
      apply ih cache _
      intro result
      exact continuation _
  | coin n resume ih =>
      change ∀ answer, MarkedCredit cost spent
        (ofGraphKeep table cache (resume answer) next)
      exact fun answer => ih answer cache next continuation
  | bits resume ih =>
      change MarkedCredit cost spent
        (unmarked ($ᵗ BitVec 256)
          (fun answer => ofGraphKeep table cache (resume answer) next))
      apply unmarked_credit
      exact fun answer => ih answer cache next continuation
  | collision target resume ih =>
      change MarkedCredit cost spent
        (unmarked ($ᵗ BitVec 256)
          (fun answer => ofGraphKeep table cache (resume answer)
            (fun result => next (addTest
              (decide (truncate answer = target)) result))))
      apply unmarked_credit
      intro answer
      apply ih answer cache _
      intro result
      exact continuation _

theorem private_hash_step_credit {α : Type}
    (parsed : Option (Message × Bytes 32))
    (state : State) (input : Query) (signedMessages : Finset Message)
    (next : BitVec 256 → State → Finset Message →
      SecurityIndexProgram.Program α)
    (cost : α → Nat) (spent : Nat)
    (continuation : ∀ answer updated messages,
      MarkedCredit cost (spent + 1) (next answer updated messages)) :
    MarkedCredit cost spent
      (privateHashStepOn parsed state input signedMessages next) := by
  cases parsed with
  | some pair =>
      change MarkedCredit cost spent
        (cachedDraw state.residual input (decide (pair.1 ∉ signedMessages))
          (fun answer residual =>
            next answer { state with residual := residual }
              (insert pair.1 signedMessages)))
      exact cached_draw_one _ _ _ _ cost spent
        (fun answer residual => continuation answer _ _)
  | none =>
      change MarkedCredit cost spent
        (unmarked ((randomOracle (spec := HashSpec) input).run state.residual)
          (fun result => next result.1
            { state with residual := result.2 } signedMessages))
      apply unmarked_credit
      intro result
      exact credit_weaken cost spent (spent + 1) (by omega) _
        (continuation result.1 _ _)

theorem public_hash_step_credit {α : Type}
    (parsed : Option (Message × Bytes 32)) (table : PointTable)
    (state : State) (input : Query) (graphCalls : Nat)
    (bad : Bool) (tests : Nat)
    (next : BitVec 256 → State → Nat → Bool → Nat →
      SecurityIndexProgram.Program α)
    (cost : α → Nat) (spent : Nat)
    (continuation : ∀ answer updated graphCalls bad tests,
      MarkedCredit cost spent
        (next answer updated graphCalls bad tests)) :
    MarkedCredit cost spent
      (publicHashStepOn parsed table state input graphCalls bad tests next) := by
  cases parsed with
  | some pair =>
      change MarkedCredit cost spent
        (cachedDraw state.residual input false
          (fun answer residual =>
            next answer { state with residual := residual }
              graphCalls bad tests))
      exact cached_draw_same _ _ _ cost spent
        (fun answer residual => continuation answer _ _ _ _)
  | none =>
      change MarkedCredit cost spent
        (ofGraphKeep table state.exposed
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
              graphCalls' (bad || result.bad) (tests + result.tests)))
      apply of_graph_keep_credit
      intro result
      exact continuation _ _ _ _ _

#print axioms private_hash_step_credit
#print axioms public_hash_step_credit

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointMarkHelpers67
