import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointTotalView67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointMarkHelpers67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointGlobal67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointSumCredit67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointTotalCost67. -/
section
/-! Count graph-addressed public calls and fresh H5 draws against one total
query budget. Other graph simulator randomness is an uncharged coin. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointSumCredit67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedGraphIndexKeep67
open GroupedBalancedGraphIndexLift67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

def SumCredit {α : Type} (graphCalls : α → Nat)
    (limit spent : Nat) : SecurityIndexProgram.Program α → Prop
  | .pure value => spent + graphCalls value ≤ limit
  | .draw _ next => ∀ answer,
      SumCredit graphCalls limit (spent + 1) (next answer)
  | .coin _ next => ∀ answer,
      SumCredit graphCalls limit spent (next answer)

theorem sum_execute {α : Type} (graphCalls : α → Nat)
    (limit spent : Nat) (program : SecurityIndexProgram.Program α)
    (credit : SumCredit graphCalls limit spent program) :
    ∀ result ∈ support (SecurityIndexProgram.execute program),
      spent + result.2.length + graphCalls result.1 ≤ limit := by
  induction program generalizing spent with
  | pure value =>
      change spent + graphCalls value ≤ limit at credit
      intro result member
      simp only [SecurityIndexProgram.execute, support_pure,
        Set.mem_singleton_iff] at member
      subst result
      simpa only [List.length_nil, Nat.add_zero] using credit
  | coin n next ih =>
      intro result member
      simp only [SecurityIndexProgram.execute, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      exact ih answer spent (credit answer) result member
  | draw mark next ih =>
      intro result member
      simp only [SecurityIndexProgram.execute, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      simp only [support_map, Set.mem_image] at member
      obtain ⟨tail, tailMember, same⟩ := member
      subst result
      have bound := ih answer (spent + 1) (credit answer) tail tailMember
      simp only [List.length_cons]
      omega

theorem sum_weaken {α : Type} (graphCalls : α → Nat)
    (limit small large : Nat) (less : small ≤ large)
    (program : SecurityIndexProgram.Program α)
    (credit : SumCredit graphCalls limit large program) :
    SumCredit graphCalls limit small program := by
  induction program generalizing small large with
  | pure value =>
      change large + graphCalls value ≤ limit at credit
      change small + graphCalls value ≤ limit
      omega
  | coin n next ih =>
      change ∀ answer, SumCredit graphCalls limit large (next answer) at credit
      exact fun answer => ih answer small large less (credit answer)
  | draw mark next ih =>
      change ∀ answer, SumCredit graphCalls limit (large + 1) (next answer)
        at credit
      exact fun answer => ih answer (small + 1) (large + 1)
        (by omega) (credit answer)

theorem unmarked_credit {α β : Type} (program : ProbComp α)
    (next : α → SecurityIndexProgram.Program β)
    (graphCalls : β → Nat) (limit spent : Nat)
    (credit : ∀ value, SumCredit graphCalls limit spent (next value)) :
    SumCredit graphCalls limit spent (unmarked program next) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact credit value
  | query_bind n resume ih =>
      rw [unmarked_query]
      exact fun answer => ih answer

theorem cached_draw_one {α : Type}
    (residual : QueryCache HashSpec) (input : Query) (mark : Bool)
    (next : BitVec 256 → QueryCache HashSpec →
      SecurityIndexProgram.Program α)
    (graphCalls : α → Nat) (limit spent : Nat)
    (credit : ∀ answer updated,
      SumCredit graphCalls limit (spent + 1) (next answer updated)) :
    SumCredit graphCalls limit spent (cachedDraw residual input mark next) := by
  cases present : residual input with
  | some answer =>
      simpa only [cachedDraw, present] using
        sum_weaken graphCalls limit spent (spent + 1) (by omega) _
          (credit answer residual)
  | none =>
      simp only [cachedDraw, present, SumCredit]
      exact fun answer => credit answer _

theorem of_graph_keep_credit {α β : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (program : Program α)
    (next : Outcome α → SecurityIndexProgram.Program β)
    (graphCalls : β → Nat) (limit spent : Nat)
    (credit : ∀ result, SumCredit graphCalls limit spent (next result)) :
    SumCredit graphCalls limit spent (ofGraphKeep table cache program next) := by
  induction program generalizing cache next with
  | done value => exact credit ⟨value, false, 0⟩
  | reveal point resume ih => exact ih (table point) _ next credit
  | guess point value resume ih =>
      apply ih cache _
      intro result
      exact credit _
  | coin n resume ih =>
      change ∀ answer, SumCredit graphCalls limit spent
        (ofGraphKeep table cache (resume answer) next)
      exact fun answer => ih answer cache next credit
  | bits resume ih =>
      change SumCredit graphCalls limit spent
        (unmarked ($ᵗ BitVec 256)
          (fun answer => ofGraphKeep table cache (resume answer) next))
      apply unmarked_credit
      exact fun answer => ih answer cache next credit
  | collision target resume ih =>
      change SumCredit graphCalls limit spent
        (unmarked ($ᵗ BitVec 256)
          (fun answer => ofGraphKeep table cache (resume answer)
            (fun result => next (addTest
              (decide (truncate answer = target)) result))))
      apply unmarked_credit
      intro answer
      apply ih answer cache _
      intro result
      exact credit _

#print axioms sum_execute
#print axioms of_graph_keep_credit

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointSumCredit67

end

/-! In the total-query-limited View, one hash action pays for at most one
located graph query or one fresh H5 draw. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointTotalCost67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedGraphIndexJointGlobal67
open GroupedBalancedGraphIndexJointTotalView67
open GroupedBalancedGraphIndexJointSumCredit67
open GroupedBalancedGraphIndexKeep67
open GroupedBalancedGraphIndexLift67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 30000
open scoped Classical

def graphCalls {α : Type} (result : JointOutcome α) : Nat :=
  result.value.graphCalls

theorem private_step {α : Type} (table : PointTable)
    (input : Query) (outside : GroupedBalancedGraphQuery67.locate input = none)
    (next : BitVec 256 → View α)
    (remaining : Nat) (state : State) (calls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat)
    (spent totalRemaining limit : Nat)
    (positive : 0 < totalRemaining)
    (bounded : spent + calls + totalRemaining ≤ limit)
    (ih : ∀ answer updated messages spent',
      spent' + calls + (totalRemaining - 1) ≤ limit →
      SumCredit graphCalls limit spent'
        (compile table (next answer) remaining updated calls
          messages bad tests)) :
    SumCredit graphCalls limit spent
      (compile table (.privateHash input outside next) remaining state
        calls signedMessages bad tests) := by
  rw [GroupedBalancedGraphIndexJoint67.compile]
  cases parsed : SecurityIndexQuery.parse input with
  | some pair =>
      change SumCredit graphCalls limit spent
        (cachedDraw state.residual input (decide (pair.1 ∉ signedMessages))
          (fun answer residual =>
            compile table (next answer) remaining
              { state with residual := residual } calls
              (insert pair.1 signedMessages) bad tests))
      apply cached_draw_one
      intro answer updated
      exact ih answer _ _ (spent + 1) (by omega)
  | none =>
      change SumCredit graphCalls limit spent
        (unmarked ((randomOracle (spec := HashSpec) input).run state.residual)
          (fun result =>
            compile table (next result.1) remaining
              { state with residual := result.2 } calls
              signedMessages bad tests))
      apply unmarked_credit
      intro result
      exact ih result.1 _ _ spent (by omega)

theorem hash_step {α : Type} (table : PointTable)
    (input : Query) (next : BitVec 256 → View α)
    (remaining : Nat) (state : State) (calls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat)
    (spent totalRemaining limit : Nat)
    (positive : 0 < totalRemaining)
    (bounded : spent + calls + totalRemaining ≤ limit)
    (ih : ∀ answer updated calls' bad' tests' spent',
      spent' + calls' + (totalRemaining - 1) ≤ limit →
      SumCredit graphCalls limit spent'
        (compile table (next answer) (remaining - 1) updated calls'
          signedMessages bad' tests')) :
    SumCredit graphCalls limit spent
      (compile table (.hash input next) remaining state calls
        signedMessages bad tests) := by
  cases remaining with
  | zero =>
      rw [GroupedBalancedGraphIndexJoint67.compile]
      change spent + calls ≤ limit
      omega
  | succ remaining =>
      rw [GroupedBalancedGraphIndexJoint67.compile]
      cases parsed : SecurityIndexQuery.parse input with
      | some pair =>
          change SumCredit graphCalls limit spent
            (cachedDraw state.residual input false
              (fun answer residual =>
                compile table (next answer) remaining
                  { state with residual := residual } calls
                  signedMessages bad tests))
          apply cached_draw_one
          intro answer updated
          exact ih answer _ calls bad tests (spent + 1) (by omega)
      | none =>
          change SumCredit graphCalls limit spent
            (ofGraphKeep table state.exposed
              (GroupedBalancedGraphMonitorOracle67.publicStep
                state.exposed state.residual input
                (fun answer exposed residual =>
                  .done (answer, exposed, residual)))
              (fun result =>
                let calls' := calls +
                  if (GroupedBalancedGraphQuery67.locate input).isSome
                  then 1 else 0
                compile table (next result.value.1) remaining
                  (opened state result.value.2.1 result.value.2.2)
                  calls' signedMessages
                  (bad || result.bad) (tests + result.tests)))
          apply of_graph_keep_credit
          intro result
          apply ih result.value.1 _ _ _ _ spent
          split <;> omega

attribute [local irreducible] SumCredit
attribute [local irreducible] GroupedBalancedGraphIndexJoint67.compile

theorem compile_total_cost {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (calls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests : Nat)
    (spent totalRemaining limit : Nat)
    (budget : TotalBudget totalRemaining view)
    (bounded : spent + calls + totalRemaining ≤ limit) :
    SumCredit graphCalls limit spent
      (compile table view remaining state calls
        signedMessages bad tests) := by
  induction view generalizing remaining state calls signedMessages bad tests
      spent totalRemaining with
  | done value =>
      simp only [GroupedBalancedGraphIndexJoint67.compile, SumCredit, graphCalls]
      omega
  | coin n next ih =>
      change ∀ answer, TotalBudget totalRemaining (next answer) at budget
      rw [GroupedBalancedGraphIndexJoint67.compile]
      simp only [SumCredit]
      exact fun answer => ih answer remaining state calls signedMessages
        bad tests spent totalRemaining (budget answer) bounded
  | sign index next ih =>
      change ∀ answer, TotalBudget totalRemaining (next answer) at budget
      rw [GroupedBalancedGraphIndexJoint67.compile]
      exact ih _ remaining _ calls signedMessages bad tests spent
        totalRemaining (budget _) bounded
  | privateHash input outside next ih =>
      change 0 < totalRemaining ∧ ∀ answer,
        TotalBudget (totalRemaining - 1) (next answer) at budget
      exact private_step table input outside next remaining state calls
        signedMessages bad tests spent totalRemaining limit budget.1 bounded
        (fun answer updated messages spent' nextBound =>
          ih answer remaining updated calls messages bad tests spent'
            (totalRemaining - 1) (budget.2 answer) nextBound)
  | hash input next ih =>
      change 0 < totalRemaining ∧ ∀ answer,
        TotalBudget (totalRemaining - 1) (next answer) at budget
      exact hash_step table input next remaining state calls
        signedMessages bad tests spent totalRemaining limit budget.1 bounded
        (fun answer updated calls' bad' tests' spent' nextBound =>
          ih answer (remaining - 1) updated calls' signedMessages
            bad' tests' spent' (totalRemaining - 1)
            (budget.2 answer) nextBound)

theorem global_total_cost {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat)
    (budget : ∀ cache, TotalBudget remaining (view cache)) :
    ∀ result ∈ support
      (SecurityIndexProgram.execute (global view remaining)),
      result.1.value.graphCalls + result.2.length ≤ remaining := by
  have credit :
      SumCredit graphCalls remaining 0 (global view remaining) := by
    unfold global
    apply unmarked_credit
    intro table
    change SumCredit graphCalls remaining 0
      (compile table
        (view (GroupedBalancedGraphMonitorSetup67.cache table)) remaining
        (GroupedBalancedGraphMonitorSignBound67.initial
          (GroupedBalancedGraphMonitorSetup67.cache table))
        0 ∅ false 0)
    exact compile_total_cost table _ remaining _ 0 ∅ false 0
      0 remaining remaining (budget _) (by omega)
  intro result member
  have bound := sum_execute graphCalls remaining 0 _ credit result member
  simpa only [Nat.zero_add, graphCalls, Nat.add_comm] using bound

#print axioms global_total_cost

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointTotalCost67
