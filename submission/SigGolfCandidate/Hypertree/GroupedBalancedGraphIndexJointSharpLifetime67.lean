import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointIndexBudget67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointMarkHelpers67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointTotalView67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointGlobal67


namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointSharpHelpers67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedGraphIndexJointMarkHelpers67
open GroupedBalancedGraphIndexMarks67
open GroupedBalancedGraphIndexLift67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem private_outside_credit {α : Type}
    (input : Query) (parsed : SecurityIndexQuery.parse input = none)
    (state : State) (signedMessages : Finset Message)
    (next : BitVec 256 → State → Finset Message →
      SecurityIndexProgram.Program α)
    (cost : α → Nat) (spent : Nat)
    (continuation : ∀ answer updated,
      MarkedCredit cost spent
        (next answer updated signedMessages)) :
    MarkedCredit cost spent
      (privateHashStepOn (SecurityIndexQuery.parse input)
        state input signedMessages next) := by
  rw [parsed]
  change MarkedCredit cost spent
    (unmarked ((randomOracle (spec := HashSpec) input).run state.residual)
      (fun result => next result.1
        { state with residual := result.2 } signedMessages))
  apply GroupedBalancedGraphIndexMarks67.unmarked_credit
  intro result
  exact continuation result.1 _

theorem private_index_credit {α : Type}
    (input : Query) (pair : Message × Bytes 32)
    (parsed : SecurityIndexQuery.parse input = some pair)
    (state : State) (signedMessages : Finset Message)
    (next : BitVec 256 → State → Finset Message →
      SecurityIndexProgram.Program α)
    (cost : α → Nat) (spent : Nat)
    (continuation : ∀ answer updated,
      MarkedCredit cost (spent + 1)
        (next answer updated (insert pair.1 signedMessages))) :
    MarkedCredit cost spent
      (privateHashStepOn (SecurityIndexQuery.parse input)
        state input signedMessages next) := by
  rw [parsed]
  change MarkedCredit cost spent
    (cachedDraw state.residual input (decide (pair.1 ∉ signedMessages))
      (fun answer residual =>
        next answer { state with residual := residual }
          (insert pair.1 signedMessages)))
  exact GroupedBalancedGraphIndexJointMarkHelpers67.cached_draw_one _ _ _ _
    cost spent (fun answer residual => continuation answer _)

#print axioms private_outside_credit
#print axioms private_index_credit

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointSharpHelpers67



/-! Total-query truncation preserves the more precise one-index-read-per-sign
lifetime certificate. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointIndexCutoff67
open SigGolf OracleSpec Reference
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJointIndexBudget67
open GroupedBalancedGraphIndexJointTotalView67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem total_limited_index_budget {α : Type} (view : View α)
    (totalRemaining indexRemaining : Nat)
    (budget : IndexBudget indexRemaining view) :
    IndexBudget indexRemaining (totalLimited view totalRemaining) := by
  induction view generalizing totalRemaining indexRemaining with
  | done value => exact .done _ _
  | coin n next ih =>
      cases budget with
      | coin _ _ _ child =>
          exact .coin _ _ _ (fun answer =>
            ih answer totalRemaining indexRemaining (child answer))
  | sign index next ih =>
      cases budget with
      | sign _ _ _ child =>
          exact .sign _ _ _ (fun answer =>
            ih answer totalRemaining indexRemaining (child answer))
  | hash input next ih =>
      cases totalRemaining with
      | zero => exact .done _ _
      | succ totalRemaining =>
          cases budget with
          | hash _ _ _ child =>
              exact .hash _ _ _ (fun answer =>
                ih answer totalRemaining indexRemaining (child answer))
  | privateHash input outside next ih =>
      cases totalRemaining with
      | zero => exact .done _ _
      | succ totalRemaining =>
          cases budget with
          | privateOutside _ _ _ parsed _ child =>
              exact .privateOutside _ _ _ parsed _ (fun answer =>
                ih answer totalRemaining indexRemaining (child answer))
          | privateIndex _ _ _ pair parsed positive _ child =>
              exact .privateIndex _ _ _ pair parsed positive _ (fun answer =>
                ih answer totalRemaining (indexRemaining - 1)
                  (child answer))

#print axioms total_limited_index_budget

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointIndexCutoff67


/-! Every marked joint H5 draw belongs to a private tag-5 index read. The
signing lifetime bounds these reads by L, while tag-6 randomizer draws are
unmarked and consume their own total-query budget. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointSharpLifetime67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedGraphIndexJointGlobal67
open GroupedBalancedGraphIndexJointIndexBudget67
open GroupedBalancedGraphIndexJointMarkHelpers67
open GroupedBalancedGraphIndexJointSharpHelpers67
open GroupedBalancedGraphIndexMarks67
open GroupedBalancedGraphIndexLift67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 30000
open scoped Classical

attribute [local irreducible] MarkedCredit
attribute [local irreducible] GroupedBalancedGraphIndexJoint67.compile

theorem compile_index_budget {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (graphCalls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests : Nat)
    (spent indexRemaining limit : Nat)
    (budget : IndexBudget indexRemaining view)
    (bounded : spent + indexRemaining ≤ limit) :
    MarkedCredit (fun _ : JointOutcome α => limit) spent
      (compile table view remaining state graphCalls
        signedMessages bad tests) := by
  induction budget generalizing remaining state graphCalls signedMessages
      bad tests spent with
  | done indexRemaining value =>
      simp only [GroupedBalancedGraphIndexJoint67.compile, MarkedCredit]
      omega
  | coin indexRemaining n next child ih =>
      rw [GroupedBalancedGraphIndexJoint67.compile]
      simp only [MarkedCredit]
      exact fun answer => ih answer remaining state graphCalls
        signedMessages bad tests spent bounded
  | sign indexRemaining index next child ih =>
      rw [GroupedBalancedGraphIndexJoint67.compile]
      exact ih _ remaining _ graphCalls signedMessages bad tests spent bounded
  | privateOutside indexRemaining input outside parsed next child ih =>
      rw [GroupedBalancedGraphIndexJoint67.compile]
      apply private_outside_credit input parsed
      intro answer updated
      exact ih answer remaining updated graphCalls signedMessages
        bad tests spent bounded
  | privateIndex indexRemaining input outside pair parsed positive next child ih =>
      rw [GroupedBalancedGraphIndexJoint67.compile]
      apply private_index_credit input pair parsed
      intro answer updated
      exact ih answer remaining updated
        graphCalls (insert pair.1 signedMessages) bad tests (spent + 1)
        (by omega)
  | hash indexRemaining input next child ih =>
      cases remaining with
      | zero =>
          rw [GroupedBalancedGraphIndexJoint67.compile]
          simp only [MarkedCredit]
          omega
      | succ remaining =>
          rw [GroupedBalancedGraphIndexJoint67.compile]
          apply public_hash_step_credit
          intro answer updated graphCalls bad tests
          exact ih answer remaining updated graphCalls signedMessages
            bad tests spent bounded

theorem global_marks_le_lifetime {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat)
    (budget : ∀ cache, IndexBudget LIFETIME (view cache)) :
    ∀ result ∈ support
      (SecurityIndexProgram.execute (global view remaining)),
      SecurityIndexTrace.marks result.2 ≤ LIFETIME := by
  have credit :
      MarkedCredit (fun _ : JointOutcome α => LIFETIME) 0
        (global view remaining) := by
    unfold global
    apply GroupedBalancedGraphIndexMarks67.unmarked_credit
    intro table
    change MarkedCredit (fun _ : JointOutcome α => LIFETIME) 0
      (compile table
        (view (GroupedBalancedGraphMonitorSetup67.cache table)) remaining
        (GroupedBalancedGraphMonitorSignBound67.initial
          (GroupedBalancedGraphMonitorSetup67.cache table))
        0 ∅ false 0)
    exact compile_index_budget table _ remaining _ 0 ∅ false 0
      0 LIFETIME LIFETIME (budget _) (by omega)
  intro result member
  have bound := marked_execute _ 0 _ credit result member
  simpa only [Nat.zero_add] using bound

#print axioms global_marks_le_lifetime

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointSharpLifetime67
