import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTraceHashEligible67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTraceHashOther67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTraceCostSmall67. -/
section
namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTrace67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedGraphIndexJointGlobal67
open GroupedBalancedGraphIndexJointTotalView67
open GroupedBalancedGraphIndexJointSumCredit67
open GroupedBalancedGraphIndexKeep67
open GroupedBalancedGraphIndexLift67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

attribute [local irreducible] SumCredit
attribute [local irreducible] GroupedBalancedGraphIndexJoint67.compile

theorem hash_other_step {α : Type} (table : PointTable)
    (input : Query) (next : BitVec 256 → View α)
    (remaining : Nat) (state : State) (calls : Nat)
    (signedMessages : Finset Message) (bad : Bool)
    (tests secret spent totalRemaining limit : Nat)
    (other : ¬SecuritySeparation.SecretKeyEligible input)
    (positive : 0 < totalRemaining)
    (bounded : spent + calls + secret + totalRemaining ≤ limit)
    (ih : ∀ answer updated calls' bad' tests' spent',
      spent' + calls' + (secret + secretCharge input) +
        (totalRemaining - 1) ≤ limit →
      SumCredit score limit spent'
        (compile table (annotate (next answer)
          (secret + secretCharge input)) remaining
          updated calls' signedMessages bad' tests')) :
    SumCredit score limit spent
      (compile table (annotate (.hash input next) secret) (remaining+1)
        state calls signedMessages bad tests) := by
  have charge : secretCharge input = 0 := by
    simp [secretCharge,other]
  rw [annotate, GroupedBalancedGraphIndexJoint67.compile]
  cases parsed : SecurityIndexQuery.parse input with
  | some pair =>
      change SumCredit score limit spent
        (cachedDraw state.residual input false
          (fun answer residual =>
            compile table
              (annotate (next answer) (secret+secretCharge input))
              remaining { state with residual := residual } calls
              signedMessages bad tests))
      simp only [charge,Nat.add_zero]
      apply cached_draw_one
      intro answer updated
      have nextBound : (spent+1) + calls +
          (secret + secretCharge input) +
          (totalRemaining-1) ≤ limit := by
        rw [charge]
        omega
      simpa only [charge,Nat.add_zero] using
        ih answer _ calls bad tests (spent+1) nextBound
  | none =>
      change SumCredit score limit spent
        (ofGraphKeep table state.exposed
          (GroupedBalancedGraphMonitorOracle67.publicStep
            state.exposed state.residual input
            (fun answer exposed residual =>
              .done (answer, exposed, residual)))
          (fun result =>
            let calls' := calls +
              if (GroupedBalancedGraphQuery67.locate input).isSome
              then 1 else 0
            compile table
              (annotate (next result.value.1)
                (secret+secretCharge input)) remaining
              (opened state result.value.2.1 result.value.2.2)
              calls' signedMessages (bad || result.bad)
              (tests+result.tests)))
      simp only [charge,Nat.add_zero]
      apply of_graph_keep_credit
      intro result
      have nextBound : spent +
          (calls + if (GroupedBalancedGraphQuery67.locate input).isSome
            then 1 else 0) +
          (secret + secretCharge input) +
          (totalRemaining-1) ≤ limit := by
        rw [charge]
        split <;> omega
      simpa only [charge,Nat.add_zero] using
        ih result.value.1 _ _ _ _ spent nextBound

#print axioms hash_other_step

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTrace67
end

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTraceHashDispatch67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTraceCostSmall67. -/
section
namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTrace67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedGraphIndexJointGlobal67
open GroupedBalancedGraphIndexJointTotalView67
open GroupedBalancedGraphIndexJointSumCredit67
open GroupedBalancedGraphIndexKeep67
open GroupedBalancedGraphIndexLift67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

attribute [local irreducible] SumCredit
attribute [local irreducible] GroupedBalancedGraphIndexJoint67.compile

theorem hash_step {α : Type} (table : PointTable)
    (input : Query) (next : BitVec 256 → View α)
    (remaining : Nat) (state : State) (calls : Nat)
    (signedMessages : Finset Message) (bad : Bool)
    (tests secret spent totalRemaining limit : Nat)
    (positive : 0 < totalRemaining)
    (bounded : spent + calls + secret + totalRemaining ≤ limit)
    (ih : ∀ answer updated calls' bad' tests' spent',
      spent' + calls' + (secret + secretCharge input) +
        (totalRemaining - 1) ≤ limit →
      SumCredit score limit spent'
        (compile table (annotate (next answer)
          (secret + secretCharge input)) (remaining - 1)
          updated calls' signedMessages bad' tests')) :
    SumCredit score limit spent
      (compile table (annotate (.hash input next) secret) remaining
        state calls signedMessages bad tests) := by
  cases remaining with
  | zero =>
      rw [annotate, GroupedBalancedGraphIndexJoint67.compile]
      simp only [SumCredit, score, secretCount, Option.map_none,
        Option.getD_none, Nat.add_zero]
      omega
  | succ remaining =>
      by_cases eligible : SecuritySeparation.SecretKeyEligible input
      · have next : ∀ answer updated calls' bad' tests' spent',
            spent' + calls' + (secret + secretCharge input) +
              (totalRemaining - 1) ≤ limit →
            SumCredit score limit spent'
              (compile table (annotate (next answer)
                (secret + secretCharge input)) remaining
                updated calls' signedMessages bad' tests') := by
          intro answer updated calls' bad' tests' spent' bound
          simpa only [Nat.add_sub_cancel_right] using
            ih answer updated calls' bad' tests' spent' bound
        exact hash_eligible_step table input _ remaining state calls
          signedMessages bad tests secret spent totalRemaining limit
          eligible positive bounded next
      · have next : ∀ answer updated calls' bad' tests' spent',
            spent' + calls' + (secret + secretCharge input) +
              (totalRemaining - 1) ≤ limit →
            SumCredit score limit spent'
              (compile table (annotate (next answer)
                (secret + secretCharge input)) remaining
                updated calls' signedMessages bad' tests') := by
          intro answer updated calls' bad' tests' spent' bound
          simpa only [Nat.add_sub_cancel_right] using
            ih answer updated calls' bad' tests' spent' bound
        exact hash_other_step table input _ remaining state calls
          signedMessages bad tests secret spent totalRemaining limit
          eligible positive bounded next

#print axioms hash_step

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTrace67
end

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTrace67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedGraphIndexJointGlobal67
open GroupedBalancedGraphIndexJointTotalView67
open GroupedBalancedGraphIndexJointSumCredit67
open GroupedBalancedGraphIndexKeep67
open GroupedBalancedGraphIndexLift67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

attribute [local irreducible] SumCredit
attribute [local irreducible] GroupedBalancedGraphIndexJoint67.compile

theorem compile_class_cost {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (calls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests : Nat) (secret spent totalRemaining limit : Nat)
    (budget : TotalBudget totalRemaining view)
    (bounded : spent + calls + secret + totalRemaining ≤ limit) :
    SumCredit score limit spent
      (compile table (annotate view secret) remaining state calls
        signedMessages bad tests) := by
  induction view generalizing remaining state calls signedMessages bad tests
      secret spent totalRemaining with
  | done value =>
      simp only [annotate, GroupedBalancedGraphIndexJoint67.compile,
        SumCredit, score, secretCount, Option.map_some, Option.getD_some]
      omega
  | coin n next ih =>
      change ∀ answer, TotalBudget totalRemaining (next answer) at budget
      rw [annotate, GroupedBalancedGraphIndexJoint67.compile]
      simp only [SumCredit]
      exact fun answer => ih answer remaining state calls signedMessages
        bad tests secret spent totalRemaining (budget answer) bounded
  | sign index next ih =>
      change ∀ answer, TotalBudget totalRemaining (next answer) at budget
      rw [annotate, GroupedBalancedGraphIndexJoint67.compile]
      exact ih _ remaining _ calls signedMessages bad tests secret spent
        totalRemaining (budget _) bounded
  | privateHash input outside next ih =>
      change 0 < totalRemaining ∧ ∀ answer,
        TotalBudget (totalRemaining - 1) (next answer) at budget
      exact private_step table input outside next remaining state calls
        signedMessages bad tests secret spent totalRemaining limit budget.1
        bounded
        (fun answer updated messages spent' nextBound =>
          ih answer remaining updated calls messages bad tests secret spent'
            (totalRemaining-1) (budget.2 answer) nextBound)
  | hash input next ih =>
      change 0 < totalRemaining ∧ ∀ answer,
        TotalBudget (totalRemaining - 1) (next answer) at budget
      exact hash_step table input next remaining state calls signedMessages
        bad tests secret spent totalRemaining limit budget.1 bounded
        (fun answer updated calls' bad' tests' spent' nextBound =>
          ih answer (remaining-1) updated calls' signedMessages bad' tests'
            (secret+secretCharge input) spent' (totalRemaining-1)
            (budget.2 answer) nextBound)

theorem global_class_cost {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat)
    (budget : ∀ cache, TotalBudget remaining (view cache)) :
    ∀ result ∈ support
      (SecurityIndexProgram.execute
        (global (fun cache => annotate (view cache) 0) remaining)),
      result.1.value.graphCalls + secretCount result.1 +
        result.2.length ≤ remaining := by
  have credit : SumCredit score remaining 0
      (global (fun cache => annotate (view cache) 0) remaining) := by
    unfold global
    apply unmarked_credit
    intro table
    change SumCredit score remaining 0
      (compile table
        (annotate (view (GroupedBalancedGraphMonitorSetup67.cache table)) 0)
        remaining
        (GroupedBalancedGraphMonitorSignBound67.initial
          (GroupedBalancedGraphMonitorSetup67.cache table))
        0 ∅ false 0)
    exact compile_class_cost table _ remaining _ 0 ∅ false 0
      0 0 remaining remaining (budget _) (by omega)
  intro result member
  have bound := sum_execute score remaining 0 _ credit result member
  simpa only [Nat.zero_add,score,Nat.add_assoc,Nat.add_comm,
    Nat.add_left_comm] using bound

#print axioms global_class_cost

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTrace67
