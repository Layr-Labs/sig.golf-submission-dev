import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTrace67


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

theorem private_step {α : Type} (table : PointTable)
    (input : Query) (outside : GroupedBalancedGraphQuery67.locate input = none)
    (next : BitVec 256 → View α) (remaining : Nat) (state : State)
    (calls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests secret spent totalRemaining limit : Nat)
    (positive : 0 < totalRemaining)
    (bounded : spent + calls + secret + totalRemaining ≤ limit)
    (ih : ∀ answer updated messages spent',
      spent' + calls + secret + (totalRemaining - 1) ≤ limit →
      SumCredit score limit spent'
        (compile table (annotate (next answer) secret) remaining updated
          calls messages bad tests)) :
    SumCredit score limit spent
      (compile table (annotate (.privateHash input outside next) secret)
        remaining state calls signedMessages bad tests) := by
  rw [annotate, GroupedBalancedGraphIndexJoint67.compile]
  cases parsed : SecurityIndexQuery.parse input with
  | some pair =>
      change SumCredit score limit spent
        (cachedDraw state.residual input (decide (pair.1 ∉ signedMessages))
          (fun answer residual =>
            compile table (annotate (next answer) secret) remaining
              { state with residual := residual } calls
              (insert pair.1 signedMessages) bad tests))
      apply cached_draw_one
      intro answer updated
      exact ih answer _ _ (spent+1) (by omega)
  | none =>
      change SumCredit score limit spent
        (unmarked ((randomOracle (spec := HashSpec) input).run state.residual)
          (fun result =>
            compile table (annotate (next result.1) secret) remaining
              { state with residual := result.2 } calls signedMessages
              bad tests))
      apply unmarked_credit
      intro result
      exact ih result.1 _ _ spent (by omega)

#print axioms private_step

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTrace67


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

theorem hash_eligible_step {α : Type} (table : PointTable)
    (input : Query) (next : BitVec 256 → View α)
    (remaining : Nat) (state : State) (calls : Nat)
    (signedMessages : Finset Message) (bad : Bool)
    (tests secret spent totalRemaining limit : Nat)
    (eligible : SecuritySeparation.SecretKeyEligible input)
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
  have parsedNone :=
    GroupedBalancedQueryClasses67.legacy_eligible_parse_none input eligible
  have locatedNone :=
    GroupedBalancedQueryClasses67.legacy_eligible_locate_none input eligible
  have charge : secretCharge input = 1 := by
    simp [secretCharge,eligible]
  rw [annotate, GroupedBalancedGraphIndexJoint67.compile, parsedNone]
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
  apply of_graph_keep_credit
  intro result
  have nextBound : spent + calls +
      (secret + secretCharge input) + (totalRemaining - 1) ≤ limit := by
    rw [charge]
    omega
  have noGraph : calls +
      (if (GroupedBalancedGraphQuery67.locate input).isSome
       then 1 else 0) = calls := by
    simp [locatedNone]
  change SumCredit score limit spent
    (compile table (annotate (next result.value.1)
      (secret+secretCharge input)) remaining
      (opened state result.value.2.1 result.value.2.2)
      (calls + if (GroupedBalancedGraphQuery67.locate input).isSome
        then 1 else 0)
      signedMessages (bad || result.bad) (tests+result.tests))
  rw [noGraph]
  exact ih result.value.1
      (opened state result.value.2.1 result.value.2.2)
      calls (bad || result.bad) (tests+result.tests)
      spent nextBound

#print axioms hash_eligible_step

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTrace67
