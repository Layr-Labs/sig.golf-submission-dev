import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTraceBudget67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTraceProjectBase67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTraceProjectSteps67. -/
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

def eraseOutcome {α : Type} (result : JointOutcome (α × Nat)) :
    JointOutcome α :=
  ⟨⟨result.value.value.map Prod.fst, result.value.remaining,
    result.value.state, result.value.graphCalls⟩,
    result.bad, result.tests⟩

def eraseRun {α : Type}
    (result : JointOutcome (α × Nat) × List SecurityIndexTrace.Entry) :
    JointOutcome α × List SecurityIndexTrace.Entry :=
  (eraseOutcome result.1, result.2)

noncomputable def projectDist {α : Type}
    (simulation : ProbComp
      (JointOutcome (α × Nat) × List SecurityIndexTrace.Entry)) :
    ProbComp (JointOutcome α × List SecurityIndexTrace.Entry) :=
  eraseRun <$> simulation

theorem project_unmarked {α β : Type} (program : ProbComp β)
    (marked : β → SecurityIndexProgram.Program (JointOutcome (α × Nat)))
    (plain : β → SecurityIndexProgram.Program (JointOutcome α))
    (next : ∀ answer,
      projectDist (SecurityIndexProgram.execute (marked answer)) =
        SecurityIndexProgram.execute (plain answer)) :
    projectDist
      (SecurityIndexProgram.execute (unmarked program marked)) =
    SecurityIndexProgram.execute (unmarked program plain) := by
  simp only [projectDist, execute_unmarked, map_bind]
  exact bind_congr next

theorem project_cachedDraw {α : Type}
    (residual : QueryCache HashSpec) (input : Query) (mark : Bool)
    (marked : BitVec 256 → QueryCache HashSpec →
      SecurityIndexProgram.Program (JointOutcome (α × Nat)))
    (plain : BitVec 256 → QueryCache HashSpec →
      SecurityIndexProgram.Program (JointOutcome α))
    (next : ∀ answer updated,
      projectDist (SecurityIndexProgram.execute (marked answer updated)) =
        SecurityIndexProgram.execute (plain answer updated)) :
    projectDist (SecurityIndexProgram.execute
      (cachedDraw residual input mark marked)) =
    SecurityIndexProgram.execute
      (cachedDraw residual input mark plain) := by
  cases cached : residual input with
  | some answer =>
      simpa only [cachedDraw, cached] using next answer residual
  | none =>
      simp only [cachedDraw, cached, SecurityIndexProgram.execute,
        projectDist, map_bind]
      apply bind_congr
      intro answer
      let updated := residual.cacheQuery input answer
      have h := next answer updated
      change eraseRun <$>
          ((fun result => (result.1,
            (mark, answer.extractLsb' 0 160)::result.2)) <$>
              SecurityIndexProgram.execute (marked answer updated)) =
        (fun result => (result.1,
          (mark, answer.extractLsb' 0 160)::result.2)) <$>
            SecurityIndexProgram.execute (plain answer updated)
      calc
        _ = (fun result => (result.1,
              (mark, answer.extractLsb' 0 160)::result.2)) <$>
              projectDist (SecurityIndexProgram.execute
                (marked answer updated)) := by
            simp only [projectDist, Functor.map_map, Function.comp_def,
              eraseRun]
        _ = _ := congrArg _ h

theorem project_ofGraphKeep {α β : Type} (table : PointTable)
    (cache : QueryCache PointSpec)
    (program : GroupedBalancedGraphMonitorProgram67.Program β)
    (marked : Outcome β →
      SecurityIndexProgram.Program (JointOutcome (α × Nat)))
    (plain : Outcome β → SecurityIndexProgram.Program (JointOutcome α))
    (next : ∀ result,
      projectDist (SecurityIndexProgram.execute (marked result)) =
        SecurityIndexProgram.execute (plain result)) :
    projectDist (SecurityIndexProgram.execute
      (ofGraphKeep table cache program marked)) =
    SecurityIndexProgram.execute
      (ofGraphKeep table cache program plain) := by
  simp only [projectDist, execute_ofGraphKeep, map_bind]
  exact bind_congr next

#print axioms project_unmarked
#print axioms project_cachedDraw
#print axioms project_ofGraphKeep

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

theorem project_privateHashStepOn {α : Type}
    (parsed : Option (Message × Bytes 32))
    (state : State) (input : Query) (signedMessages : Finset Message)
    (marked : BitVec 256 → State → Finset Message →
      SecurityIndexProgram.Program (JointOutcome (α × Nat)))
    (plain : BitVec 256 → State → Finset Message →
      SecurityIndexProgram.Program (JointOutcome α))
    (next : ∀ answer updated messages,
      projectDist (SecurityIndexProgram.execute
        (marked answer updated messages)) =
      SecurityIndexProgram.execute (plain answer updated messages)) :
    projectDist (SecurityIndexProgram.execute
      (privateHashStepOn parsed state input signedMessages marked)) =
    SecurityIndexProgram.execute
      (privateHashStepOn parsed state input signedMessages plain) := by
  cases parsed with
  | some pair =>
      change projectDist (SecurityIndexProgram.execute
          (cachedDraw state.residual input
            (decide (pair.1 ∉ signedMessages))
            (fun answer residual =>
              marked answer { state with residual := residual }
                (insert pair.1 signedMessages)))) =
        SecurityIndexProgram.execute
          (cachedDraw state.residual input
            (decide (pair.1 ∉ signedMessages))
            (fun answer residual =>
              plain answer { state with residual := residual }
                (insert pair.1 signedMessages)))
      exact project_cachedDraw _ _ _ _ _
        (fun answer residual => next answer _ _)
  | none =>
      change projectDist (SecurityIndexProgram.execute
          (unmarked ((randomOracle (spec := HashSpec) input).run state.residual)
            (fun result => marked result.1
              { state with residual := result.2 } signedMessages))) =
        SecurityIndexProgram.execute
          (unmarked ((randomOracle (spec := HashSpec) input).run state.residual)
            (fun result => plain result.1
              { state with residual := result.2 } signedMessages))
      exact project_unmarked _ _ _
        (fun result => next result.1 _ _)

theorem project_publicHashStepOn {α : Type}
    (parsed : Option (Message × Bytes 32)) (table : PointTable)
    (state : State) (input : Query) (calls : Nat)
    (bad : Bool) (tests : Nat)
    (marked : BitVec 256 → State → Nat → Bool → Nat →
      SecurityIndexProgram.Program (JointOutcome (α × Nat)))
    (plain : BitVec 256 → State → Nat → Bool → Nat →
      SecurityIndexProgram.Program (JointOutcome α))
    (next : ∀ answer updated calls' bad' tests',
      projectDist (SecurityIndexProgram.execute
        (marked answer updated calls' bad' tests')) =
      SecurityIndexProgram.execute
        (plain answer updated calls' bad' tests')) :
    projectDist (SecurityIndexProgram.execute
      (publicHashStepOn parsed table state input calls bad tests marked)) =
    SecurityIndexProgram.execute
      (publicHashStepOn parsed table state input calls bad tests plain) := by
  cases parsed with
  | some pair =>
      change projectDist (SecurityIndexProgram.execute
          (cachedDraw state.residual input false
            (fun answer residual =>
              marked answer { state with residual := residual }
                calls bad tests))) =
        SecurityIndexProgram.execute
          (cachedDraw state.residual input false
            (fun answer residual =>
              plain answer { state with residual := residual }
                calls bad tests))
      exact project_cachedDraw _ _ _ _ _
        (fun answer residual => next answer _ _ _ _)
  | none =>
      change projectDist (SecurityIndexProgram.execute
          (ofGraphKeep table state.exposed
            (GroupedBalancedGraphMonitorOracle67.publicStep
              state.exposed state.residual input
              (fun answer exposed residual =>
                .done (answer, exposed, residual)))
            (fun result =>
              let calls' := calls +
                if (GroupedBalancedGraphQuery67.locate input).isSome
                then 1 else 0
              marked result.value.1
                (opened state result.value.2.1 result.value.2.2)
                calls' (bad || result.bad) (tests+result.tests)))) =
        SecurityIndexProgram.execute
          (ofGraphKeep table state.exposed
            (GroupedBalancedGraphMonitorOracle67.publicStep
              state.exposed state.residual input
              (fun answer exposed residual =>
                .done (answer, exposed, residual)))
            (fun result =>
              let calls' := calls +
                if (GroupedBalancedGraphQuery67.locate input).isSome
                then 1 else 0
              plain result.value.1
                (opened state result.value.2.1 result.value.2.2)
                calls' (bad || result.bad) (tests+result.tests)))
      exact project_ofGraphKeep _ _ _ _ _
        (fun result => next result.value.1 _ _ _ _)

#print axioms project_privateHashStepOn
#print axioms project_publicHashStepOn

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTrace67
