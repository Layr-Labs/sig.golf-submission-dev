import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTraceProjectSteps67
import SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerGraphProjection67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTraceProjectCompile67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerAnnotated67. -/
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

theorem compile_project {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (calls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests secret : Nat) :
    projectDist (SecurityIndexProgram.execute
      (compile table (annotate view secret) remaining state calls
        signedMessages bad tests)) =
    SecurityIndexProgram.execute
      (compile table view remaining state calls signedMessages bad tests) := by
  induction view generalizing remaining state calls signedMessages bad tests
      secret with
  | done value =>
      simp only [annotate, GroupedBalancedGraphIndexJoint67.compile,
        SecurityIndexProgram.execute, projectDist, map_pure, eraseRun,
        eraseOutcome, Option.map_some]
  | coin n next ih =>
      simp only [annotate, GroupedBalancedGraphIndexJoint67.compile,
        SecurityIndexProgram.execute, projectDist, map_bind]
      exact bind_congr (fun answer => ih answer remaining state calls
        signedMessages bad tests secret)
  | sign index next ih =>
      simp only [annotate, GroupedBalancedGraphIndexJoint67.compile]
      exact ih _ remaining _ calls signedMessages bad tests secret
  | privateHash input outside next ih =>
      change projectDist (SecurityIndexProgram.execute
          (privateHashStepOn (SecurityIndexQuery.parse input)
            state input signedMessages
            (fun answer updated messages =>
              compile table (annotate (next answer) secret) remaining updated
                calls messages bad tests))) =
        SecurityIndexProgram.execute
          (privateHashStepOn (SecurityIndexQuery.parse input)
            state input signedMessages
            (fun answer updated messages =>
              compile table (next answer) remaining updated
                calls messages bad tests))
      exact project_privateHashStepOn _ _ _ _ _ _
        (fun answer updated messages =>
          ih answer remaining updated calls messages bad tests secret)
  | hash input next ih =>
      cases remaining with
      | zero =>
          simp only [annotate, GroupedBalancedGraphIndexJoint67.compile,
            SecurityIndexProgram.execute, projectDist, map_pure,
            eraseRun, eraseOutcome, Option.map_none]
      | succ remaining =>
          change projectDist (SecurityIndexProgram.execute
              (publicHashStepOn (SecurityIndexQuery.parse input)
                table state input calls bad tests
                (fun answer updated calls' bad' tests' =>
                  compile table (annotate (next answer)
                    (secret+secretCharge input)) remaining updated
                    calls' signedMessages bad' tests'))) =
            SecurityIndexProgram.execute
              (publicHashStepOn (SecurityIndexQuery.parse input)
                table state input calls bad tests
                (fun answer updated calls' bad' tests' =>
                  compile table (next answer) remaining updated
                    calls' signedMessages bad' tests'))
          exact project_publicHashStepOn _ _ _ _ _ _ _ _ _
            (fun answer updated calls' bad' tests' =>
              ih answer remaining updated calls' signedMessages bad' tests'
                (secret+secretCharge input))

#print axioms compile_project

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTrace67
end

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTrace67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
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

theorem global_project {α : Type}
    (view : QueryCache PointSpec → View α) (budget : Nat) :
    projectDist
      (SecurityIndexProgram.execute
        (global (fun cache => annotate (view cache) 0) budget)) =
    SecurityIndexProgram.execute (global view budget) := by
  unfold global
  apply project_unmarked
  intro table
  unfold start
  exact compile_project table
    (view (GroupedBalancedGraphMonitorSetup67.cache table)) budget
    (GroupedBalancedGraphMonitorSignBound67.initial
      (GroupedBalancedGraphMonitorSetup67.cache table))
    0 ∅ false 0 0

theorem global_event_project {α : Type}
    (view : QueryCache PointSpec → View α) (budget : Nat)
    (event : JointOutcome α × List SecurityIndexTrace.Entry → Prop) :
    Pr[event | SecurityIndexProgram.execute (global view budget)] =
    Pr[fun result => event (eraseRun result) |
      SecurityIndexProgram.execute
        (global (fun cache => annotate (view cache) 0) budget)] := by
  rw [← global_project view budget, projectDist, probEvent_map]
  rfl

theorem global_expected_project {α : Type}
    (view : QueryCache PointSpec → View α) (budget : Nat)
    (weight : JointOutcome α × List SecurityIndexTrace.Entry → ENNReal) :
    expectedValue (SecurityIndexProgram.execute (global view budget))
      weight =
    expectedValue
      (SecurityIndexProgram.execute
        (global (fun cache => annotate (view cache) 0) budget))
      (fun result => weight (eraseRun result)) := by
  rw [← global_project view budget, projectDist, expectedValue_map]

#print axioms global_project
#print axioms global_event_project
#print axioms global_expected_project

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTrace67


/-! The eager ideal event and all three query-class counters inhabit one
annotated joint graph/H5 simulation. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerAnnotated67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedPlantedEagerGraphProjection67
open GroupedBalancedPlantedEagerGlobalUnion67
open GroupedBalancedGraphInteraction67 SecurityGraphIdeal
open GroupedBalancedGraphIndexJointClassTrace67
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def annotatedJointGlobal {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) : ProbComp
      (GroupedBalancedGraphIndexJoint67.JointOutcome
        ((Option α × List GroupedBalancedGameQueryTrace67.Action) × Nat) ×
        List SecurityIndexTrace.Entry) := do
  let answers ← $ᵗ PrivateTable
  SecurityIndexProgram.execute
    (GroupedBalancedGraphIndexJointGlobal67.global
      (fun cache => annotate (viewOf answers interaction budget cache) 0)
      budget)

theorem jointGlobal_project {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    GroupedBalancedPlantedEagerGraphProjection67.jointGlobal
      interaction budget =
      eraseRun <$> annotatedJointGlobal interaction budget := by
  unfold GroupedBalancedPlantedEagerGraphProjection67.jointGlobal
    annotatedJointGlobal
  rw [map_bind]
  apply bind_congr
  intro answers
  exact (global_project (viewOf answers interaction budget) budget).symm

theorem eager_global_le_annotated_union {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat)
    (event : (Option α ×
      List GroupedBalancedGameQueryTrace67.Action) → Prop) :
    Pr[event | eagerGlobal interaction budget] ≤
      Pr[fun result =>
        let plain := eraseRun result
        plain.1.bad = true ∨
          GroupedBalancedPlantedEagerUnion67.optionEvent event
            plain.1.value.value |
        annotatedJointGlobal interaction budget] := by
  have bound := eager_global_le_joint_union interaction budget event
  rw [jointGlobal_project, probEvent_map] at bound
  exact bound

#print axioms jointGlobal_project
#print axioms eager_global_le_annotated_union

end SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerAnnotated67
