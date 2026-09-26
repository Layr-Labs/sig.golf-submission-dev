import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTraceProjectSteps67
import SigGolfCandidate.Hypertree.GroupedBalancedGameViewLoggedBridge67

/-! Natural mapping of the terminal value through the joint graph/H5 runner. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointMapView67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedGraphIndexJointGlobal67
open GroupedBalancedGraphIndexKeep67
open GroupedBalancedGraphIndexLift67
open GroupedBalancedGameViewLoggedBridge67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

def mapOutcome {α β : Type} (f : α → β) (result : JointOutcome α) :
    JointOutcome β :=
  ⟨⟨result.value.value.map f, result.value.remaining,
    result.value.state, result.value.graphCalls⟩,
    result.bad, result.tests⟩

def mapRun {α β : Type} (f : α → β)
    (result : JointOutcome α × List SecurityIndexTrace.Entry) :
    JointOutcome β × List SecurityIndexTrace.Entry :=
  (mapOutcome f result.1, result.2)

noncomputable def mapDist {α β : Type} (f : α → β)
    (simulation : ProbComp
      (JointOutcome α × List SecurityIndexTrace.Entry)) :
    ProbComp (JointOutcome β × List SecurityIndexTrace.Entry) :=
  mapRun f <$> simulation

private theorem map_unmarked {α β γ : Type} (f : α → β)
    (program : ProbComp γ)
    (before : γ → SecurityIndexProgram.Program (JointOutcome α))
    (after : γ → SecurityIndexProgram.Program (JointOutcome β))
    (next : ∀ answer,
      mapDist f (SecurityIndexProgram.execute (before answer)) =
        SecurityIndexProgram.execute (after answer)) :
    mapDist f
      (SecurityIndexProgram.execute (unmarked program before)) =
    SecurityIndexProgram.execute (unmarked program after) := by
  simp only [mapDist, execute_unmarked, map_bind]
  exact bind_congr next

private theorem map_cachedDraw {α β : Type} (f : α → β)
    (residual : QueryCache HashSpec) (input : Query) (mark : Bool)
    (before : BitVec 256 → QueryCache HashSpec →
      SecurityIndexProgram.Program (JointOutcome α))
    (after : BitVec 256 → QueryCache HashSpec →
      SecurityIndexProgram.Program (JointOutcome β))
    (next : ∀ answer updated,
      mapDist f (SecurityIndexProgram.execute (before answer updated)) =
        SecurityIndexProgram.execute (after answer updated)) :
    mapDist f (SecurityIndexProgram.execute
      (cachedDraw residual input mark before)) =
    SecurityIndexProgram.execute
      (cachedDraw residual input mark after) := by
  cases cached : residual input with
  | some answer =>
      simpa only [cachedDraw, cached] using next answer residual
  | none =>
      simp only [cachedDraw, cached, SecurityIndexProgram.execute,
        mapDist, map_bind]
      apply bind_congr
      intro answer
      let updated := residual.cacheQuery input answer
      have h := next answer updated
      change mapRun f <$>
          ((fun result => (result.1,
            (mark, answer.extractLsb' 0 160)::result.2)) <$>
              SecurityIndexProgram.execute (before answer updated)) =
        (fun result => (result.1,
          (mark, answer.extractLsb' 0 160)::result.2)) <$>
            SecurityIndexProgram.execute (after answer updated)
      calc
        _ = (fun result => (result.1,
              (mark, answer.extractLsb' 0 160)::result.2)) <$>
              mapDist f (SecurityIndexProgram.execute
                (before answer updated)) := by
            simp only [mapDist, Functor.map_map, Function.comp_def,
              mapRun]
        _ = _ := congrArg _ h

private theorem map_ofGraphKeep {α β γ : Type} (f : α → β)
    (table : PointTable) (cache : QueryCache PointSpec)
    (program : GroupedBalancedGraphMonitorProgram67.Program γ)
    (before : Outcome γ →
      SecurityIndexProgram.Program (JointOutcome α))
    (after : Outcome γ →
      SecurityIndexProgram.Program (JointOutcome β))
    (next : ∀ result,
      mapDist f (SecurityIndexProgram.execute (before result)) =
        SecurityIndexProgram.execute (after result)) :
    mapDist f (SecurityIndexProgram.execute
      (ofGraphKeep table cache program before)) =
    SecurityIndexProgram.execute
      (ofGraphKeep table cache program after) := by
  simp only [mapDist, execute_ofGraphKeep, map_bind]
  exact bind_congr next

private theorem map_privateHashStepOn {α β : Type} (f : α → β)
    (parsed : Option (Message × Bytes 32))
    (state : State) (input : Query) (signedMessages : Finset Message)
    (before : BitVec 256 → State → Finset Message →
      SecurityIndexProgram.Program (JointOutcome α))
    (after : BitVec 256 → State → Finset Message →
      SecurityIndexProgram.Program (JointOutcome β))
    (next : ∀ answer updated messages,
      mapDist f (SecurityIndexProgram.execute
        (before answer updated messages)) =
      SecurityIndexProgram.execute (after answer updated messages)) :
    mapDist f (SecurityIndexProgram.execute
      (privateHashStepOn parsed state input signedMessages before)) =
    SecurityIndexProgram.execute
      (privateHashStepOn parsed state input signedMessages after) := by
  cases parsed with
  | some pair =>
      change mapDist f (SecurityIndexProgram.execute
          (cachedDraw state.residual input
            (decide (pair.1 ∉ signedMessages))
            (fun answer residual =>
              before answer { state with residual := residual }
                (insert pair.1 signedMessages)))) =
        SecurityIndexProgram.execute
          (cachedDraw state.residual input
            (decide (pair.1 ∉ signedMessages))
            (fun answer residual =>
              after answer { state with residual := residual }
                (insert pair.1 signedMessages)))
      exact map_cachedDraw f _ _ _ _ _
        (fun answer residual => next answer _ _)
  | none =>
      change mapDist f (SecurityIndexProgram.execute
          (unmarked ((randomOracle (spec := HashSpec) input).run state.residual)
            (fun result => before result.1
              { state with residual := result.2 } signedMessages))) =
        SecurityIndexProgram.execute
          (unmarked ((randomOracle (spec := HashSpec) input).run state.residual)
            (fun result => after result.1
              { state with residual := result.2 } signedMessages))
      exact map_unmarked f _ _ _
        (fun result => next result.1 _ _)

private theorem map_publicHashStepOn {α β : Type} (f : α → β)
    (parsed : Option (Message × Bytes 32)) (table : PointTable)
    (state : State) (input : Query) (calls : Nat)
    (bad : Bool) (tests : Nat)
    (before : BitVec 256 → State → Nat → Bool → Nat →
      SecurityIndexProgram.Program (JointOutcome α))
    (after : BitVec 256 → State → Nat → Bool → Nat →
      SecurityIndexProgram.Program (JointOutcome β))
    (next : ∀ answer updated calls' bad' tests',
      mapDist f (SecurityIndexProgram.execute
        (before answer updated calls' bad' tests')) =
      SecurityIndexProgram.execute
        (after answer updated calls' bad' tests')) :
    mapDist f (SecurityIndexProgram.execute
      (publicHashStepOn parsed table state input calls bad tests before)) =
    SecurityIndexProgram.execute
      (publicHashStepOn parsed table state input calls bad tests after) := by
  cases parsed with
  | some pair =>
      change mapDist f (SecurityIndexProgram.execute
          (cachedDraw state.residual input false
            (fun answer residual =>
              before answer { state with residual := residual }
                calls bad tests))) =
        SecurityIndexProgram.execute
          (cachedDraw state.residual input false
            (fun answer residual =>
              after answer { state with residual := residual }
                calls bad tests))
      exact map_cachedDraw f _ _ _ _ _
        (fun answer residual => next answer _ _ _ _)
  | none =>
      change mapDist f (SecurityIndexProgram.execute
          (ofGraphKeep table state.exposed
            (GroupedBalancedGraphMonitorOracle67.publicStep
              state.exposed state.residual input
              (fun answer exposed residual =>
                .done (answer, exposed, residual)))
            (fun result =>
              let calls' := calls +
                if (GroupedBalancedGraphQuery67.locate input).isSome
                then 1 else 0
              before result.value.1
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
              after result.value.1
                (opened state result.value.2.1 result.value.2.2)
                calls' (bad || result.bad) (tests+result.tests)))
      exact map_ofGraphKeep f _ _ _ _ _
        (fun result => next result.value.1 _ _ _ _)

theorem compile_mapView {α β : Type} (f : α → β) (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (calls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests : Nat) :
    mapDist f (SecurityIndexProgram.execute
      (compile table view remaining state calls signedMessages bad tests)) =
    SecurityIndexProgram.execute
      (compile table (mapView f view) remaining state calls
        signedMessages bad tests) := by
  induction view generalizing remaining state calls signedMessages bad tests with
  | done value =>
      simp only [mapView, GroupedBalancedGraphIndexJoint67.compile,
        SecurityIndexProgram.execute, mapDist, map_pure,
        mapRun, mapOutcome, Option.map_some]
  | coin n next ih =>
      simp only [mapView, GroupedBalancedGraphIndexJoint67.compile,
        SecurityIndexProgram.execute, mapDist, map_bind]
      exact bind_congr (fun answer => ih answer remaining state calls
        signedMessages bad tests)
  | sign index next ih =>
      simp only [mapView, GroupedBalancedGraphIndexJoint67.compile]
      exact ih _ remaining _ calls signedMessages bad tests
  | privateHash input outside next ih =>
      change mapDist f (SecurityIndexProgram.execute
          (privateHashStepOn (SecurityIndexQuery.parse input)
            state input signedMessages
            (fun answer updated messages =>
              compile table (next answer) remaining updated
                calls messages bad tests))) =
        SecurityIndexProgram.execute
          (privateHashStepOn (SecurityIndexQuery.parse input)
            state input signedMessages
            (fun answer updated messages =>
              compile table (mapView f (next answer)) remaining updated
                calls messages bad tests))
      exact map_privateHashStepOn f _ _ _ _ _ _
        (fun answer updated messages =>
          ih answer remaining updated calls messages bad tests)
  | hash input next ih =>
      cases remaining with
      | zero =>
          simp only [mapView, GroupedBalancedGraphIndexJoint67.compile,
            SecurityIndexProgram.execute, mapDist, map_pure,
            mapRun, mapOutcome, Option.map_none]
      | succ remaining =>
          change mapDist f (SecurityIndexProgram.execute
              (publicHashStepOn (SecurityIndexQuery.parse input)
                table state input calls bad tests
                (fun answer updated calls' bad' tests' =>
                  compile table (next answer) remaining updated
                    calls' signedMessages bad' tests'))) =
            SecurityIndexProgram.execute
              (publicHashStepOn (SecurityIndexQuery.parse input)
                table state input calls bad tests
                (fun answer updated calls' bad' tests' =>
                  compile table (mapView f (next answer)) remaining updated
                    calls' signedMessages bad' tests'))
          exact map_publicHashStepOn f _ _ _ _ _ _ _ _ _
            (fun answer updated calls' bad' tests' =>
              ih answer remaining updated calls' signedMessages bad' tests')

theorem global_mapView {α β : Type} (f : α → β)
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    mapDist f (SecurityIndexProgram.execute (global view remaining)) =
    SecurityIndexProgram.execute
      (global (fun cache => mapView f (view cache)) remaining) := by
  unfold global
  apply map_unmarked
  intro table
  unfold start
  exact compile_mapView f table
    (view (GroupedBalancedGraphMonitorSetup67.cache table)) remaining
    (GroupedBalancedGraphMonitorSignBound67.initial
      (GroupedBalancedGraphMonitorSetup67.cache table))
    0 ∅ false 0

#print axioms global_mapView

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointMapView67
