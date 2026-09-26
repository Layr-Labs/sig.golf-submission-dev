import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAuditMonotone67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledJoint67
import SigGolfCandidate.Hypertree.GroupedBalancedGameViewLoggedBridge67


/-! A parsed private H5 query records its message before any continuation. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAuditSign67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledAuditMonotone67
open GroupedBalancedIndexLabeledJoint67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem private_sign_present {α : Type}
    (state : GroupedBalancedGraphMonitorSignCompiler67.State)
    (input : Query) (pair : Message × Bytes 32)
    (signedMessages : Finset Message)
    (next : BitVec 256 →
      GroupedBalancedGraphMonitorSignCompiler67.State →
      Finset Message → Program α)
    (audit : Audit) (result : (α × List Draw) × Audit)
    (member : result ∈ support (run
      (privateHashStepOn (some pair) state input signedMessages next) audit)) :
    pair.1 ∈ result.2.signedMessages := by
  cases cached : state.residual input with
  | some answer =>
      simp only [privateHashStepOn,
        GroupedBalancedIndexLabeledLift67.cachedDraw, cached, run] at member
      exact run_signed_mem _ (signStep audit pair) result pair.1
        (by simp [signStep])
        member
  | none =>
      simp only [privateHashStepOn,
        GroupedBalancedIndexLabeledLift67.cachedDraw, cached,
        run, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      simp only [support_map, Set.mem_image] at member
      obtain ⟨child, childMember, same⟩ := member
      have present : pair.1 ∈
          (signStep
            { audit with
              h5cache := audit.h5cache.cacheQuery input answer
              draws := audit.draws ++
                [(input, (decide (pair.1 ∉ signedMessages),
                  answer.extractLsb' 0 160))] }
            pair).signedMessages := by
        simp [signStep]
      have childPresent := run_signed_mem _ _ child pair.1 present childMember
      have auditEq := congrArg (fun x : (α × List Draw) × Audit => x.2) same
      rw [← auditEq]
      exact childPresent

#print axioms private_sign_present

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAuditSign67



/-! Mapping a terminal value leaves H5 draws and the signed-message audit intact. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledMapProgram67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def mapProgram {α β : Type} (f : α → β) : Program α → Program β
  | .pure value => .pure (f value)
  | .draw input mark next =>
      .draw input mark (fun answer => mapProgram f (next answer))
  | .recordPublic pair next => .recordPublic pair (mapProgram f next)
  | .recordSign pair next => .recordSign pair (mapProgram f next)
  | .coin n next => .coin n (fun answer => mapProgram f (next answer))

def mapRun {α β : Type} (f : α → β)
    (result : (α × List Draw) × Audit) :
    (β × List Draw) × Audit := ((f result.1.1, result.1.2), result.2)

theorem run_mapProgram {α β : Type} (f : α → β)
    (program : Program α) (audit : Audit) :
    mapRun f <$> run program audit = run (mapProgram f program) audit := by
  induction program generalizing audit with
  | pure value => rfl
  | recordPublic pair next ih =>
      exact ih (publicStep audit pair)
  | recordSign pair next ih =>
      exact ih (signStep audit pair)
  | coin n next ih =>
      simp only [run, mapProgram, map_bind]
      exact bind_congr fun answer => ih answer audit
  | draw input mark next ih =>
      simp only [run, mapProgram, map_bind]
      apply bind_congr
      intro answer
      rw [← ih answer
        { audit with
          h5cache := audit.h5cache.cacheQuery input answer
          draws := audit.draws ++
            [(input, (mark, answer.extractLsb' 0 160))] }]
      simp only [Functor.map_map, Function.comp_def, mapRun]

#print axioms run_mapProgram

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledMapProgram67


/-! Terminal-value naturality for the input-labelled graph/H5 compiler. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledMapView67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledMapProgram67
open GroupedBalancedIndexLabeledJoint67
open GroupedBalancedGameViewLoggedBridge67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

def mapOutcome {α β : Type} (f : α → β)
    (result : GroupedBalancedGraphIndexJoint67.JointOutcome α) :
    GroupedBalancedGraphIndexJoint67.JointOutcome β :=
  ⟨⟨result.value.value.map f, result.value.remaining,
    result.value.state, result.value.graphCalls⟩,
    result.bad, result.tests⟩

theorem map_unmarked {α β γ : Type} (f : α → β)
    (program : ProbComp γ) (next : γ → Program α) :
    mapProgram f (GroupedBalancedIndexLabeledLift67.unmarked program next) =
      GroupedBalancedIndexLabeledLift67.unmarked program
        (fun value => mapProgram f (next value)) := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind n resume ih =>
      simp only [GroupedBalancedIndexLabeledLift67.unmarked, mapProgram]
      exact congrArg _ (funext fun answer => ih answer)

theorem map_cachedDraw {α β : Type} (f : α → β)
    (residual : QueryCache HashSpec) (input : Query) (mark : Bool)
    (next : BitVec 256 → QueryCache HashSpec → Program α) :
    mapProgram f
      (GroupedBalancedIndexLabeledLift67.cachedDraw residual input mark next) =
      GroupedBalancedIndexLabeledLift67.cachedDraw residual input mark
        (fun answer residual => mapProgram f (next answer residual)) := by
  cases present : residual input <;>
    simp only [GroupedBalancedIndexLabeledLift67.cachedDraw,
      present, mapProgram]

theorem map_ofGraphKeep {α β γ : Type} (f : α → β)
    (table : PointTable) (cache : QueryCache PointSpec)
    (program : GroupedBalancedGraphMonitorProgram67.Program γ)
    (next : GroupedBalancedGraphMonitorProgram67.Outcome γ → Program α) :
    mapProgram f
      (GroupedBalancedIndexLabeledLift67.ofGraphKeep table cache program next) =
      GroupedBalancedIndexLabeledLift67.ofGraphKeep table cache program
        (fun result => mapProgram f (next result)) := by
  induction program generalizing cache next with
  | done value => rfl
  | reveal point resume ih => exact ih (table point) _ _
  | guess point value resume ih => exact ih cache _
  | coin n resume ih =>
      simp only [GroupedBalancedIndexLabeledLift67.ofGraphKeep,
        mapProgram]
      exact congrArg _ (funext fun answer => ih answer cache next)
  | bits resume ih =>
      rw [GroupedBalancedIndexLabeledLift67.ofGraphKeep, map_unmarked]
      change _ = GroupedBalancedIndexLabeledLift67.unmarked ($ᵗ BitVec 256)
        (fun answer => GroupedBalancedIndexLabeledLift67.ofGraphKeep table cache
          (resume answer) (fun result => mapProgram f (next result)))
      exact congrArg _ (funext fun answer => ih answer cache next)
  | collision target resume ih =>
      rw [GroupedBalancedIndexLabeledLift67.ofGraphKeep, map_unmarked]
      change _ = GroupedBalancedIndexLabeledLift67.unmarked ($ᵗ BitVec 256)
        (fun answer => GroupedBalancedIndexLabeledLift67.ofGraphKeep table cache
          (resume answer) (fun result => mapProgram f
            (next (GroupedBalancedGraphMonitorProgram67.addTest
              (decide (truncate answer = target)) result))))
      exact congrArg _ (funext fun answer => ih answer cache _)

theorem map_privateHashStepOn {α β : Type} (f : α → β)
    (parsed : Option (Message × Bytes 32))
    (state : State) (input : Query) (signedMessages : Finset Message)
    (next : BitVec 256 → State → Finset Message → Program α) :
    mapProgram f
      (privateHashStepOn parsed state input signedMessages next) =
      privateHashStepOn parsed state input signedMessages
        (fun answer state messages => mapProgram f (next answer state messages)) := by
  cases parsed with
  | none =>
      simp only [privateHashStepOn]
      exact map_unmarked f _ _
  | some pair =>
      simp only [privateHashStepOn, map_cachedDraw, mapProgram]

theorem map_publicHashStepOn {α β : Type} (f : α → β)
    (parsed : Option (Message × Bytes 32)) (table : PointTable)
    (state : State) (input : Query) (calls : Nat)
    (bad : Bool) (tests : Nat)
    (next : BitVec 256 → State → Nat → Bool → Nat → Program α) :
    mapProgram f
      (publicHashStepOn parsed table state input calls bad tests next) =
      publicHashStepOn parsed table state input calls bad tests
        (fun answer state calls bad tests =>
          mapProgram f (next answer state calls bad tests)) := by
  cases parsed with
  | none =>
      simp only [publicHashStepOn, map_ofGraphKeep]
  | some pair =>
      simp only [publicHashStepOn]
      split <;> simp only [mapProgram, map_cachedDraw]

theorem compile_mapView {α β : Type} (f : α → β) (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (calls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests : Nat) :
    mapProgram (mapOutcome f)
      (compile table view remaining state calls signedMessages bad tests) =
      compile table (mapView f view) remaining state calls
        signedMessages bad tests := by
  induction view generalizing remaining state calls signedMessages bad tests with
  | done value => rfl
  | coin n next ih =>
      simp only [compile, mapView, mapProgram]
      exact congrArg _ (funext fun answer =>
        ih answer remaining state calls signedMessages bad tests)
  | sign index next ih =>
      exact ih _ remaining _ calls signedMessages bad tests
  | privateHash input outside next ih =>
      simp only [compile, mapView, map_privateHashStepOn]
      congr 1
      funext answer updated messages
      exact ih answer remaining updated calls messages bad tests
  | hash input next ih =>
      cases remaining with
      | zero => rfl
      | succ remaining =>
          simp only [compile, mapView, map_publicHashStepOn]
          congr 1
          funext answer updated calls' bad' tests'
          exact ih answer remaining updated calls' signedMessages bad' tests'

theorem run_compile_mapView {α β : Type} (f : α → β)
    (table : PointTable) (view : View α) (remaining : Nat)
    (state : State) (calls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests : Nat)
    (audit : GroupedBalancedIndexLabeledAudit67.Audit) :
    mapRun (mapOutcome f) <$>
      GroupedBalancedIndexLabeledAudit67.run
        (compile table view remaining state calls signedMessages bad tests)
        audit =
      GroupedBalancedIndexLabeledAudit67.run
        (compile table (mapView f view) remaining state calls
          signedMessages bad tests) audit := by
  rw [← compile_mapView]
  exact run_mapProgram _ _ _

theorem run_compile_mapView_member {α β : Type} (f : α → β)
    (table : PointTable) (view : View α) (remaining : Nat)
    (state : State) (calls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests : Nat)
    (audit : GroupedBalancedIndexLabeledAudit67.Audit)
    (result :
      (GroupedBalancedGraphIndexJoint67.JointOutcome β × List Draw) ×
        GroupedBalancedIndexLabeledAudit67.Audit)
    (member : result ∈ support
      (GroupedBalancedIndexLabeledAudit67.run
        (compile table (mapView f view) remaining state calls
          signedMessages bad tests) audit)) :
    ∃ child,
      child ∈ support
        (GroupedBalancedIndexLabeledAudit67.run
          (compile table view remaining state calls signedMessages bad tests)
          audit) ∧
      mapRun (mapOutcome f) child = result := by
  rw [← run_compile_mapView] at member
  simpa only [support_map, Set.mem_image] using member

theorem annotate_mapView {α β : Type} (f : α → β)
    (view : View α) (secret : Nat) :
    GroupedBalancedGraphIndexJointClassTrace67.annotate
      (mapView f view) secret =
      mapView (fun result : α × Nat => (f result.1, result.2))
        (GroupedBalancedGraphIndexJointClassTrace67.annotate view secret) := by
  induction view generalizing secret with
  | done value => rfl
  | coin n next ih =>
      simp only [mapView,
        GroupedBalancedGraphIndexJointClassTrace67.annotate]
      exact congrArg _ (funext fun answer => ih answer secret)
  | sign index next ih =>
      simp only [mapView,
        GroupedBalancedGraphIndexJointClassTrace67.annotate]
      exact congrArg _ (funext fun answer => ih answer secret)
  | privateHash input outside next ih =>
      simp only [mapView,
        GroupedBalancedGraphIndexJointClassTrace67.annotate]
      exact congrArg _ (funext fun answer => ih answer secret)
  | hash input next ih =>
      simp only [mapView,
        GroupedBalancedGraphIndexJointClassTrace67.annotate]
      exact congrArg _ (funext fun answer =>
        ih answer (secret +
          GroupedBalancedGraphIndexJointClassTrace67.secretCharge input))

#print axioms compile_mapView
#print axioms run_compile_mapView_member
#print axioms annotate_mapView

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledMapView67
