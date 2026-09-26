import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledMapView67

/-! Peel an action-log prefix from a labeled, class-annotated View. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPrepend67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGameViewLoggedBridge67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledJoint67
open GroupedBalancedIndexLabeledMapView67
open GroupedBalancedGraphIndexJoint67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem annotated_prepend {α : Type} (action : Action)
    (view : View (Option α × List Action)) (secret : Nat) :
    GroupedBalancedGraphIndexJointClassTrace67.annotate
      (prependAction action view) secret =
      mapView
        (fun result : (Option α × List Action) × Nat =>
          ((result.1.1, action :: result.1.2), result.2))
        (GroupedBalancedGraphIndexJointClassTrace67.annotate view secret) := by
  exact GroupedBalancedIndexLabeledMapView67.annotate_mapView
    (fun result : Option α × List Action =>
      (result.1, action :: result.2)) view secret

theorem prepend_member {α : Type} (action : Action) (table : PointTable)
    (view : View (Option α × List Action)) (secret remaining : Nat)
    (state : State) (calls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests : Nat) (audit : Audit)
    (result :
      (JointOutcome ((Option α × List Action) × Nat) × List Draw) × Audit)
    (member : result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.compile table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          (prependAction action view) secret)
        remaining state calls signedMessages bad tests) audit)) :
    ∃ child,
      child ∈ support (run
        (GroupedBalancedIndexLabeledJoint67.compile table
          (GroupedBalancedGraphIndexJointClassTrace67.annotate view secret)
          remaining state calls signedMessages bad tests) audit) ∧
      child.2 = result.2 ∧
      result.1.1.value.value = child.1.1.value.value.map
        (fun output => ((output.1.1, action :: output.1.2), output.2)) := by
  rw [annotated_prepend] at member
  obtain ⟨child, childMember, same⟩ :=
    GroupedBalancedIndexLabeledMapView67.run_compile_mapView_member
      (fun output : (Option α × List Action) × Nat =>
        ((output.1.1, action :: output.1.2), output.2))
      table _ remaining state calls signedMessages bad tests audit
      result member
  refine ⟨child, childMember, ?_, ?_⟩
  · simpa only [GroupedBalancedIndexLabeledMapProgram67.mapRun] using
      (congrArg
        (fun x : (JointOutcome ((Option α × List Action) × Nat) ×
          List Draw) × Audit => x.2) same)
  · rw [← same]
    rfl

theorem prepend_completed {α : Type} (action : Action) (table : PointTable)
    (view : View (Option α × List Action)) (secret remaining : Nat)
    (state : State) (calls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests : Nat) (audit : Audit)
    (result :
      (JointOutcome ((Option α × List Action) × Nat) × List Draw) × Audit)
    (value : α) (trace : List Action) (secretOut : Nat)
    (member : result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.compile table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          (prependAction action view) secret)
        remaining state calls signedMessages bad tests) audit))
    (returned : result.1.1.value.value =
      some ((some value, trace), secretOut)) :
    ∃ child innerTrace,
      child ∈ support (run
        (GroupedBalancedIndexLabeledJoint67.compile table
          (GroupedBalancedGraphIndexJointClassTrace67.annotate view secret)
          remaining state calls signedMessages bad tests) audit) ∧
      child.2 = result.2 ∧
      child.1.1.value.value =
        some ((some value, innerTrace), secretOut) := by
  obtain ⟨child, childMember, auditEq, valueEq⟩ :=
    prepend_member action table view secret remaining state calls
      signedMessages bad tests audit result member
  cases childValue : child.1.1.value.value with
  | none =>
      rw [childValue] at valueEq
      simp only [Option.map_none] at valueEq
      rw [returned] at valueEq
      cases valueEq
  | some output =>
      rcases output with ⟨⟨maybeValue, innerTrace⟩, innerSecret⟩
      rw [childValue] at valueEq
      simp only [Option.map_some] at valueEq
      have equal :
          ((maybeValue, action :: innerTrace), innerSecret) =
            ((some value, trace), secretOut) :=
        Option.some.inj (valueEq.symm.trans returned)
      have valueSame : maybeValue = some value :=
        congrArg (fun x => x.1.1) equal
      have secretSame : innerSecret = secretOut :=
        congrArg Prod.snd equal
      refine ⟨child, innerTrace, childMember, auditEq, ?_⟩
      simpa only [valueSame, secretSame] using childValue

#print axioms prepend_member
#print axioms prepend_completed

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPrepend67
