import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAuditPrivateStep67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPrepend67
import SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerCutoff67

/-! A completed eager signing step leaves its message in the same H5 audit
used by the labeled joint graph monitor. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledOrganizerSignAudit67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedIdealEagerCutoff67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledJoint67
open scoped Classical
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false

theorem compile_private_eq {α : Type}
    (table : PointTable) (input : Query)
    (outside : GroupedBalancedGraphQuery67.locate input = none)
    (next : BitVec 256 → View (Option α × List Action))
    (secret remaining : Nat) (state : State) (calls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat) :
    compile table
      (GroupedBalancedGraphIndexJointClassTrace67.annotate
        (.privateHash input outside next) secret)
      remaining state calls signedMessages bad tests =
    privateHashStepOn (SecurityIndexQuery.parse input)
      state input signedMessages
      (fun answer updated signed =>
        compile table
          (GroupedBalancedGraphIndexJointClassTrace67.annotate
            (next answer) secret)
          remaining updated calls signed bad tests) := rfl

theorem compile_private_sign_present {α : Type}
    (table : PointTable) (input : Query)
    (outside : GroupedBalancedGraphQuery67.locate input = none)
    (pair : Message × Bytes 32)
    (parsed : SecurityIndexQuery.parse input = some pair)
    (next : BitVec 256 → View (Option α × List Action))
    (secret remaining : Nat)
    (state : State) (calls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat)
    (audit : Audit)
    (result :
      (GroupedBalancedGraphIndexJoint67.JointOutcome
        ((Option α × List Action) × Nat) × List Draw) × Audit)
    (member : result ∈ support (run
      (compile table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          (.privateHash input outside next) secret)
        remaining state calls signedMessages bad tests) audit)) :
    pair.1 ∈ result.2.signedMessages := by
  rw [compile_private_eq table input outside next secret remaining state
    calls signedMessages bad tests, parsed] at member
  exact GroupedBalancedIndexLabeledAuditSign67.private_sign_present
    state input pair signedMessages _ audit result member

theorem compile_private_handoff {α : Type}
    (table : PointTable) (input : Query)
    (outside : GroupedBalancedGraphQuery67.locate input = none)
    (pair : Message × Bytes 32)
    (parsed : SecurityIndexQuery.parse input = some pair)
    (next : BitVec 256 → View (Option α × List Action))
    (secret remaining : Nat) (state : State) (calls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat)
    (audit : Audit)
    (result :
      (GroupedBalancedGraphIndexJoint67.JointOutcome
        ((Option α × List Action) × Nat) × List Draw) × Audit)
    (member : result ∈ support (run
      (compile table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          (.privateHash input outside next) secret)
        remaining state calls signedMessages bad tests) audit)) :
    ∃ answer residual nextAudit child,
      child ∈ support (run
        (compile table
          (GroupedBalancedGraphIndexJointClassTrace67.annotate
            (next answer) secret)
          remaining { state with residual := residual } calls
          (insert pair.1 signedMessages) bad tests) nextAudit) ∧
      nextAudit.signedMessages = insert pair.1 audit.signedMessages ∧
      child.1.1 = result.1.1 ∧
      child.2 = result.2 ∧
      pair.1 ∈ nextAudit.signedMessages := by
  rw [compile_private_eq table input outside next secret remaining state
    calls signedMessages bad tests, parsed] at member
  exact GroupedBalancedIndexLabeledAuditPrivateStep67.private_step
    state input pair signedMessages _ audit result member

theorem prepend_preserves_signed {α : Type}
    (table : PointTable) (view : View (Option α × List Action))
    (action : Action) (secret remaining : Nat)
    (state : State) (calls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat)
    (audit : Audit) (message : Message)
    (base : ∀ child ∈ support (run
      (compile table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          view secret)
        remaining state calls signedMessages bad tests) audit),
        message ∈ child.2.signedMessages)
    (result :
      (GroupedBalancedGraphIndexJoint67.JointOutcome
        ((Option α × List Action) × Nat) × List Draw) × Audit)
    (member : result ∈ support (run
      (compile table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          (GroupedBalancedGameViewLoggedBridge67.prependAction action
            view) secret)
        remaining state calls signedMessages bad tests) audit)) :
    message ∈ result.2.signedMessages := by
  obtain ⟨child, childMember, auditEq, _⟩ :=
    GroupedBalancedIndexLabeledPrepend67.prepend_member
      action table view secret remaining state calls signedMessages
      bad tests audit result member
  rw [← auditEq]
  exact base child childMember

theorem signed_view_present {α : Type}
    (table : PointTable) (input : Query)
    (outside : GroupedBalancedGraphQuery67.locate input = none)
    (pair : Message × Bytes 32)
    (parsed : SecurityIndexQuery.parse input = some pair)
    (next : BitVec 256 → View (Option α × List Action))
    (action : Action) (inner outer : View (Option α × List Action))
    (innerEq : inner = .privateHash input outside next)
    (outerEq : outer =
      GroupedBalancedGameViewLoggedBridge67.prependAction action
        inner)
    (secret remaining : Nat) (state : State) (calls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat)
    (audit : Audit)
    (result :
      (GroupedBalancedGraphIndexJoint67.JointOutcome
        ((Option α × List Action) × Nat) × List Draw) × Audit)
    (member : result ∈ support (run
      (compile table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          outer secret)
        remaining state calls signedMessages bad tests) audit)) :
    pair.1 ∈ result.2.signedMessages := by
  rw [outerEq] at member
  have base : ∀ child ∈ support (run
      (compile table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          inner secret)
        remaining state calls signedMessages bad tests) audit),
        pair.1 ∈ child.2.signedMessages := by
    intro child childMember
    rw [innerEq] at childMember
    rw [compile_private_eq table input outside next secret remaining state
      calls signedMessages bad tests, parsed] at childMember
    exact GroupedBalancedIndexLabeledAuditSign67.private_sign_present
      state input pair signedMessages _ audit child childMember
  exact prepend_preserves_signed table inner action secret remaining
    state calls signedMessages bad tests audit pair.1 base result member

theorem prepended_private_completed {α : Type}
    (table : PointTable) (input : Query)
    (outside : GroupedBalancedGraphQuery67.locate input = none)
    (pair : Message × Bytes 32)
    (parsed : SecurityIndexQuery.parse input = some pair)
    (next : BitVec 256 → View (Option α × List Action))
    (action : Action) (inner outer : View (Option α × List Action))
    (innerEq : inner = .privateHash input outside next)
    (outerEq : outer =
      GroupedBalancedGameViewLoggedBridge67.prependAction action inner)
    (secret remaining : Nat) (state : State) (calls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat)
    (audit : Audit)
    (result :
      (GroupedBalancedGraphIndexJoint67.JointOutcome
        ((Option α × List Action) × Nat) × List Draw) × Audit)
    (value : α) (trace : List Action) (secretOut : Nat)
    (member : result ∈ support (run
      (compile table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          outer secret)
        remaining state calls signedMessages bad tests) audit))
    (returned : result.1.1.value.value =
      some ((some value, trace), secretOut)) :
    ∃ answer residual nextAudit child innerTrace,
      child ∈ support (run
        (compile table
          (GroupedBalancedGraphIndexJointClassTrace67.annotate
            (next answer) secret)
          remaining { state with residual := residual } calls
          (insert pair.1 signedMessages) bad tests) nextAudit) ∧
      nextAudit.signedMessages = insert pair.1 audit.signedMessages ∧
      pair.1 ∈ nextAudit.signedMessages ∧
      child.2 = result.2 ∧
      child.1.1.value.value =
        some ((some value, innerTrace), secretOut) := by
  rw [outerEq] at member
  obtain ⟨outerChild, outerTrace, outerMember, outerAudit, outerValue⟩ :=
    GroupedBalancedIndexLabeledPrepend67.prepend_completed action table
      inner secret remaining state calls signedMessages bad tests audit
      result value trace secretOut member returned
  rw [innerEq, compile_private_eq table input outside next secret remaining
    state calls signedMessages bad tests, parsed] at outerMember
  obtain ⟨answer, residual, nextAudit, child, childMember,
      signedEq, valueEq, auditEq, present⟩ :=
    GroupedBalancedIndexLabeledAuditPrivateStep67.private_step
      state input pair signedMessages _ audit outerChild outerMember
  refine ⟨answer, residual, nextAudit, child, outerTrace, childMember,
    signedEq, present, ?_, ?_⟩
  · exact auditEq.trans outerAudit
  · rw [valueEq]
    exact outerValue

#print axioms compile_private_eq
#print axioms compile_private_sign_present
#print axioms compile_private_handoff
#print axioms prepend_preserves_signed
#print axioms signed_view_present
#print axioms prepended_private_completed

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledOrganizerSignAudit67
