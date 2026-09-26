import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledOrganizerSignAudit67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledEagerSignAudit67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledEagerSignHandoff67. -/
section
/-! Each completed eager signer action records its H5 message in the
audited graph/index execution. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledEagerSignAudit67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedIdealEagerCutoff67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledJoint67
open GroupedBalancedIndexLabeledOrganizerSignAudit67
open scoped Classical
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false

theorem eager_sign_present {α : Type}
    (answers : SecurityGraphIdeal.PrivateTable)
    (cache : QueryCache PointSpec) (table : PointTable)
    (message : Message) (next : GroupedBalancedScheme67.Signature →
      Interaction α) (budget secret remaining : Nat)
    (state : State) (calls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat)
    (audit : Audit)
    (result :
      (GroupedBalancedGraphIndexJoint67.JointOutcome
        ((Option α × List Action) × Nat) × List Draw) × Audit)
    (member : result ∈ support (run
      (compile table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          (eagerCutoffView answers cache (.sign message next)
            (budget + 2)) secret)
        remaining state calls signedMessages bad tests) audit)) :
    message ∈ result.2.signedMessages := by
  let randomizer := answers (.randomizer message)
  let input := SecurityRandomOracle.indexInput message randomizer
  let nextView : BitVec 256 → View (Option α × List Action) :=
    fun indexAnswer =>
      let index : BitVec 160 := indexAnswer.extractLsb' 0 160
      .sign index (fun bottomAnswer =>
        GroupedBalancedGameViewLoggedBridge67.prependAction
          (.publicHash input)
          (eagerCutoffView answers cache
            (next (GroupedBalancedGraphHonestSignView67.signatureFromAnswers
              cache randomizer index bottomAnswer)) budget))
  let outside := GroupedBalancedGraphHonestSignView67.locate_index_none
    message randomizer
  let inner : View (Option α × List Action) :=
    .privateHash input outside nextView
  generalize hOuter : eagerCutoffView answers cache
    (.sign message next) (budget + 2) = outer at member
  have innerEq : inner = .privateHash input outside nextView := rfl
  have outerEq : outer =
      GroupedBalancedGameViewLoggedBridge67.prependAction
        .privateHash inner := by
    rw [← hOuter]
    rfl
  change result ∈ support (run
    (compile table
      (GroupedBalancedGraphIndexJointClassTrace67.annotate outer secret)
      remaining state calls signedMessages bad tests) audit) at member
  have parsed : SecurityIndexQuery.parse input =
      some (message, randomizer) := SecurityIndexQuery.parse_index _ _
  have law := @signed_view_present α table input outside
    (message, randomizer) parsed nextView .privateHash inner outer
    innerEq outerEq secret remaining state calls signedMessages bad
    tests audit
  exact law result member

#print axioms eager_sign_present

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledEagerSignAudit67

end

/-! A completed eager signing action can be peeled to its continuation while
retaining the same terminal value and audited signed-message insertion. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledEagerSignHandoff67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedIdealEagerCutoff67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledJoint67
open GroupedBalancedIndexLabeledOrganizerSignAudit67
open scoped Classical
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false

theorem compile_sign_eq {β : Type}
    (table : PointTable) (index : BitVec 160)
    (next : BitVec 256 → View β)
    (secret remaining : Nat) (state : State) (calls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat) :
    compile table
      (GroupedBalancedGraphIndexJointClassTrace67.annotate
        (.sign index next) secret)
      remaining state calls signedMessages bad tests =
    compile table
      (GroupedBalancedGraphIndexJointClassTrace67.annotate
        (next (table (.inr (.inl index)))) secret)
      remaining
      (signed state index (table (.inr (.inl index))))
      calls signedMessages bad tests := rfl

theorem eager_sign_handoff {α : Type}
    (answers : SecurityGraphIdeal.PrivateTable)
    (cache : QueryCache PointSpec) (table : PointTable)
    (message : Message) (next : GroupedBalancedScheme67.Signature →
      Interaction α) (budget secret remaining : Nat)
    (state : State) (calls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat)
    (audit : Audit)
    (result :
      (GroupedBalancedGraphIndexJoint67.JointOutcome
        ((Option α × List Action) × Nat) × List Draw) × Audit)
    (value : α) (trace : List Action) (secretOut : Nat)
    (member : result ∈ support (run
      (compile table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          (eagerCutoffView answers cache (.sign message next)
            (budget + 2)) secret)
        remaining state calls signedMessages bad tests) audit))
    (returned : result.1.1.value.value =
      some ((some value, trace), secretOut)) :
    ∃ (indexAnswer : BitVec 256), ∃ residual nextAudit tail tailTrace,
      let index : BitVec 160 := indexAnswer.extractLsb' 0 160
      let randomizer := answers (.randomizer message)
      let signature :=
        GroupedBalancedGraphHonestSignView67.signatureFromAnswers
          cache randomizer index (table (.inr (.inl index)))
      tail ∈ support (run
        (compile table
          (GroupedBalancedGraphIndexJointClassTrace67.annotate
            (eagerCutoffView answers cache (next signature) budget)
            secret)
          remaining
          (signed { state with residual := residual } index
            (table (.inr (.inl index))))
          calls (insert message signedMessages) bad tests) nextAudit) ∧
      nextAudit.signedMessages = insert message audit.signedMessages ∧
      message ∈ nextAudit.signedMessages ∧
      tail.2 = result.2 ∧
      tail.1.1.value.value =
        some ((some value, tailTrace), secretOut) := by
  let randomizer := answers (.randomizer message)
  let input := SecurityRandomOracle.indexInput message randomizer
  let nextView : BitVec 256 → View (Option α × List Action) :=
    fun indexAnswer =>
      let index : BitVec 160 := indexAnswer.extractLsb' 0 160
      .sign index (fun bottomAnswer =>
        GroupedBalancedGameViewLoggedBridge67.prependAction
          (.publicHash input)
          (eagerCutoffView answers cache
            (next (GroupedBalancedGraphHonestSignView67.signatureFromAnswers
              cache randomizer index bottomAnswer)) budget))
  let outside := GroupedBalancedGraphHonestSignView67.locate_index_none
    message randomizer
  let inner : View (Option α × List Action) :=
    .privateHash input outside nextView
  generalize hOuter : eagerCutoffView answers cache
    (.sign message next) (budget + 2) = outer at member
  have innerEq : inner = .privateHash input outside nextView := rfl
  have outerEq : outer =
      GroupedBalancedGameViewLoggedBridge67.prependAction
        .privateHash inner := by
    rw [← hOuter]
    rfl
  change result ∈ support (run
    (compile table
      (GroupedBalancedGraphIndexJointClassTrace67.annotate outer secret)
      remaining state calls signedMessages bad tests) audit) at member
  have parsed : SecurityIndexQuery.parse input =
      some (message, randomizer) := SecurityIndexQuery.parse_index _ _
  obtain ⟨indexAnswer, residual, nextAudit, mid, midTrace,
      midMember, signedEq, present, midAudit, midValue⟩ :=
    prepended_private_completed table input outside
      (message, randomizer) parsed nextView .privateHash inner outer
      innerEq outerEq secret remaining state calls signedMessages
      bad tests audit result value trace secretOut member returned
  let index : BitVec 160 := indexAnswer.extractLsb' 0 160
  let bottomAnswer := table (.inr (.inl index))
  let signature := GroupedBalancedGraphHonestSignView67.signatureFromAnswers
    cache randomizer index bottomAnswer
  let signedState := signed { state with residual := residual } index bottomAnswer
  have nextEq : nextView indexAnswer =
      .sign index (fun answer =>
        GroupedBalancedGameViewLoggedBridge67.prependAction
          (.publicHash input)
          (eagerCutoffView answers cache
            (next (GroupedBalancedGraphHonestSignView67.signatureFromAnswers
              cache randomizer index answer)) budget)) := rfl
  rw [nextEq, compile_sign_eq] at midMember
  change mid ∈ support (run
    (compile table
      (GroupedBalancedGraphIndexJointClassTrace67.annotate
        (GroupedBalancedGameViewLoggedBridge67.prependAction
          (.publicHash input)
          (eagerCutoffView answers cache (next signature) budget)) secret)
      remaining signedState calls
      (insert message signedMessages) bad tests) nextAudit) at midMember
  obtain ⟨tail, tailTrace, tailMember, tailAudit, tailValue⟩ :=
    GroupedBalancedIndexLabeledPrepend67.prepend_completed
      (.publicHash input) table
      (eagerCutoffView answers cache (next signature) budget)
      secret remaining signedState calls (insert message signedMessages)
      bad tests nextAudit mid value midTrace secretOut midMember midValue
  refine ⟨indexAnswer, residual, nextAudit, tail, tailTrace,
    ?_, signedEq, present, ?_, tailValue⟩
  · exact tailMember
  · exact tailAudit.trans midAudit

theorem eager_sign_handoff_view {α : Type}
    (answers : SecurityGraphIdeal.PrivateTable)
    (cache : QueryCache PointSpec) (table : PointTable)
    (message : Message) (next : GroupedBalancedScheme67.Signature →
      Interaction α) (budget secret remaining : Nat)
    (outer : View (Option α × List Action))
    (outerEq : outer = eagerCutoffView answers cache
      (.sign message next) (budget + 2))
    (state : State) (calls : Nat)
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
    ∃ (indexAnswer : BitVec 256), ∃ residual nextAudit tail tailTrace,
      let index : BitVec 160 := indexAnswer.extractLsb' 0 160
      let randomizer := answers (.randomizer message)
      let signature :=
        GroupedBalancedGraphHonestSignView67.signatureFromAnswers
          cache randomizer index (table (.inr (.inl index)))
      tail ∈ support (run
        (compile table
          (GroupedBalancedGraphIndexJointClassTrace67.annotate
            (eagerCutoffView answers cache (next signature) budget)
            secret)
          remaining
          (signed { state with residual := residual } index
            (table (.inr (.inl index))))
          calls (insert message signedMessages) bad tests) nextAudit) ∧
      nextAudit.signedMessages = insert message audit.signedMessages ∧
      message ∈ nextAudit.signedMessages ∧
      tail.2 = result.2 ∧
      tail.1.1.value.value =
        some ((some value, tailTrace), secretOut) := by
  let randomizer := answers (.randomizer message)
  let input := SecurityRandomOracle.indexInput message randomizer
  let nextView : BitVec 256 → View (Option α × List Action) :=
    fun indexAnswer =>
      let index : BitVec 160 := indexAnswer.extractLsb' 0 160
      .sign index (fun bottomAnswer =>
        GroupedBalancedGameViewLoggedBridge67.prependAction
          (.publicHash input)
          (eagerCutoffView answers cache
            (next (GroupedBalancedGraphHonestSignView67.signatureFromAnswers
              cache randomizer index bottomAnswer)) budget))
  let outside := GroupedBalancedGraphHonestSignView67.locate_index_none
    message randomizer
  let inner : View (Option α × List Action) :=
    .privateHash input outside nextView
  have innerEq : inner = .privateHash input outside nextView := rfl
  have outerSign : outer =
      GroupedBalancedGameViewLoggedBridge67.prependAction
        .privateHash inner := by
    rw [outerEq]
    rfl
  change result ∈ support (run
    (compile table
      (GroupedBalancedGraphIndexJointClassTrace67.annotate outer secret)
      remaining state calls signedMessages bad tests) audit) at member
  have parsed : SecurityIndexQuery.parse input =
      some (message, randomizer) := SecurityIndexQuery.parse_index _ _
  obtain ⟨indexAnswer, residual, nextAudit, mid, midTrace,
      midMember, signedEq, present, midAudit, midValue⟩ :=
    prepended_private_completed table input outside
      (message, randomizer) parsed nextView .privateHash inner outer
      innerEq outerSign secret remaining state calls signedMessages
      bad tests audit result value trace secretOut member returned
  let index : BitVec 160 := indexAnswer.extractLsb' 0 160
  let bottomAnswer := table (.inr (.inl index))
  let signature := GroupedBalancedGraphHonestSignView67.signatureFromAnswers
    cache randomizer index bottomAnswer
  let signedState := signed { state with residual := residual } index bottomAnswer
  have nextEq : nextView indexAnswer =
      .sign index (fun answer =>
        GroupedBalancedGameViewLoggedBridge67.prependAction
          (.publicHash input)
          (eagerCutoffView answers cache
            (next (GroupedBalancedGraphHonestSignView67.signatureFromAnswers
              cache randomizer index answer)) budget)) := rfl
  rw [nextEq, compile_sign_eq] at midMember
  change mid ∈ support (run
    (compile table
      (GroupedBalancedGraphIndexJointClassTrace67.annotate
        (GroupedBalancedGameViewLoggedBridge67.prependAction
          (.publicHash input)
          (eagerCutoffView answers cache (next signature) budget)) secret)
      remaining signedState calls
      (insert message signedMessages) bad tests) nextAudit) at midMember
  obtain ⟨tail, tailTrace, tailMember, tailAudit, tailValue⟩ :=
    GroupedBalancedIndexLabeledPrepend67.prepend_completed
      (.publicHash input) table
      (eagerCutoffView answers cache (next signature) budget)
      secret remaining signedState calls (insert message signedMessages)
      bad tests nextAudit mid value midTrace secretOut midMember midValue
  refine ⟨indexAnswer, residual, nextAudit, tail, tailTrace,
    ?_, signedEq, present, ?_, tailValue⟩
  · exact tailMember
  · exact tailAudit.trans midAudit

#print axioms compile_sign_eq
#print axioms eager_sign_handoff
#print axioms eager_sign_handoff_view

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledEagerSignHandoff67
