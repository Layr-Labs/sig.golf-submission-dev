import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAuditPrivateStep67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAuditLift67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledEagerSignHandoff67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAuditPublicStep67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledEagerHashHandoff67. -/
section
/-! Invert one labeled public hash call while retaining signed-message coverage. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAuditPublicStep67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledJoint67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem public_step {α : Type}
    (parsed : Option (Message × Bytes 32)) (table : PointTable)
    (state : State) (input : Query) (calls : Nat)
    (bad : Bool) (tests : Nat)
    (next : BitVec 256 → State → Nat → Bool → Nat → Program α)
    (audit : Audit) (result : (α × List Draw) × Audit)
    (member : result ∈ support (run
      (publicHashStepOn parsed table state input calls bad tests next) audit)) :
    ∃ answer state' calls' bad' tests' nextAudit child,
      child ∈ support
        (run (next answer state' calls' bad' tests') nextAudit) ∧
      audit.signedMessages ⊆ nextAudit.signedMessages ∧
      child.1.1 = result.1.1 ∧
      child.2 = result.2 := by
  cases parsed with
  | none =>
      rw [publicHashStepOn,
        GroupedBalancedIndexLabeledAuditLift67.run_ofGraphKeep,
        mem_support_bind_iff] at member
      obtain ⟨graphResult, _, child⟩ := member
      exact ⟨graphResult.value.1,
        opened state graphResult.value.2.1 graphResult.value.2.2,
        calls + if (GroupedBalancedGraphQuery67.locate input).isSome
          then 1 else 0,
        bad || graphResult.bad, tests + graphResult.tests,
        audit, result, child, Finset.Subset.rfl, rfl, rfl⟩
  | some pair =>
      cases cached : state.residual input with
      | some answer =>
          refine ⟨answer, state, calls, bad, tests, audit,
            result, ?_, Finset.Subset.rfl, rfl, rfl⟩
          simpa only [publicHashStepOn,
            GroupedBalancedIndexLabeledLift67.cachedDraw,
            cached, reduceCtorEq, if_false] using member
      | none =>
          simp only [publicHashStepOn,
            GroupedBalancedIndexLabeledLift67.cachedDraw,
            cached, if_true, run, mem_support_bind_iff] at member
          obtain ⟨answer, _, member⟩ := member
          simp only [support_map, Set.mem_image] at member
          obtain ⟨child, childMember, same⟩ := member
          let updated : Audit :=
            { publicStep audit pair with
              h5cache := (publicStep audit pair).h5cache.cacheQuery
                input answer
              draws := (publicStep audit pair).draws ++
                [(input, (false, answer.extractLsb' 0 160))] }
          refine ⟨answer,
            { state with residual := state.residual.cacheQuery input answer },
            calls, bad, tests, updated, child, ?_, ?_, ?_, ?_⟩
          · simpa only [updated] using childMember
          · simp only [updated, publicStep]
            split <;> exact Finset.Subset.rfl
          · simpa only [] using
              (congrArg (fun x : (α × List Draw) × Audit => x.1.1) same)
          · simpa only [] using
              (congrArg (fun x : (α × List Draw) × Audit => x.2) same)

#print axioms public_step

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAuditPublicStep67

end

/-! Peel a completed eager public hash call into its continuation while
retaining the signed-message audit and terminal organizer value. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledEagerHashHandoff67
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
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false

theorem compile_hash_eq {β : Type}
    (table : PointTable) (input : Query)
    (next : BitVec 256 → View β)
    (secret remaining : Nat) (state : State) (calls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat) :
    compile table
      (GroupedBalancedGraphIndexJointClassTrace67.annotate
        (.hash input next) secret)
      (remaining + 1) state calls signedMessages bad tests =
    publicHashStepOn (SecurityIndexQuery.parse input)
      table state input calls bad tests
      (fun answer updated calls' bad' tests' =>
        compile table
          (GroupedBalancedGraphIndexJointClassTrace67.annotate
            (next answer)
            (secret +
              GroupedBalancedGraphIndexJointClassTrace67.secretCharge input))
          remaining updated calls' signedMessages bad' tests') := rfl

theorem eager_hash_handoff {α : Type}
    (answers : SecurityGraphIdeal.PrivateTable)
    (cache : QueryCache PointSpec) (table : PointTable)
    (input : Query) (next : BitVec 256 → Interaction α)
    (budget secret remaining : Nat)
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
          (eagerCutoffView answers cache (.hash input next)
            (budget + 1)) secret)
        (remaining + 1) state calls signedMessages bad tests) audit))
    (returned : result.1.1.value.value =
      some ((some value, trace), secretOut)) :
    ∃ answer updated calls' bad' tests' nextAudit tail tailTrace,
      tail ∈ support (run
        (compile table
          (GroupedBalancedGraphIndexJointClassTrace67.annotate
            (eagerCutoffView answers cache (next answer) budget)
            (secret +
              GroupedBalancedGraphIndexJointClassTrace67.secretCharge input))
          remaining updated calls' signedMessages bad' tests') nextAudit) ∧
      audit.signedMessages ⊆ nextAudit.signedMessages ∧
      tail.2 = result.2 ∧
      tail.1.1.value.value =
        some ((some value, tailTrace), secretOut) := by
  let nextView : BitVec 256 → View (Option α × List Action) :=
    fun answer => GroupedBalancedGameViewLoggedBridge67.prependAction
      (.publicHash input)
      (eagerCutoffView answers cache (next answer) budget)
  generalize hOuter : eagerCutoffView answers cache
    (.hash input next) (budget + 1) = outer at member
  have outerEq : outer = .hash input nextView := by
    rw [← hOuter]
    rfl
  change result ∈ support (run
    (compile table
      (GroupedBalancedGraphIndexJointClassTrace67.annotate outer secret)
      (remaining + 1) state calls signedMessages bad tests) audit) at member
  rw [outerEq, compile_hash_eq] at member
  generalize hParsed : SecurityIndexQuery.parse input = parsed at member
  generalize hStep :
    (fun answer updated calls' bad' tests' =>
      compile table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          (nextView answer)
          (secret +
            GroupedBalancedGraphIndexJointClassTrace67.secretCharge input))
        remaining updated calls' signedMessages bad' tests') = step at member
  have stepEq : step =
    fun answer updated calls' bad' tests' =>
      compile table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          (nextView answer)
          (secret +
            GroupedBalancedGraphIndexJointClassTrace67.secretCharge input))
        remaining updated calls' signedMessages bad' tests' := hStep.symm
  change result ∈ support (run
    (publicHashStepOn parsed
      table state input calls bad tests step) audit) at member
  obtain ⟨answer, updated, calls', bad', tests', nextAudit, mid,
      midMember, signedSubset, valueEq, auditEq⟩ :=
    GroupedBalancedIndexLabeledAuditPublicStep67.public_step
      parsed table state input calls bad tests
      step audit result member
  rw [stepEq] at midMember
  have midValue : mid.1.1.value.value =
      some ((some value, trace), secretOut) := by
    rw [valueEq]
    exact returned
  have nextEq : nextView answer =
      GroupedBalancedGameViewLoggedBridge67.prependAction
        (.publicHash input)
        (eagerCutoffView answers cache (next answer) budget) := rfl
  change mid ∈ support (run
    (compile table
      (GroupedBalancedGraphIndexJointClassTrace67.annotate
        (nextView answer)
        (secret +
          GroupedBalancedGraphIndexJointClassTrace67.secretCharge input))
      remaining updated calls' signedMessages bad' tests') nextAudit)
    at midMember
  rw [nextEq] at midMember
  obtain ⟨tail, tailTrace, tailMember, tailAudit, tailValue⟩ :=
    GroupedBalancedIndexLabeledPrepend67.prepend_completed
      (.publicHash input) table
      (eagerCutoffView answers cache (next answer) budget)
      (secret +
        GroupedBalancedGraphIndexJointClassTrace67.secretCharge input)
      remaining updated calls' signedMessages bad' tests' nextAudit mid
      value trace secretOut midMember midValue
  exact ⟨answer, updated, calls', bad', tests', nextAudit,
    tail, tailTrace, tailMember, signedSubset,
    tailAudit.trans auditEq, tailValue⟩

theorem eager_hash_handoff_view {α : Type}
    (answers : SecurityGraphIdeal.PrivateTable)
    (cache : QueryCache PointSpec) (table : PointTable)
    (input : Query) (next : BitVec 256 → Interaction α)
    (budget secret remaining : Nat)
    (outer : View (Option α × List Action))
    (outerEq : outer = eagerCutoffView answers cache
      (.hash input next) (budget + 1))
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
        (remaining + 1) state calls signedMessages bad tests) audit))
    (returned : result.1.1.value.value =
      some ((some value, trace), secretOut)) :
    ∃ answer updated calls' bad' tests' nextAudit tail tailTrace,
      tail ∈ support (run
        (compile table
          (GroupedBalancedGraphIndexJointClassTrace67.annotate
            (eagerCutoffView answers cache (next answer) budget)
            (secret +
              GroupedBalancedGraphIndexJointClassTrace67.secretCharge input))
          remaining updated calls' signedMessages bad' tests') nextAudit) ∧
      audit.signedMessages ⊆ nextAudit.signedMessages ∧
      tail.2 = result.2 ∧
      tail.1.1.value.value =
        some ((some value, tailTrace), secretOut) := by
  let nextView : BitVec 256 → View (Option α × List Action) :=
    fun answer => GroupedBalancedGameViewLoggedBridge67.prependAction
      (.publicHash input)
      (eagerCutoffView answers cache (next answer) budget)
  have outerHash : outer = .hash input nextView := by
    rw [outerEq]
    rfl
  change result ∈ support (run
    (compile table
      (GroupedBalancedGraphIndexJointClassTrace67.annotate outer secret)
      (remaining + 1) state calls signedMessages bad tests) audit) at member
  rw [outerHash, compile_hash_eq] at member
  generalize hParsed : SecurityIndexQuery.parse input = parsed at member
  generalize hStep :
    (fun answer updated calls' bad' tests' =>
      compile table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          (nextView answer)
          (secret +
            GroupedBalancedGraphIndexJointClassTrace67.secretCharge input))
        remaining updated calls' signedMessages bad' tests') = step at member
  have stepEq : step =
    fun answer updated calls' bad' tests' =>
      compile table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          (nextView answer)
          (secret +
            GroupedBalancedGraphIndexJointClassTrace67.secretCharge input))
        remaining updated calls' signedMessages bad' tests' := hStep.symm
  change result ∈ support (run
    (publicHashStepOn parsed
      table state input calls bad tests step) audit) at member
  obtain ⟨answer, updated, calls', bad', tests', nextAudit, mid,
      midMember, signedSubset, valueEq, auditEq⟩ :=
    GroupedBalancedIndexLabeledAuditPublicStep67.public_step
      parsed table state input calls bad tests
      step audit result member
  rw [stepEq] at midMember
  have midValue : mid.1.1.value.value =
      some ((some value, trace), secretOut) := by
    rw [valueEq]
    exact returned
  have nextEq : nextView answer =
      GroupedBalancedGameViewLoggedBridge67.prependAction
        (.publicHash input)
        (eagerCutoffView answers cache (next answer) budget) := rfl
  change mid ∈ support (run
    (compile table
      (GroupedBalancedGraphIndexJointClassTrace67.annotate
        (nextView answer)
        (secret +
          GroupedBalancedGraphIndexJointClassTrace67.secretCharge input))
      remaining updated calls' signedMessages bad' tests') nextAudit)
    at midMember
  rw [nextEq] at midMember
  obtain ⟨tail, tailTrace, tailMember, tailAudit, tailValue⟩ :=
    GroupedBalancedIndexLabeledPrepend67.prepend_completed
      (.publicHash input) table
      (eagerCutoffView answers cache (next answer) budget)
      (secret +
        GroupedBalancedGraphIndexJointClassTrace67.secretCharge input)
      remaining updated calls' signedMessages bad' tests' nextAudit mid
      value trace secretOut midMember midValue
  exact ⟨answer, updated, calls', bad', tests', nextAudit,
    tail, tailTrace, tailMember, signedSubset,
    tailAudit.trans auditEq, tailValue⟩

#print axioms compile_hash_eq
#print axioms eager_hash_handoff
#print axioms eager_hash_handoff_view

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledEagerHashHandoff67
