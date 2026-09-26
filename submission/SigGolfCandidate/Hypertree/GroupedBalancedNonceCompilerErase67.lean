import SigGolfCandidate.Hypertree.GroupedBalancedNonceStepBind67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedNonceStepNaturality67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedNonceCompilerErase67. -/
section
/-! Each hybrid one-step segment erases to the original labelled macro with
its continuation attached. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceStepNaturality67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedNonceProgram67
open GroupedBalancedNonceStepBind67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem privateStep_bind {β : Type}
    (nonces : Message → BitVec 256)
    (state : State) (input : Query)
    (signedMessages : Finset Message)
    (next : BitVec 256 → State → Finset Message →
      GroupedBalancedIndexLabeledProgram67.Program β) :
    bindLabeled
      (erase nonces
        (GroupedBalancedNonceJointCompiler67.privateStep
          state input signedMessages))
      (fun ⟨answer, updated, signedMessages⟩ =>
        next answer updated signedMessages) =
    GroupedBalancedIndexLabeledJoint67.privateHashStepOn
      (SecurityIndexQuery.parse input) state input signedMessages next := by
  rw [GroupedBalancedNonceJointCompiler67.privateStep,
    erase_fromLabeled]
  cases parsed : SecurityIndexQuery.parse input with
  | some pair =>
      simp only [GroupedBalancedIndexLabeledJoint67.privateHashStepOn,
        bind_cachedDraw, bindLabeled]
  | none =>
      simp only [GroupedBalancedIndexLabeledJoint67.privateHashStepOn,
        bind_unmarked, bindLabeled]

theorem publicStep_bind {β : Type}
    (nonces : Message → BitVec 256)
    (table : PointTable) (state : State) (input : Query)
    (graphCalls : Nat) (bad : Bool) (tests : Nat)
    (next : BitVec 256 → State → Nat → Bool → Nat →
      GroupedBalancedIndexLabeledProgram67.Program β) :
    bindLabeled
      (erase nonces
        (GroupedBalancedNonceJointCompiler67.publicStep
          table state input graphCalls bad tests))
      (fun ⟨answer, updated, calls, bad, tests⟩ =>
        next answer updated calls bad tests) =
    GroupedBalancedIndexLabeledJoint67.publicHashStepOn
      (SecurityIndexQuery.parse input) table state input graphCalls bad tests
      next := by
  rw [GroupedBalancedNonceJointCompiler67.publicStep,
    erase_fromLabeled]
  cases parsed : SecurityIndexQuery.parse input with
  | some pair =>
      simp only [GroupedBalancedIndexLabeledJoint67.publicHashStepOn]
      split
      · simp only [bindLabeled, bind_cachedDraw]
      · simp only [bind_cachedDraw, bindLabeled]
  | none =>
      simp only [GroupedBalancedIndexLabeledJoint67.publicHashStepOn,
        bind_ofGraphKeep, bindLabeled]

#print axioms privateStep_bind
#print axioms publicStep_bind

end SigGolfCandidate.Hypertree.GroupedBalancedNonceStepNaturality67

end

/-! Filling the hybrid compiler's nonce effects with any fixed table yields
exactly the existing stopped input-labelled graph/H5 compiler. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceCompilerErase67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedNonceView67
open GroupedBalancedNonceProgram67
open GroupedBalancedNonceJointCompiler67
open GroupedBalancedNonceStepNaturality67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
open scoped Classical

theorem erase_compile {α : Type}
    (nonces : Message → BitVec 256) (table : PointTable)
    (view : NView α) (remaining : Nat) (state : State)
    (graphCalls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests : Nat) :
    GroupedBalancedNonceProgram67.erase nonces
      (compile table view remaining state graphCalls signedMessages bad tests) =
    GroupedBalancedIndexLabeledJoint67.compile table
      (instantiate nonces view) remaining state graphCalls signedMessages
      bad tests := by
  induction view generalizing remaining state graphCalls signedMessages bad tests with
  | done value => rfl
  | coin n next ih =>
      simp only [GroupedBalancedNonceJointCompiler67.compile,
        GroupedBalancedNonceProgram67.erase,
        instantiate, GroupedBalancedIndexLabeledJoint67.compile]
      exact congrArg _ (funext fun answer =>
        ih answer remaining state graphCalls signedMessages bad tests)
  | sign index next ih =>
      exact ih (table (.inr (.inl index))) _ _ _ _ _ _
  | nonce message next ih =>
      exact ih (nonces message) _ _ _ _ _ _
  | privateHash input outside next ih =>
      simp only [GroupedBalancedNonceJointCompiler67.compile,
        GroupedBalancedNonceProgram67.erase_bind,
        instantiate, GroupedBalancedIndexLabeledJoint67.compile]
      change bindLabeled
        (GroupedBalancedNonceProgram67.erase nonces
          (privateStep state input signedMessages))
        (fun ⟨answer, updated, signedMessages⟩ =>
          GroupedBalancedNonceProgram67.erase nonces
            (GroupedBalancedNonceJointCompiler67.compile table
              (next answer) remaining updated graphCalls signedMessages
              bad tests)) = _
      let continuation := fun answer updated signedMessages =>
        GroupedBalancedNonceProgram67.erase nonces
          (GroupedBalancedNonceJointCompiler67.compile table
            (next answer) remaining updated graphCalls signedMessages
            bad tests)
      have step := privateStep_bind nonces state input signedMessages
        continuation
      apply Eq.trans step
      have hcont : continuation =
          (fun answer updated signedMessages =>
            GroupedBalancedIndexLabeledJoint67.compile table
              (instantiate nonces (next answer)) remaining updated
              graphCalls signedMessages bad tests) := by
        funext answer updated signedMessages
        exact ih answer _ _ _ _ _ _
      exact congrArg
        (GroupedBalancedIndexLabeledJoint67.privateHashStepOn
          (SecurityIndexQuery.parse input) state input signedMessages)
        hcont
  | hash input next ih =>
      cases remaining with
      | zero => rfl
      | succ remaining =>
          simp only [GroupedBalancedNonceJointCompiler67.compile,
            GroupedBalancedNonceProgram67.erase_bind,
            instantiate, GroupedBalancedIndexLabeledJoint67.compile]
          change bindLabeled
            (GroupedBalancedNonceProgram67.erase nonces
              (publicStep table state input graphCalls bad tests))
            (fun ⟨answer, updated, calls, bad, tests⟩ =>
              GroupedBalancedNonceProgram67.erase nonces
                (GroupedBalancedNonceJointCompiler67.compile table
                  (next answer) remaining updated calls signedMessages
                  bad tests)) = _
          let continuation := fun answer updated calls bad tests =>
            GroupedBalancedNonceProgram67.erase nonces
              (GroupedBalancedNonceJointCompiler67.compile table
                (next answer) remaining updated calls signedMessages
                bad tests)
          have step := publicStep_bind nonces table state input graphCalls
            bad tests continuation
          apply Eq.trans step
          have hcont : continuation =
              (fun answer updated graphCalls bad tests =>
                GroupedBalancedIndexLabeledJoint67.compile table
                  (instantiate nonces (next answer)) remaining updated
                  graphCalls signedMessages bad tests) := by
            funext answer updated graphCalls bad tests
            exact ih answer _ _ _ _ _ _
          exact congrArg
            (GroupedBalancedIndexLabeledJoint67.publicHashStepOn
              (SecurityIndexQuery.parse input) table state input
              graphCalls bad tests) hcont

theorem erase_start {α : Type}
    (nonces : Message → BitVec 256) (table : PointTable)
    (view : QueryCache PointSpec → NView α) (remaining : Nat) :
    GroupedBalancedNonceProgram67.erase nonces
      (start table view remaining) =
    GroupedBalancedIndexLabeledJoint67.start table
      (fun cache => instantiate nonces (view cache)) remaining := by
  exact erase_compile nonces table _ _ _ _ _ _ _

#print axioms erase_compile
#print axioms erase_start

end SigGolfCandidate.Hypertree.GroupedBalancedNonceCompilerErase67
