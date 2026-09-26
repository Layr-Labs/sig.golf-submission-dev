import SigGolfCandidate.Hypertree.GroupedBalancedNonceInterpreterObserve67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledJoint67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedNonceJointCompiler67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedNonceStepBind67. -/
section
/-! The direct67 stopped graph/H5 compiler with nonce reads represented as
passive effects. Its control flow is independent of the sampled nonce table. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceJointCompiler67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedNonceView67
open GroupedBalancedNonceProgram67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

abbrev HProgram := GroupedBalancedNonceProgram67.Program

noncomputable def privateStep
    (state : State) (input : Query)
    (signedMessages : Finset Message) :
    HProgram (BitVec 256 × State × Finset Message) :=
  fromLabeled <|
    GroupedBalancedIndexLabeledJoint67.privateHashStepOn
      (SecurityIndexQuery.parse input) state input signedMessages
      (fun answer updated signed => .pure (answer, updated, signed))

noncomputable def publicStep
    (table : PointTable) (state : State) (input : Query)
    (graphCalls : Nat) (bad : Bool) (tests : Nat) :
    HProgram (BitVec 256 × State × Nat × Bool × Nat) :=
  fromLabeled <|
    GroupedBalancedIndexLabeledJoint67.publicHashStepOn
      (SecurityIndexQuery.parse input) table state input graphCalls bad tests
      (fun answer updated calls bad tests =>
        .pure (answer, updated, calls, bad, tests))

noncomputable def compile {α : Type} (table : PointTable) :
    NView α → Nat → State → Nat → Finset Message → Bool → Nat →
    HProgram (JointOutcome α)
  | .done value, remaining, state, graphCalls, _, bad, tests =>
      .pure ⟨⟨some value, remaining, state, graphCalls⟩, bad, tests⟩
  | .coin n next, remaining, state, graphCalls, signedMessages, bad, tests =>
      .coin n (fun answer => compile table (next answer) remaining state
        graphCalls signedMessages bad tests)
  | .sign index next, remaining, state, graphCalls, signedMessages, bad, tests =>
      let answer := table (.inr (.inl index))
      compile table (next answer) remaining (signed state index answer)
        graphCalls signedMessages bad tests
  | .privateHash input _ next, remaining, state, graphCalls,
      signedMessages, bad, tests =>
      bind (privateStep state input signedMessages)
        (fun ⟨answer, updated, signedMessages⟩ =>
          compile table (next answer) remaining updated graphCalls
            signedMessages bad tests)
  | .hash input next, remaining, state, graphCalls,
      signedMessages, bad, tests =>
      match remaining with
      | 0 => .pure ⟨⟨none, 0, state, graphCalls⟩, bad, tests⟩
      | remaining + 1 =>
          bind (publicStep table state input graphCalls bad tests)
            (fun ⟨answer, updated, graphCalls, bad, tests⟩ =>
              compile table (next answer) remaining updated graphCalls
                signedMessages bad tests)
  | .nonce message next, remaining, state, graphCalls,
      signedMessages, bad, tests =>
      .nonce message (fun answer =>
        compile table (next answer) remaining state graphCalls
          signedMessages bad tests)

noncomputable def start {α : Type} (table : PointTable)
    (view : QueryCache PointSpec → NView α) (remaining : Nat) :
    HProgram (JointOutcome α) :=
  compile table (view (GroupedBalancedGraphMonitorSetup67.cache table))
    remaining
    (GroupedBalancedGraphMonitorSignBound67.initial
      (GroupedBalancedGraphMonitorSetup67.cache table))
    0 ∅ false 0

#print axioms compile
#print axioms start

end SigGolfCandidate.Hypertree.GroupedBalancedNonceJointCompiler67

end

/-! Kleisli laws for the existing labelled H5 and graph macros. These make
the one-step hybrid compiler erase to the original continuation-passing
compiler without changing its sampled path. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceStepBind67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedNonceProgram67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem bind_cachedDraw {α β : Type}
    (residual : QueryCache HashSpec) (input : Query) (mark : Bool)
    (next : BitVec 256 → QueryCache HashSpec →
      GroupedBalancedIndexLabeledProgram67.Program α)
    (resume : α → GroupedBalancedIndexLabeledProgram67.Program β) :
    bindLabeled
      (GroupedBalancedIndexLabeledLift67.cachedDraw residual input mark next)
      resume =
    GroupedBalancedIndexLabeledLift67.cachedDraw residual input mark
      (fun answer cache => bindLabeled (next answer cache) resume) := by
  cases present : residual input <;>
    simp only [GroupedBalancedIndexLabeledLift67.cachedDraw,
      present, bindLabeled]

theorem bind_unmarked {α β γ : Type} (program : ProbComp α)
    (next : α → GroupedBalancedIndexLabeledProgram67.Program β)
    (resume : β → GroupedBalancedIndexLabeledProgram67.Program γ) :
    bindLabeled (GroupedBalancedIndexLabeledLift67.unmarked program next)
      resume =
    GroupedBalancedIndexLabeledLift67.unmarked program
      (fun value => bindLabeled (next value) resume) := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind n child ih =>
      change GroupedBalancedIndexLabeledProgram67.Program.coin n
        (fun answer => bindLabeled
          (GroupedBalancedIndexLabeledLift67.unmarked (child answer) next)
          resume) =
        GroupedBalancedIndexLabeledProgram67.Program.coin n
          (fun answer => GroupedBalancedIndexLabeledLift67.unmarked
            (child answer) (fun value => bindLabeled (next value) resume))
      exact congrArg _ (funext fun answer => ih answer)

theorem bind_ofGraphKeep {α β γ : Type}
    (table : PointTable) (cache : QueryCache PointSpec)
    (program : GroupedBalancedGraphMonitorProgram67.Program α)
    (next : GroupedBalancedGraphMonitorProgram67.Outcome α →
      GroupedBalancedIndexLabeledProgram67.Program β)
    (resume : β → GroupedBalancedIndexLabeledProgram67.Program γ) :
    bindLabeled
      (GroupedBalancedIndexLabeledLift67.ofGraphKeep table cache program next)
      resume =
    GroupedBalancedIndexLabeledLift67.ofGraphKeep table cache program
      (fun result => bindLabeled (next result) resume) := by
  induction program generalizing cache next with
  | done value => rfl
  | reveal point child ih => exact ih (table point) _ _
  | guess point value child ih => exact ih cache _
  | coin n child ih =>
      simp only [GroupedBalancedIndexLabeledLift67.ofGraphKeep,
        bindLabeled]
      exact congrArg _ (funext fun answer => ih answer cache next)
  | bits child ih =>
      rw [GroupedBalancedIndexLabeledLift67.ofGraphKeep, bind_unmarked]
      change _ = GroupedBalancedIndexLabeledLift67.unmarked
        ($ᵗ BitVec 256)
        (fun answer => GroupedBalancedIndexLabeledLift67.ofGraphKeep
          table cache (child answer)
          (fun result => bindLabeled (next result) resume))
      exact congrArg _ (funext fun answer => ih answer cache next)
  | collision target child ih =>
      rw [GroupedBalancedIndexLabeledLift67.ofGraphKeep, bind_unmarked]
      change _ = GroupedBalancedIndexLabeledLift67.unmarked
        ($ᵗ BitVec 256)
        (fun answer => GroupedBalancedIndexLabeledLift67.ofGraphKeep
          table cache (child answer)
          (fun result => bindLabeled
            (next (GroupedBalancedGraphMonitorProgram67.addTest
              (decide (truncate answer = target)) result)) resume))
      exact congrArg _ (funext fun answer => ih answer cache _)

#print axioms bind_cachedDraw
#print axioms bind_unmarked
#print axioms bind_ofGraphKeep

end SigGolfCandidate.Hypertree.GroupedBalancedNonceStepBind67
