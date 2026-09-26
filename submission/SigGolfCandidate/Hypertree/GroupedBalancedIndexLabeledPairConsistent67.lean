import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPairCoverage67
import SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerCutoff67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedIndexFixedNonce67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPairConsistent67. -/
section
/-! Every signer H5 input in the eager ideal View uses the deterministic
private randomizer for its message. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexFixedNonce67
open SigGolf OracleComp OracleSpec Reference SecurityRandomOracle
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGameViewLoggedBridge67
open GroupedBalancedIdealEagerCutoff67
open SecurityGraphIdeal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

def FixedNonce {α : Type} (nonces : Message → Bytes 32) :
    View α → Prop
  | .done _ => True
  | .coin _ next => ∀ answer, FixedNonce nonces (next answer)
  | .sign _ next => ∀ answer, FixedNonce nonces (next answer)
  | .hash _ next => ∀ answer, FixedNonce nonces (next answer)
  | .privateHash input _ next =>
      (∀ pair, SecurityIndexQuery.parse input = some pair →
        pair.2 = nonces pair.1) ∧
      (∀ answer, FixedNonce nonces (next answer))

theorem mapView {α β : Type} (nonces : Message → Bytes 32)
    (f : α → β) (view : View α)
    (fixed : FixedNonce nonces view) :
    FixedNonce nonces (GroupedBalancedGameViewLoggedBridge67.mapView f view) := by
  induction view with
  | done value => trivial
  | coin n next ih =>
      exact fun answer => ih answer (fixed answer)
  | sign index next ih =>
      exact fun answer => ih answer (fixed answer)
  | hash input next ih =>
      exact fun answer => ih answer (fixed answer)
  | privateHash input outside next ih =>
      exact ⟨fixed.1, fun answer => ih answer (fixed.2 answer)⟩

theorem prependAction {α : Type} (nonces : Message → Bytes 32)
    (action : GroupedBalancedGameQueryTrace67.Action)
    (view : View (α × List GroupedBalancedGameQueryTrace67.Action))
    (fixed : FixedNonce nonces view) :
    FixedNonce nonces (GroupedBalancedGameViewLoggedBridge67.prependAction
      action view) := by
  exact mapView nonces _ view fixed

theorem annotate {α : Type} (nonces : Message → Bytes 32)
    (view : View α) (secret : Nat)
    (fixed : FixedNonce nonces view) :
    FixedNonce nonces
      (GroupedBalancedGraphIndexJointClassTrace67.annotate view secret) := by
  induction view generalizing secret with
  | done value => trivial
  | coin n next ih => exact fun answer => ih answer secret (fixed answer)
  | sign index next ih => exact fun answer => ih answer secret (fixed answer)
  | hash input next ih =>
      exact fun answer => ih answer
        (secret + GroupedBalancedGraphIndexJointClassTrace67.secretCharge input)
        (fixed answer)
  | privateHash input outside next ih =>
      exact ⟨fixed.1, fun answer => ih answer secret (fixed.2 answer)⟩

theorem eagerCutoffView_fixed {α : Type}
    (answers : PrivateTable) (cache : QueryCache PointSpec)
    (interaction : Interaction α) (budget : Nat) :
    FixedNonce (fun message => answers (.randomizer message))
      (GroupedBalancedIdealEagerCutoff67.eagerCutoffView
        answers cache interaction budget) := by
  induction interaction generalizing budget with
  | done value =>
      trivial
  | coin n next ih =>
      exact fun answer => ih answer budget
  | hash input next ih =>
      cases budget with
      | zero => trivial
      | succ budget =>
          intro answer
          exact prependAction _ _ _ (ih answer budget)
  | sign message next ih =>
      cases budget with
      | zero => trivial
      | succ budget =>
          cases budget with
          | zero =>
              exact prependAction _ _ _ trivial
          | succ budget =>
              apply prependAction
              constructor
              · intro pair parsed
                have actual : SecurityIndexQuery.parse
                    (indexInput message (answers (.randomizer message))) =
                    some (message, answers (.randomizer message)) :=
                  SecurityIndexQuery.parse_index _ _
                have same : pair =
                    (message, answers (.randomizer message)) := by
                  exact Option.some.inj (parsed.symm.trans actual)
                subst pair
                rfl
              · intro indexAnswer
                intro bottomAnswer
                exact prependAction _ _ _
                  (ih (GroupedBalancedGraphHonestSignView67.signatureFromAnswers
                    cache (answers (.randomizer message))
                    (indexAnswer.extractLsb' 0 160) bottomAnswer) budget)

#print axioms eagerCutoffView_fixed

end SigGolfCandidate.Hypertree.GroupedBalancedIndexFixedNonce67

end

/-! Every retained signer pair in a fixed-nonce View agrees with its private
nonce table, even when public queries and signing answers are adaptive. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPairConsistent67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexFixedNonce67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false
open scoped Classical

def Consistent (nonces : Message → Bytes 32) (audit : Audit) : Prop :=
  ∀ pair ∈ audit.signedPairs, pair.2 = nonces pair.1

theorem empty (nonces : Message → Bytes 32) : Consistent nonces {} := by
  intro pair member
  cases member

theorem publicStep (nonces : Message → Bytes 32) (audit : Audit)
    (pair : Message × Bytes 32) (consistent : Consistent nonces audit) :
    Consistent nonces (GroupedBalancedIndexLabeledAudit67.publicStep audit pair) := by
  by_cases signed : pair.1 ∈ audit.signedMessages <;>
    simpa [Consistent, GroupedBalancedIndexLabeledAudit67.publicStep,
      signed] using consistent

theorem signStep (nonces : Message → Bytes 32) (audit : Audit)
    (pair : Message × Bytes 32) (consistent : Consistent nonces audit)
    (honest : pair.2 = nonces pair.1) :
    Consistent nonces (GroupedBalancedIndexLabeledAudit67.signStep audit pair) := by
  intro earlier member
  by_cases signed : pair.1 ∈ audit.signedMessages
  · have old : earlier ∈ audit.signedPairs := by
      simpa [GroupedBalancedIndexLabeledAudit67.signStep, signed] using member
    exact consistent earlier old
  · have split : earlier = pair ∨ earlier ∈ audit.signedPairs := by
      simpa [GroupedBalancedIndexLabeledAudit67.signStep, signed] using member
    rcases split with same | old
    · simpa [same] using honest
    · exact consistent earlier old

theorem compile_consistent {α : Type} (table : PointTable)
    (nonces : Message → Bytes 32) (view : View α)
    (fixed : FixedNonce nonces view)
    (remaining : Nat) (state : State) (graphCalls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat)
    (audit : Audit) (consistent : Consistent nonces audit) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.compile table view remaining
        state graphCalls signedMessages bad tests) audit),
      Consistent nonces result.2 := by
  induction view generalizing remaining state graphCalls signedMessages bad tests audit with
  | done value =>
      intro result member
      simp only [GroupedBalancedIndexLabeledJoint67.compile, run,
        support_pure, Set.mem_singleton_iff] at member
      subst result
      exact consistent
  | coin n next ih =>
      intro result member
      simp only [GroupedBalancedIndexLabeledJoint67.compile, run,
        mem_support_bind_iff] at member
      obtain ⟨answer, _, child⟩ := member
      exact ih answer (fixed answer) remaining state graphCalls
        signedMessages bad tests audit consistent result child
  | sign index next ih =>
      intro result member
      change result ∈ support (run
        (GroupedBalancedIndexLabeledJoint67.compile table
          (next (table (.inr (.inl index)))) remaining
          (signed state index (table (.inr (.inl index)))) graphCalls
          signedMessages bad tests) audit) at member
      exact ih (table (.inr (.inl index)))
        (fixed (table (.inr (.inl index)))) remaining
        (signed state index (table (.inr (.inl index)))) graphCalls
        signedMessages bad tests audit consistent result member
  | privateHash input outside next ih =>
      intro result member
      cases parsed : SecurityIndexQuery.parse input with
      | some pair =>
          have honest := fixed.1 pair parsed
          have member' : result ∈ support (run
              (GroupedBalancedIndexLabeledJoint67.privateHashStepOn
                (some pair) state input signedMessages
                (fun answer updated signed =>
                  GroupedBalancedIndexLabeledJoint67.compile table
                    (next answer) remaining updated graphCalls signed bad tests))
              audit) := by
            unfold GroupedBalancedIndexLabeledJoint67.compile at member
            rw [parsed] at member
            exact member
          cases cached : state.residual input with
          | some answer =>
              simp only [GroupedBalancedIndexLabeledJoint67.privateHashStepOn,
                GroupedBalancedIndexLabeledLift67.cachedDraw,
                cached, run] at member'
              exact ih answer (fixed.2 answer) remaining state graphCalls
                (insert pair.1 signedMessages) bad tests
                (GroupedBalancedIndexLabeledAudit67.signStep audit pair)
                (signStep nonces audit pair consistent honest)
                result member'
          | none =>
              simp only [GroupedBalancedIndexLabeledJoint67.privateHashStepOn,
                GroupedBalancedIndexLabeledLift67.cachedDraw,
                cached, run, mem_support_bind_iff] at member'
              obtain ⟨answer, _, member'⟩ := member'
              simp only [support_map, Set.mem_image] at member'
              obtain ⟨childResult, childMember, same⟩ := member'
              have childGood := ih answer (fixed.2 answer) remaining
                { state with residual := state.residual.cacheQuery input answer }
                graphCalls (insert pair.1 signedMessages) bad tests
                (GroupedBalancedIndexLabeledAudit67.signStep
                  { audit with
                    h5cache := audit.h5cache.cacheQuery input answer
                    draws := audit.draws ++
                      [(input, (decide (pair.1 ∉ signedMessages),
                        answer.extractLsb' 0 160))] }
                  pair)
                (signStep nonces _ pair
                  (by simpa only [Consistent] using consistent) honest)
                childResult childMember
              have auditEqRaw :=
                congrArg (fun x : (JointOutcome α × List Draw) × Audit => x.2) same
              have auditEq : childResult.2 = result.2 := auditEqRaw
              simpa only [auditEq] using childGood
      | none =>
          have member' : result ∈ support (run
              (GroupedBalancedIndexLabeledJoint67.privateHashStepOn
                none state input signedMessages
                (fun answer updated signed =>
                  GroupedBalancedIndexLabeledJoint67.compile table
                    (next answer) remaining updated graphCalls signed bad tests))
              audit) := by
            unfold GroupedBalancedIndexLabeledJoint67.compile at member
            rw [parsed] at member
            exact member
          rw [GroupedBalancedIndexLabeledJoint67.privateHashStepOn,
            GroupedBalancedIndexLabeledAuditLift67.run_unmarked,
            mem_support_bind_iff] at member'
          obtain ⟨sample, _, childMember⟩ := member'
          rcases sample with ⟨answer, residual⟩
          exact ih answer (fixed.2 answer) remaining
            { state with residual := residual } graphCalls
            signedMessages bad tests audit consistent result childMember
  | hash input next ih =>
      intro result member
      cases remaining with
      | zero =>
          simp only [GroupedBalancedIndexLabeledJoint67.compile, run,
            support_pure, Set.mem_singleton_iff] at member
          subst result
          exact consistent
      | succ remaining =>
          cases parsed : SecurityIndexQuery.parse input with
          | some pair =>
              have member' : result ∈ support (run
                  (GroupedBalancedIndexLabeledJoint67.publicHashStepOn
                    (some pair) table state input graphCalls bad tests
                    (fun answer updated calls bad tests =>
                      GroupedBalancedIndexLabeledJoint67.compile table
                        (next answer) remaining updated calls
                        signedMessages bad tests)) audit) := by
                unfold GroupedBalancedIndexLabeledJoint67.compile at member
                rw [parsed] at member
                exact member
              cases cached : state.residual input with
              | some answer =>
                  simp only [GroupedBalancedIndexLabeledJoint67.publicHashStepOn,
                    GroupedBalancedIndexLabeledLift67.cachedDraw, cached,
                    reduceCtorEq, if_false, run] at member'
                  exact ih answer (fixed answer) remaining state graphCalls
                    signedMessages bad tests audit consistent result member'
              | none =>
                  simp only [GroupedBalancedIndexLabeledJoint67.publicHashStepOn,
                    GroupedBalancedIndexLabeledLift67.cachedDraw, cached,
                    if_true, run, mem_support_bind_iff] at member'
                  obtain ⟨answer, _, member'⟩ := member'
                  simp only [support_map, Set.mem_image] at member'
                  obtain ⟨childResult, childMember, same⟩ := member'
                  have childGood := ih answer (fixed answer) remaining
                    { state with residual := state.residual.cacheQuery input answer }
                    graphCalls signedMessages bad tests
                    { GroupedBalancedIndexLabeledAudit67.publicStep audit pair with
                      h5cache := (GroupedBalancedIndexLabeledAudit67.publicStep audit pair).h5cache.cacheQuery
                        input answer
                      draws := (GroupedBalancedIndexLabeledAudit67.publicStep audit pair).draws ++
                        [(input, (false, answer.extractLsb' 0 160))] }
                    (by simpa only [Consistent] using
                      publicStep nonces audit pair consistent)
                    childResult childMember
                  have auditEqRaw :=
                    congrArg (fun x : (JointOutcome α × List Draw) × Audit => x.2) same
                  have auditEq : childResult.2 = result.2 := auditEqRaw
                  simpa only [auditEq] using childGood
          | none =>
              have member' : result ∈ support (run
                  (GroupedBalancedIndexLabeledJoint67.publicHashStepOn
                    none table state input graphCalls bad tests
                    (fun answer updated calls bad tests =>
                      GroupedBalancedIndexLabeledJoint67.compile table
                        (next answer) remaining updated calls
                        signedMessages bad tests)) audit) := by
                unfold GroupedBalancedIndexLabeledJoint67.compile at member
                rw [parsed] at member
                exact member
              rw [GroupedBalancedIndexLabeledJoint67.publicHashStepOn,
                GroupedBalancedIndexLabeledAuditLift67.run_ofGraphKeep,
                mem_support_bind_iff] at member'
              obtain ⟨graphResult, _, childMember⟩ := member'
              exact ih graphResult.value.1 (fixed graphResult.value.1)
                remaining
                (opened state graphResult.value.2.1 graphResult.value.2.2)
                (graphCalls + if (GroupedBalancedGraphQuery67.locate input).isSome
                  then 1 else 0)
                signedMessages (bad || graphResult.bad)
                (tests + graphResult.tests) audit consistent result childMember

theorem start_consistent {α : Type} (table : PointTable)
    (nonces : Message → Bytes 32)
    (view : QueryCache PointSpec → View α) (remaining : Nat)
    (fixed : FixedNonce nonces
      (view (GroupedBalancedGraphMonitorSetup67.cache table))) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.start table view remaining) {}),
      Consistent nonces result.2 := by
  exact compile_consistent table nonces _ fixed remaining
    (GroupedBalancedGraphMonitorSignBound67.initial
      (GroupedBalancedGraphMonitorSetup67.cache table))
    0 ∅ false 0 {} (empty nonces)

#print axioms compile_consistent
#print axioms start_consistent

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPairConsistent67
