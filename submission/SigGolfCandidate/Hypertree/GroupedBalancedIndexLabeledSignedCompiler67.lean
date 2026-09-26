import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledSignedState67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphPublicResidualFrame67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledSignedStatePublic67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledSignedCompiler67. -/
section
/-! Public H5 and graph reads preserve the first-signer state invariant. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledSignedStatePublic67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledCacheAgree67
open GroupedBalancedIndexLabeledNonceCovered67
open GroupedBalancedIndexLabeledSignedWitness67
open GroupedBalancedIndexLabeledDrawFaithful67
open GroupedBalancedIndexLabeledSignedState67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option linter.constructorNameAsVariable false
open scoped Classical

theorem publicFresh (state : State) (signedMessages : Finset Message)
    (audit : Audit) (sound : Sound state signedMessages audit)
    (input : Query) (pair : Message × Bytes 32)
    (parsed : SecurityIndexQuery.parse input = some pair)
    (answer : BitVec 256)
    (miss : state.residual input = none) :
    Sound
      { state with residual := state.residual.cacheQuery input answer }
      signedMessages
      { GroupedBalancedIndexLabeledAudit67.publicStep audit pair with
        h5cache := (GroupedBalancedIndexLabeledAudit67.publicStep audit pair).h5cache.cacheQuery input answer
        draws := (GroupedBalancedIndexLabeledAudit67.publicStep audit pair).draws ++
          [(input, (false, answer.extractLsb' 0 160))] } := by
  have inputEq : SecurityRandomOracle.indexInput pair.1 pair.2 = input :=
    (SecurityIndexQuery.parse_some_iff input pair).1 parsed
  subst input
  let advanced := GroupedBalancedIndexLabeledAudit67.publicStep audit pair
  let updated : Audit :=
    { advanced with
      h5cache := advanced.h5cache.cacheQuery
        (SecurityRandomOracle.indexInput pair.1 pair.2) answer
      draws := advanced.draws ++
        [(SecurityRandomOracle.indexInput pair.1 pair.2,
          (false, answer.extractLsb' 0 160))] }
  have filled : NonceCovered updated := by
    by_cases signed : pair.1 ∈ audit.signedMessages
    · simpa [updated, advanced, NonceCovered,
        GroupedBalancedIndexLabeledAudit67.publicStep, signed] using
        (GroupedBalancedIndexLabeledNonceCovered67.publicFill
          audit pair answer sound.nonceCovered)
    · simpa [updated, advanced, NonceCovered,
        GroupedBalancedIndexLabeledAudit67.publicStep, signed] using
        (GroupedBalancedIndexLabeledNonceCovered67.publicFill
          audit pair answer sound.nonceCovered)
  have witnessed : SignedWitness updated :=
    GroupedBalancedIndexLabeledSignedWitness67.drawStep advanced
      (SecurityRandomOracle.indexInput pair.1 pair.2) false answer
      (GroupedBalancedIndexLabeledSignedWitness67.publicStep
        audit pair sound.witness)
  have ghostMiss : advanced.h5cache
      (SecurityRandomOracle.indexInput pair.1 pair.2) = none := by
    by_cases signed : pair.1 ∈ audit.signedMessages
    · simpa [advanced, GroupedBalancedIndexLabeledAudit67.publicStep,
        signed, ← sound.agree pair.1 pair.2] using miss
    · simpa [advanced, GroupedBalancedIndexLabeledAudit67.publicStep,
        signed, ← sound.agree pair.1 pair.2] using miss
  have faithfulAdvanced : DrawFaithful advanced :=
    GroupedBalancedIndexLabeledDrawFaithful67.publicStep
      audit pair sound.faithful
  have faithfulUpdated : DrawFaithful updated :=
    GroupedBalancedIndexLabeledDrawFaithful67.drawStep advanced
      (SecurityRandomOracle.indexInput pair.1 pair.2) false answer
      faithfulAdvanced ghostMiss
  constructor
  · by_cases signed : pair.1 ∈ audit.signedMessages
    · simpa [updated, advanced,
        GroupedBalancedIndexLabeledAudit67.publicStep, signed] using
        (cacheBoth state.residual audit.h5cache sound.agree
          (SecurityRandomOracle.indexInput pair.1 pair.2) answer)
    · simpa [updated, advanced,
        GroupedBalancedIndexLabeledAudit67.publicStep, signed] using
        (cacheBoth state.residual audit.h5cache sound.agree
          (SecurityRandomOracle.indexInput pair.1 pair.2) answer)
  · exact filled
  · by_cases signed : pair.1 ∈ audit.signedMessages <;>
      simpa [updated, advanced,
        GroupedBalancedIndexLabeledAudit67.publicStep, signed]
        using sound.signedEq
  · exact witnessed
  · exact faithfulUpdated

theorem publicOther (table : PointTable) (state : State)
    (signedMessages : Finset Message) (audit : Audit)
    (sound : Sound state signedMessages audit)
    (input : Query) (notH5 : SecurityIndexQuery.parse input = none)
    (graphResult : GroupedBalancedGraphMonitorProgram67.Outcome
      (BitVec 256 × QueryCache PointSpec × QueryCache HashSpec))
    (member : graphResult ∈ support
      (GroupedBalancedGraphMonitorProgram67.run table state.exposed
        (GroupedBalancedGraphMonitorOracle67.publicStep
          state.exposed state.residual input
          (fun answer exposed residual =>
            .done (answer, exposed, residual))))) :
    Sound
      (opened state graphResult.value.2.1 graphResult.value.2.2)
      signedMessages audit := by
  have frame := GroupedBalancedGraphPublicResidualFrame67.publicStep_frame
    table state.exposed state.residual input graphResult member
  constructor
  · rcases frame with unchanged | ⟨answer, cached⟩
    · simpa only [opened, unchanged] using sound.agree
    · simpa only [opened, cached] using
        (cacheNonH5 state.residual audit.h5cache sound.agree
          input notH5 answer)
  · exact sound.nonceCovered
  · exact sound.signedEq
  · exact sound.witness
  · exact sound.faithful

theorem privateOther (state : State)
    (signedMessages : Finset Message) (audit : Audit)
    (sound : Sound state signedMessages audit)
    (input : Query) (notH5 : SecurityIndexQuery.parse input = none)
    (answer : BitVec 256) :
    Sound
      { state with residual := state.residual.cacheQuery input answer }
      signedMessages audit := by
  constructor
  · exact cacheNonH5 state.residual audit.h5cache sound.agree
      input notH5 answer
  · exact sound.nonceCovered
  · exact sound.signedEq
  · exact sound.witness
  · exact sound.faithful

#print axioms publicFresh
#print axioms publicOther
#print axioms privateOther

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledSignedStatePublic67

end

/-! Every first signer call in the stopped labelled joint compiler leaves a
prereveal nonce guess or a marked H5 draw. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledSignedCompiler67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledSignedWitness67
open GroupedBalancedIndexLabeledDrawFaithful67
open GroupedBalancedIndexLabeledSignedState67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false
open scoped Classical

theorem compile_signed_witness {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (graphCalls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests : Nat) (audit : Audit)
    (sound : Sound state signedMessages audit) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.compile table view remaining
        state graphCalls signedMessages bad tests) audit),
      SignedWitness result.2 ∧ DrawFaithful result.2 := by
  induction view generalizing remaining state graphCalls signedMessages bad tests audit with
  | done value =>
      intro result member
      simp only [GroupedBalancedIndexLabeledJoint67.compile, run,
        support_pure, Set.mem_singleton_iff] at member
      subst result
      exact ⟨sound.witness, sound.faithful⟩
  | coin n next ih =>
      intro result member
      simp only [GroupedBalancedIndexLabeledJoint67.compile, run,
        mem_support_bind_iff] at member
      obtain ⟨answer, _, child⟩ := member
      exact ih answer remaining state graphCalls signedMessages bad tests
        audit sound result child
  | sign index next ih =>
      intro result member
      change result ∈ support (run
        (GroupedBalancedIndexLabeledJoint67.compile table
          (next (table (.inr (.inl index)))) remaining
          (signed state index (table (.inr (.inl index)))) graphCalls
          signedMessages bad tests) audit) at member
      exact ih (table (.inr (.inl index))) remaining
        (signed state index (table (.inr (.inl index)))) graphCalls
        signedMessages bad tests audit
        (GroupedBalancedIndexLabeledSignedState67.signedBottom
          state signedMessages audit sound index
          (table (.inr (.inl index)))) result member
  | privateHash input outside next ih =>
      intro result member
      cases parsed : SecurityIndexQuery.parse input with
      | some pair =>
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
              exact ih answer remaining state graphCalls
                (insert pair.1 signedMessages) bad tests
                (GroupedBalancedIndexLabeledAudit67.signStep audit pair)
                (GroupedBalancedIndexLabeledSignedState67.privateCached
                  state signedMessages audit sound input pair parsed
                  answer cached) result member'
          | none =>
              simp only [GroupedBalancedIndexLabeledJoint67.privateHashStepOn,
                GroupedBalancedIndexLabeledLift67.cachedDraw,
                cached, run, mem_support_bind_iff] at member'
              obtain ⟨answer, _, member'⟩ := member'
              simp only [support_map, Set.mem_image] at member'
              obtain ⟨childResult, childMember, same⟩ := member'
              have childGood := ih answer remaining
                { state with residual := state.residual.cacheQuery input answer }
                graphCalls (insert pair.1 signedMessages) bad tests
                (GroupedBalancedIndexLabeledAudit67.signStep
                  { audit with
                    h5cache := audit.h5cache.cacheQuery input answer
                    draws := audit.draws ++
                      [(input, (decide (pair.1 ∉ signedMessages),
                        answer.extractLsb' 0 160))] }
                  pair)
                (GroupedBalancedIndexLabeledSignedState67.privateFresh
                  state signedMessages audit sound input pair parsed answer
                  cached)
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
          obtain ⟨sample, sampled, childMember⟩ := member'
          rcases sample with ⟨answer, residual⟩
          cases cached : state.residual input with
          | some known =>
              simp only [randomOracle.run_eq, cached,
                support_pure, Set.mem_singleton_iff] at sampled
              cases sampled
              exact ih answer remaining state graphCalls signedMessages
                bad tests audit sound result childMember
          | none =>
              simp only [randomOracle.run_eq, cached,
                mem_support_bind_iff] at sampled
              obtain ⟨fresh, _, sampled⟩ := sampled
              simp only [support_pure, Set.mem_singleton_iff] at sampled
              cases sampled
              exact ih answer remaining
                { state with residual := state.residual.cacheQuery input answer }
                graphCalls signedMessages bad tests audit
                (GroupedBalancedIndexLabeledSignedStatePublic67.privateOther
                  state signedMessages audit sound input parsed answer)
                result childMember
  | hash input next ih =>
      intro result member
      cases remaining with
      | zero =>
          simp only [GroupedBalancedIndexLabeledJoint67.compile, run,
            support_pure, Set.mem_singleton_iff] at member
          subst result
          exact ⟨sound.witness, sound.faithful⟩
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
                  exact ih answer remaining state graphCalls signedMessages
                    bad tests audit sound result member'
              | none =>
                  simp only [GroupedBalancedIndexLabeledJoint67.publicHashStepOn,
                    GroupedBalancedIndexLabeledLift67.cachedDraw, cached,
                    if_true, run, mem_support_bind_iff] at member'
                  obtain ⟨answer, _, member'⟩ := member'
                  simp only [support_map, Set.mem_image] at member'
                  obtain ⟨childResult, childMember, same⟩ := member'
                  have childGood := ih answer remaining
                    { state with residual := state.residual.cacheQuery input answer }
                    graphCalls signedMessages bad tests
                    { GroupedBalancedIndexLabeledAudit67.publicStep audit pair with
                      h5cache := (GroupedBalancedIndexLabeledAudit67.publicStep audit pair).h5cache.cacheQuery
                        input answer
                      draws := (GroupedBalancedIndexLabeledAudit67.publicStep audit pair).draws ++
                        [(input, (false, answer.extractLsb' 0 160))] }
                    (GroupedBalancedIndexLabeledSignedStatePublic67.publicFresh
                      state signedMessages audit sound input pair parsed answer
                      cached)
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
              obtain ⟨graphResult, graphMember, childMember⟩ := member'
              exact ih graphResult.value.1 remaining
                (opened state graphResult.value.2.1 graphResult.value.2.2)
                (graphCalls + if (GroupedBalancedGraphQuery67.locate input).isSome
                  then 1 else 0)
                signedMessages (bad || graphResult.bad)
                (tests + graphResult.tests) audit
                (GroupedBalancedIndexLabeledSignedStatePublic67.publicOther
                  table state signedMessages audit sound input parsed
                  graphResult graphMember)
                result childMember

theorem start_signed_sound {α : Type} (table : PointTable)
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.start table view remaining) {}),
      SignedWitness result.2 ∧ DrawFaithful result.2 := by
  apply compile_signed_witness table
    (view (GroupedBalancedGraphMonitorSetup67.cache table)) remaining
    (GroupedBalancedGraphMonitorSignBound67.initial
      (GroupedBalancedGraphMonitorSetup67.cache table))
    0 ∅ false 0 {}
  exact GroupedBalancedIndexLabeledSignedState67.empty _ rfl

theorem start_signed_witness {α : Type} (table : PointTable)
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.start table view remaining) {}),
      SignedWitness result.2 := by
  intro result member
  exact (start_signed_sound table view remaining result member).1

theorem start_draw_faithful {α : Type} (table : PointTable)
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.start table view remaining) {}),
      DrawFaithful result.2 := by
  intro result member
  exact (start_signed_sound table view remaining result member).2

#print axioms compile_signed_witness
#print axioms start_signed_witness
#print axioms start_draw_faithful

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledSignedCompiler67
