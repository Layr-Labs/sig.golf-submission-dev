import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAgreePrivate67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphPublicResidualFrame67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAgreePublic67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledCompilerAgree67. -/
section
/-! H5 cache agreement across public index reads and ordinary graph reads. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAgreePublic67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledCacheAgree67
open GroupedBalancedIndexLabeledAgreePrivate67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem public_some_step {α : Type} (table : PointTable)
    (state : State) (input : Query)
    (pair : Message × Bytes 32)
    (graphCalls : Nat) (bad : Bool) (tests : Nat)
    (audit : Audit) (agree : H5Agree state.residual audit.h5cache)
    (next : BitVec 256 → State → Nat → Bool → Nat →
      Program (JointOutcome α))
    (child : ∀ answer updated calls bad tests audit',
      H5Agree updated.residual audit'.h5cache →
      ∀ result ∈ support (run
        (next answer updated calls bad tests) audit'), Good result) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.publicHashStepOn
        (some pair) table state input graphCalls bad tests next) audit),
      Good result := by
  intro result member
  cases cached : state.residual input with
  | some answer =>
      simp only [GroupedBalancedIndexLabeledJoint67.publicHashStepOn,
        GroupedBalancedIndexLabeledLift67.cachedDraw, cached,
        reduceCtorEq, if_false, run] at member
      exact child answer state graphCalls bad tests audit agree
        result member
  | none =>
      simp only [GroupedBalancedIndexLabeledJoint67.publicHashStepOn,
        GroupedBalancedIndexLabeledLift67.cachedDraw, cached,
        if_true, run, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      simp only [support_map, Set.mem_image] at member
      obtain ⟨childResult, childMember, same⟩ := member
      subst result
      exact child answer
        { state with residual := state.residual.cacheQuery input answer }
        graphCalls bad tests
        { publicStep audit pair with
          h5cache := (publicStep audit pair).h5cache.cacheQuery
            input answer
          draws := (publicStep audit pair).draws ++
            [(input, (false, answer.extractLsb' 0 160))] }
        (by
          by_cases signed : pair.1 ∈ audit.signedMessages
          · simpa [GroupedBalancedIndexLabeledAudit67.publicStep, signed]
              using (cacheBoth state.residual audit.h5cache agree input answer)
          · simpa [GroupedBalancedIndexLabeledAudit67.publicStep, signed]
              using (cacheBoth state.residual audit.h5cache agree input answer))
        childResult childMember

theorem public_none_step {α : Type} (table : PointTable)
    (state : State) (input : Query)
    (notH5 : SecurityIndexQuery.parse input = none)
    (graphCalls : Nat) (bad : Bool) (tests : Nat)
    (audit : Audit) (agree : H5Agree state.residual audit.h5cache)
    (next : BitVec 256 → State → Nat → Bool → Nat →
      Program (JointOutcome α))
    (child : ∀ answer updated calls bad tests audit',
      H5Agree updated.residual audit'.h5cache →
      ∀ result ∈ support (run
        (next answer updated calls bad tests) audit'), Good result) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.publicHashStepOn
        none table state input graphCalls bad tests next) audit),
      Good result := by
  intro result member
  rw [GroupedBalancedIndexLabeledJoint67.publicHashStepOn,
    GroupedBalancedIndexLabeledAuditLift67.run_ofGraphKeep,
    mem_support_bind_iff] at member
  obtain ⟨graphResult, graphMember, childMember⟩ := member
  have frame := GroupedBalancedGraphPublicResidualFrame67.publicStep_frame
    table state.exposed state.residual input graphResult graphMember
  let updated := opened state graphResult.value.2.1 graphResult.value.2.2
  have h5Agree : H5Agree updated.residual audit.h5cache := by
    rcases frame with unchanged | ⟨answer, cached⟩
    · simpa only [updated, opened, unchanged] using agree
    · simpa only [updated, opened, cached] using
        (cacheNonH5 state.residual audit.h5cache agree input notH5 answer)
  exact child graphResult.value.1 updated
    (graphCalls + if (GroupedBalancedGraphQuery67.locate input).isSome
      then 1 else 0)
    (bad || graphResult.bad) (tests + graphResult.tests)
    audit h5Agree result childMember

#print axioms public_some_step
#print axioms public_none_step

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAgreePublic67

end

/-! Every direct67 joint compiler run has matching actual and ghost tag-5
residual caches. Branch details are isolated in the private/public step files. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledCompilerAgree67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledCacheAgree67
open GroupedBalancedIndexLabeledJoint67
open GroupedBalancedIndexLabeledAgreePrivate67
open GroupedBalancedIndexLabeledAgreePublic67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false
open scoped Classical

theorem compile_h5_agree {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (graphCalls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests : Nat) (audit : Audit)
    (agree : H5Agree state.residual audit.h5cache) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.compile table view remaining
        state graphCalls signedMessages bad tests) audit),
      H5Agree result.1.1.value.state.residual result.2.h5cache := by
  induction view generalizing remaining state graphCalls signedMessages bad tests audit with
  | done value =>
      intro result member
      simp only [GroupedBalancedIndexLabeledJoint67.compile, run,
        support_pure, Set.mem_singleton_iff] at member
      subst result
      exact agree
  | coin n next ih =>
      intro result member
      simp only [GroupedBalancedIndexLabeledJoint67.compile, run,
        mem_support_bind_iff] at member
      obtain ⟨answer, _, child⟩ := member
      exact ih answer remaining state graphCalls signedMessages bad tests
        audit agree result child
  | sign index next ih =>
      intro result member
      change result ∈ support (run
        (GroupedBalancedIndexLabeledJoint67.compile table
          (next (table (.inr (.inl index)))) remaining
          (signed state index (table (.inr (.inl index)))) graphCalls
          signedMessages bad tests) audit) at member
      exact ih (table (.inr (.inl index))) remaining
        (signed state index (table (.inr (.inl index)))) graphCalls
        signedMessages bad tests audit agree result member
  | privateHash input outside next ih =>
      intro result member
      cases parsed : SecurityIndexQuery.parse input with
      | some pair =>
          exact private_some_step state input pair signedMessages audit agree
            (fun answer updated signed =>
              GroupedBalancedIndexLabeledJoint67.compile table
                (next answer) remaining updated graphCalls signed bad tests)
            (fun answer updated signed audit' h5Agree =>
              ih answer remaining updated graphCalls signed bad tests
                audit' h5Agree)
            result (by
              unfold GroupedBalancedIndexLabeledJoint67.compile at member
              rw [parsed] at member
              exact member)
      | none =>
          exact private_none_step state input parsed signedMessages audit agree
            (fun answer updated signed =>
              GroupedBalancedIndexLabeledJoint67.compile table
                (next answer) remaining updated graphCalls signed bad tests)
            (fun answer updated signed audit' h5Agree =>
              ih answer remaining updated graphCalls signed bad tests
                audit' h5Agree)
            result (by
              unfold GroupedBalancedIndexLabeledJoint67.compile at member
              rw [parsed] at member
              exact member)
  | hash input next ih =>
      intro result member
      cases remaining with
      | zero =>
          simp only [GroupedBalancedIndexLabeledJoint67.compile, run,
            support_pure, Set.mem_singleton_iff] at member
          subst result
          exact agree
      | succ remaining =>
          cases parsed : SecurityIndexQuery.parse input with
          | some pair =>
              exact public_some_step table state input pair graphCalls bad tests
                audit agree
                (fun answer updated calls bad tests =>
                  GroupedBalancedIndexLabeledJoint67.compile table
                    (next answer) remaining updated calls signedMessages
                    bad tests)
                (fun answer updated calls bad tests audit' h5Agree =>
                  ih answer remaining updated calls signedMessages bad tests
                    audit' h5Agree)
                result (by
                  unfold GroupedBalancedIndexLabeledJoint67.compile at member
                  rw [parsed] at member
                  exact member)
          | none =>
              exact public_none_step table state input parsed graphCalls bad
                tests audit agree
                (fun answer updated calls bad tests =>
                  GroupedBalancedIndexLabeledJoint67.compile table
                    (next answer) remaining updated calls signedMessages
                    bad tests)
                (fun answer updated calls bad tests audit' h5Agree =>
                  ih answer remaining updated calls signedMessages bad tests
                    audit' h5Agree)
                result (by
                  unfold GroupedBalancedIndexLabeledJoint67.compile at member
                  rw [parsed] at member
                  exact member)

theorem start_h5_agree {α : Type} (table : PointTable)
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.start table view remaining) {}),
      H5Agree result.1.1.value.state.residual result.2.h5cache := by
  exact compile_h5_agree table
    (view (GroupedBalancedGraphMonitorSetup67.cache table)) remaining
    (GroupedBalancedGraphMonitorSignBound67.initial
      (GroupedBalancedGraphMonitorSetup67.cache table))
    0 ∅ false 0 {} empty

#print axioms compile_h5_agree
#print axioms start_h5_agree

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledCompilerAgree67
