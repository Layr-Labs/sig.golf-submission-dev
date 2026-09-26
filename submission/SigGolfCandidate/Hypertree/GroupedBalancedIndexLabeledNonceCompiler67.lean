import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNoncePublic67

/-! Nonce coverage for the complete labelled joint compiler. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCompiler67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledNonceCovered67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false
open scoped Classical

theorem compile_nonce_covered {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (graphCalls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests : Nat) (audit : Audit)
    (covered : NonceCovered audit) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.compile table view remaining
        state graphCalls signedMessages bad tests) audit),
      NonceCovered result.2 := by
  induction view generalizing remaining state graphCalls signedMessages bad tests audit with
  | done value =>
      intro result member
      simp only [GroupedBalancedIndexLabeledJoint67.compile, run,
        support_pure, Set.mem_singleton_iff] at member
      subst result
      exact covered
  | coin n next ih =>
      intro result member
      simp only [GroupedBalancedIndexLabeledJoint67.compile, run,
        mem_support_bind_iff] at member
      obtain ⟨answer, _, child⟩ := member
      exact ih answer remaining state graphCalls signedMessages bad tests
        audit covered result child
  | sign index next ih =>
      intro result member
      change result ∈ support (run
        (GroupedBalancedIndexLabeledJoint67.compile table
          (next (table (.inr (.inl index)))) remaining
          (signed state index (table (.inr (.inl index)))) graphCalls
          signedMessages bad tests) audit) at member
      exact ih (table (.inr (.inl index))) remaining
        (signed state index (table (.inr (.inl index)))) graphCalls
        signedMessages bad tests audit covered result member
  | privateHash input outside next ih =>
      intro result member
      cases parsed : SecurityIndexQuery.parse input with
      | some pair =>
          exact GroupedBalancedIndexLabeledNoncePrivate67.private_some_step
            state input pair parsed signedMessages audit covered
            (fun answer updated signed =>
              GroupedBalancedIndexLabeledJoint67.compile table
                (next answer) remaining updated graphCalls signed bad tests)
            (fun answer updated signed audit' covered' =>
              ih answer remaining updated graphCalls signed bad tests
                audit' covered')
            result (by
              unfold GroupedBalancedIndexLabeledJoint67.compile at member
              rw [parsed] at member
              exact member)
      | none =>
          exact GroupedBalancedIndexLabeledNoncePrivate67.private_none_step
            state input signedMessages audit covered
            (fun answer updated signed =>
              GroupedBalancedIndexLabeledJoint67.compile table
                (next answer) remaining updated graphCalls signed bad tests)
            (fun answer updated signed audit' covered' =>
              ih answer remaining updated graphCalls signed bad tests
                audit' covered')
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
          exact covered
      | succ remaining =>
          cases parsed : SecurityIndexQuery.parse input with
          | some pair =>
              exact GroupedBalancedIndexLabeledNoncePublic67.public_some_step
                table state input pair parsed graphCalls bad tests audit covered
                (fun answer updated calls bad tests =>
                  GroupedBalancedIndexLabeledJoint67.compile table
                    (next answer) remaining updated calls signedMessages
                    bad tests)
                (fun answer updated calls bad tests audit' covered' =>
                  ih answer remaining updated calls signedMessages bad tests
                    audit' covered')
                result (by
                  unfold GroupedBalancedIndexLabeledJoint67.compile at member
                  rw [parsed] at member
                  exact member)
          | none =>
              exact GroupedBalancedIndexLabeledNoncePublic67.public_none_step
                table state input graphCalls bad tests audit covered
                (fun answer updated calls bad tests =>
                  GroupedBalancedIndexLabeledJoint67.compile table
                    (next answer) remaining updated calls signedMessages
                    bad tests)
                (fun answer updated calls bad tests audit' covered' =>
                  ih answer remaining updated calls signedMessages bad tests
                    audit' covered')
                result (by
                  unfold GroupedBalancedIndexLabeledJoint67.compile at member
                  rw [parsed] at member
                  exact member)

theorem start_nonce_covered {α : Type} (table : PointTable)
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.start table view remaining) {}),
      NonceCovered result.2 := by
  exact compile_nonce_covered table
    (view (GroupedBalancedGraphMonitorSetup67.cache table)) remaining
    (GroupedBalancedGraphMonitorSignBound67.initial
      (GroupedBalancedGraphMonitorSetup67.cache table))
    0 ∅ false 0 {} empty

#print axioms compile_nonce_covered
#print axioms start_nonce_covered

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCompiler67
