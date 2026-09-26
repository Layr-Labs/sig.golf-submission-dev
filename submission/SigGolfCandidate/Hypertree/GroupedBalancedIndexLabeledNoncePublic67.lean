import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledGlobalAgree67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCovered67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNoncePublic67. -/
section
/-! A cached H5 input for an unsigned message must have been queried publicly
before that message was signed. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCovered67
open SigGolf OracleComp OracleSpec Reference SecurityRandomOracle
open GroupedBalancedIndexLabeledAudit67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

def NonceCovered (audit : Audit) : Prop :=
  ∀ message nonce,
    audit.h5cache (indexInput message nonce) ≠ none →
      message ∈ audit.signedMessages ∨
        (message, nonce) ∈ audit.nonceGuesses

theorem empty : NonceCovered {} := by
  intro message nonce present
  exact False.elim (present rfl)

theorem publicStep (audit : Audit) (pair : Message × Bytes 32)
    (covered : NonceCovered audit) :
    NonceCovered (GroupedBalancedIndexLabeledAudit67.publicStep audit pair) := by
  intro message nonce present
  by_cases signed : pair.1 ∈ audit.signedMessages
  · simpa [GroupedBalancedIndexLabeledAudit67.publicStep, signed] using
      covered message nonce (by simpa
        [GroupedBalancedIndexLabeledAudit67.publicStep, signed] using present)
  · have old : audit.h5cache (indexInput message nonce) ≠ none := by
      simpa [GroupedBalancedIndexLabeledAudit67.publicStep, signed] using present
    rcases covered message nonce old with known | guessed
    · exact Or.inl (by simpa
        [GroupedBalancedIndexLabeledAudit67.publicStep, signed] using known)
    · exact Or.inr (by simp
        [GroupedBalancedIndexLabeledAudit67.publicStep, signed, guessed])

theorem publicFill (audit : Audit) (pair : Message × Bytes 32)
    (answer : BitVec 256) (covered : NonceCovered audit) :
    NonceCovered
      { GroupedBalancedIndexLabeledAudit67.publicStep audit pair with
        h5cache := audit.h5cache.cacheQuery
          (indexInput pair.1 pair.2) answer } := by
  intro message nonce present
  by_cases same : indexInput message nonce = indexInput pair.1 pair.2
  · have pairs := @SecurityForgery.indexInput_pair_injective
      (message, nonce) pair same
    have messageEq : message = pair.1 := congrArg Prod.fst pairs
    have nonceEq : nonce = pair.2 := congrArg Prod.snd pairs
    subst message
    subst nonce
    by_cases signed : pair.1 ∈ audit.signedMessages
    · exact Or.inl (by simpa only
        [GroupedBalancedIndexLabeledAudit67.publicStep, signed, if_pos] using signed)
    · exact Or.inr (by simp
        [GroupedBalancedIndexLabeledAudit67.publicStep, signed])
  · have old : audit.h5cache (indexInput message nonce) ≠ none := by
      simpa only [QueryCache.cacheQuery_of_ne _ _ same] using present
    have oldStep :
        (GroupedBalancedIndexLabeledAudit67.publicStep audit pair).h5cache
          (indexInput message nonce) ≠ none := by
      by_cases signed : pair.1 ∈ audit.signedMessages <;>
        simpa [GroupedBalancedIndexLabeledAudit67.publicStep, signed] using old
    exact publicStep audit pair covered message nonce oldStep

theorem signStep (audit : Audit) (pair : Message × Bytes 32)
    (covered : NonceCovered audit) :
    NonceCovered (GroupedBalancedIndexLabeledAudit67.signStep audit pair) := by
  intro message nonce present
  rcases covered message nonce present with known | guessed
  · exact Or.inl (Finset.mem_insert_of_mem known)
  · exact Or.inr guessed

theorem signFill (audit : Audit) (pair : Message × Bytes 32)
    (answer : BitVec 256) (covered : NonceCovered audit) :
    NonceCovered
      (GroupedBalancedIndexLabeledAudit67.signStep
        { audit with
          h5cache := audit.h5cache.cacheQuery
            (indexInput pair.1 pair.2) answer }
        pair) := by
  intro message nonce present
  by_cases same : indexInput message nonce = indexInput pair.1 pair.2
  · have pairs := @SecurityForgery.indexInput_pair_injective
      (message, nonce) pair same
    have messageEq : message = pair.1 := congrArg Prod.fst pairs
    subst message
    exact Or.inl (Finset.mem_insert_self _ _)
  · have old : audit.h5cache (indexInput message nonce) ≠ none := by
      simpa only [GroupedBalancedIndexLabeledAudit67.signStep,
        QueryCache.cacheQuery_of_ne _ _ same] using present
    rcases covered message nonce old with known | guessed
    · exact Or.inl (Finset.mem_insert_of_mem known)
    · exact Or.inr guessed

theorem firstSignHit (audit : Audit) (covered : NonceCovered audit)
    (message : Message) (nonce : Bytes 32)
    (unsigned : message ∉ audit.signedMessages)
    (present : audit.h5cache (indexInput message nonce) ≠ none) :
    (message, nonce) ∈ audit.nonceGuesses :=
  (covered message nonce present).resolve_left unsigned

#print axioms publicFill
#print axioms signFill
#print axioms firstSignHit

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCovered67
end

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNoncePrivate67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNoncePublic67. -/
section
/-! The private H5 signer step preserves nonce coverage. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNoncePrivate67
open SigGolf OracleComp OracleSpec Reference SecurityRandomOracle
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledNonceCovered67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option linter.constructorNameAsVariable false

theorem private_some_step {α : Type}
    (state : State) (input : Query)
    (pair : Message × Bytes 32)
    (parsed : SecurityIndexQuery.parse input = some pair)
    (signedMessages : Finset Message) (audit : Audit)
    (covered : NonceCovered audit)
    (next : BitVec 256 → State → Finset Message →
      Program (JointOutcome α))
    (child : ∀ answer updated signed audit',
      NonceCovered audit' →
      ∀ result ∈ support (run (next answer updated signed) audit'),
        NonceCovered result.2) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.privateHashStepOn
        (some pair) state input signedMessages next) audit),
      NonceCovered result.2 := by
  intro result member
  have inputEq : indexInput pair.1 pair.2 = input :=
    (SecurityIndexQuery.parse_some_iff input pair).1 parsed
  cases cached : state.residual input with
  | some answer =>
      simp only [GroupedBalancedIndexLabeledJoint67.privateHashStepOn,
        GroupedBalancedIndexLabeledLift67.cachedDraw,
        cached, run] at member
      exact child answer state (insert pair.1 signedMessages)
        (signStep audit pair)
        (GroupedBalancedIndexLabeledNonceCovered67.signStep audit pair covered)
        result member
  | none =>
      simp only [GroupedBalancedIndexLabeledJoint67.privateHashStepOn,
        GroupedBalancedIndexLabeledLift67.cachedDraw,
        cached, run, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      simp only [support_map, Set.mem_image] at member
      obtain ⟨childResult, childMember, same⟩ := member
      subst result
      have fresh : NonceCovered (GroupedBalancedIndexLabeledAudit67.signStep
          { audit with
            h5cache := audit.h5cache.cacheQuery input answer
            draws := audit.draws ++
              [(input, (decide (pair.1 ∉ signedMessages),
                answer.extractLsb' 0 160))] }
          pair) := by
        rw [← inputEq]
        simpa only [NonceCovered, GroupedBalancedIndexLabeledAudit67.signStep] using
          (GroupedBalancedIndexLabeledNonceCovered67.signFill audit pair answer covered)
      exact child answer
        { state with residual := state.residual.cacheQuery input answer }
        (insert pair.1 signedMessages)
        (signStep
          { audit with
            h5cache := audit.h5cache.cacheQuery input answer
            draws := audit.draws ++
              [(input, (decide (pair.1 ∉ signedMessages),
                answer.extractLsb' 0 160))] }
          pair)
        fresh childResult childMember

theorem private_none_step {α : Type}
    (state : State) (input : Query)
    (signedMessages : Finset Message) (audit : Audit)
    (covered : NonceCovered audit)
    (next : BitVec 256 → State → Finset Message →
      Program (JointOutcome α))
    (child : ∀ answer updated signed audit',
      NonceCovered audit' →
      ∀ result ∈ support (run (next answer updated signed) audit'),
        NonceCovered result.2) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.privateHashStepOn
        none state input signedMessages next) audit),
      NonceCovered result.2 := by
  intro result member
  rw [GroupedBalancedIndexLabeledJoint67.privateHashStepOn,
    GroupedBalancedIndexLabeledAuditLift67.run_unmarked,
    mem_support_bind_iff] at member
  obtain ⟨sample, _, childMember⟩ := member
  rcases sample with ⟨answer, residual⟩
  exact child answer { state with residual := residual }
    signedMessages audit covered result childMember

#print axioms private_some_step
#print axioms private_none_step

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNoncePrivate67

end

/-! Public H5 reads record prereveal pairs before filling the audit cache. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNoncePublic67
open SigGolf OracleComp OracleSpec Reference SecurityRandomOracle
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledNonceCovered67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option linter.constructorNameAsVariable false

theorem public_some_step {α : Type} (table : PointTable)
    (state : State) (input : Query)
    (pair : Message × Bytes 32)
    (parsed : SecurityIndexQuery.parse input = some pair)
    (graphCalls : Nat) (bad : Bool) (tests : Nat)
    (audit : Audit) (covered : NonceCovered audit)
    (next : BitVec 256 → State → Nat → Bool → Nat →
      Program (JointOutcome α))
    (child : ∀ answer updated calls bad tests audit',
      NonceCovered audit' →
      ∀ result ∈ support (run
        (next answer updated calls bad tests) audit'),
        NonceCovered result.2) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.publicHashStepOn
        (some pair) table state input graphCalls bad tests next) audit),
      NonceCovered result.2 := by
  intro result member
  have inputEq : indexInput pair.1 pair.2 = input :=
    (SecurityIndexQuery.parse_some_iff input pair).1 parsed
  cases cached : state.residual input with
  | some answer =>
      simp only [GroupedBalancedIndexLabeledJoint67.publicHashStepOn,
        GroupedBalancedIndexLabeledLift67.cachedDraw, cached,
        reduceCtorEq, if_false, run] at member
      exact child answer state graphCalls bad tests audit covered
        result member
  | none =>
      simp only [GroupedBalancedIndexLabeledJoint67.publicHashStepOn,
        GroupedBalancedIndexLabeledLift67.cachedDraw, cached,
        if_true, run, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      simp only [support_map, Set.mem_image] at member
      obtain ⟨childResult, childMember, same⟩ := member
      subst result
      have filled : NonceCovered
          { GroupedBalancedIndexLabeledAudit67.publicStep audit pair with
            h5cache := (GroupedBalancedIndexLabeledAudit67.publicStep audit pair).h5cache.cacheQuery input answer
            draws := (GroupedBalancedIndexLabeledAudit67.publicStep audit pair).draws ++
              [(input, (false, answer.extractLsb' 0 160))] } := by
        rw [← inputEq]
        by_cases signed : pair.1 ∈ audit.signedMessages
        · simpa [NonceCovered, GroupedBalancedIndexLabeledAudit67.publicStep,
            signed] using (publicFill audit pair answer covered)
        · simpa [NonceCovered, GroupedBalancedIndexLabeledAudit67.publicStep,
            signed] using (publicFill audit pair answer covered)
      exact child answer
        { state with residual := state.residual.cacheQuery input answer }
        graphCalls bad tests
        { GroupedBalancedIndexLabeledAudit67.publicStep audit pair with
          h5cache := (GroupedBalancedIndexLabeledAudit67.publicStep audit pair).h5cache.cacheQuery input answer
          draws := (GroupedBalancedIndexLabeledAudit67.publicStep audit pair).draws ++
            [(input, (false, answer.extractLsb' 0 160))] }
        filled childResult childMember

theorem public_none_step {α : Type} (table : PointTable)
    (state : State) (input : Query)
    (graphCalls : Nat) (bad : Bool) (tests : Nat)
    (audit : Audit) (covered : NonceCovered audit)
    (next : BitVec 256 → State → Nat → Bool → Nat →
      Program (JointOutcome α))
    (child : ∀ answer updated calls bad tests audit',
      NonceCovered audit' →
      ∀ result ∈ support (run
        (next answer updated calls bad tests) audit'),
        NonceCovered result.2) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.publicHashStepOn
        none table state input graphCalls bad tests next) audit),
      NonceCovered result.2 := by
  intro result member
  rw [GroupedBalancedIndexLabeledJoint67.publicHashStepOn,
    GroupedBalancedIndexLabeledAuditLift67.run_ofGraphKeep,
    mem_support_bind_iff] at member
  obtain ⟨graphResult, _, childMember⟩ := member
  exact child graphResult.value.1
    (opened state graphResult.value.2.1 graphResult.value.2.2)
    (graphCalls + if (GroupedBalancedGraphQuery67.locate input).isSome
      then 1 else 0)
    (bad || graphResult.bad) (tests + graphResult.tests)
    audit covered result childMember

#print axioms public_some_step
#print axioms public_none_step

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNoncePublic67
