import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAudit67
import SigGolfCandidate.Hypertree.SecurityIndexQuery
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAuditLift67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledCoverage67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAgreePrivate67. -/
section
/-! Every entry in the audit's H5 cache has a matching input-labelled fresh
draw. This is independent of the graph and attacker continuation. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledCoverage67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

def Covered (audit : Audit) : Prop :=
  ∀ input answer, audit.h5cache input = some answer →
    ∃ mark, (input, (mark, answer.extractLsb' 0 160)) ∈ audit.draws

theorem covered_empty : Covered {} := by
  intro input answer present
  cases present

theorem Covered.publicStep (audit : Audit) (pair : Message × Bytes 32)
    (covered : Covered audit) :
    Covered (GroupedBalancedIndexLabeledAudit67.publicStep audit pair) := by
  by_cases signed : pair.1 ∈ audit.signedMessages
  · simpa [GroupedBalancedIndexLabeledAudit67.publicStep, signed] using covered
  · simpa [GroupedBalancedIndexLabeledAudit67.publicStep, signed, Covered] using covered

theorem Covered.signStep (audit : Audit) (pair : Message × Bytes 32)
    (covered : Covered audit) :
    Covered (GroupedBalancedIndexLabeledAudit67.signStep audit pair) := covered

theorem Covered.drawStep (audit : Audit) (input : Query)
    (mark : Bool) (answer : BitVec 256)
    (covered : Covered audit) :
    Covered { audit with
      h5cache := audit.h5cache.cacheQuery input answer
      draws := audit.draws ++
        [(input, (mark, answer.extractLsb' 0 160))] } := by
  intro query value present
  by_cases same : query = input
  · subst query
    have valueEq : value = answer := by
      simpa only [QueryCache.cacheQuery_self, Option.some.injEq] using present.symm
    subst value
    exact ⟨mark, List.mem_append.mpr
      (Or.inr (List.mem_singleton_self _))⟩
  · have old : audit.h5cache query = some value := by
      simpa only [QueryCache.cacheQuery_of_ne _ _ same] using present
    obtain ⟨oldMark, member⟩ := covered query value old
    exact ⟨oldMark, List.mem_append.mpr (Or.inl member)⟩

theorem run_covered {α : Type} (program : Program α)
    (audit : Audit) (covered : Covered audit) :
    ∀ result ∈ support (run program audit), Covered result.2 := by
  induction program generalizing audit with
  | pure value =>
      intro result member
      simp only [run, support_pure, Set.mem_singleton_iff] at member
      subst result
      exact covered
  | recordPublic pair next ih =>
      exact ih (publicStep audit pair)
        (Covered.publicStep audit pair covered)
  | recordSign pair next ih =>
      exact ih (signStep audit pair)
        (Covered.signStep audit pair covered)
  | coin n next ih =>
      intro result member
      simp only [run, mem_support_bind_iff] at member
      obtain ⟨answer, _, child⟩ := member
      exact ih answer audit covered result child
  | draw input mark next ih =>
      intro result member
      simp only [run, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      simp only [support_map, Set.mem_image] at member
      obtain ⟨child, childMember, same⟩ := member
      subst result
      exact ih answer _ (Covered.drawStep audit input mark answer covered)
        child childMember

theorem run_draws_append {α : Type} (program : Program α)
    (audit : Audit) :
    ∀ result ∈ support (run program audit),
      result.2.draws = audit.draws ++ result.1.2 := by
  induction program generalizing audit with
  | pure value =>
      intro result member
      simp only [run, support_pure, Set.mem_singleton_iff] at member
      subst result
      simp
  | recordPublic pair next ih =>
      intro result member
      have eq := ih (publicStep audit pair) result member
      by_cases signed : pair.1 ∈ audit.signedMessages
      · simpa [GroupedBalancedIndexLabeledAudit67.publicStep, signed] using eq
      · simpa [GroupedBalancedIndexLabeledAudit67.publicStep, signed] using eq
  | recordSign pair next ih =>
      intro result member
      have eq := ih (signStep audit pair) result member
      simpa only [signStep] using eq
  | coin n next ih =>
      intro result member
      simp only [run, mem_support_bind_iff] at member
      obtain ⟨answer, _, child⟩ := member
      exact ih answer audit result child
  | draw input mark next ih =>
      intro result member
      simp only [run, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      simp only [support_map, Set.mem_image] at member
      obtain ⟨child, childMember, same⟩ := member
      subst result
      have eq := ih answer
        { audit with
          h5cache := audit.h5cache.cacheQuery input answer
          draws := audit.draws ++
            [(input, (mark, answer.extractLsb' 0 160))] }
        child childMember
      simpa only [List.append_assoc, List.singleton_append] using eq

theorem run_empty_cache_covered {α : Type} (program : Program α)
    (result : (α × List Draw) × Audit)
    (member : result ∈ support (run program {})) :
    ∀ input answer, result.2.h5cache input = some answer →
      ∃ mark,
        (input, (mark, answer.extractLsb' 0 160)) ∈ result.1.2 := by
  have covered := run_covered program {} covered_empty result member
  have draws := run_draws_append program {} result member
  intro input answer present
  obtain ⟨mark, found⟩ := covered input answer present
  refine ⟨mark, ?_⟩
  rw [draws] at found
  simpa using found

#print axioms covered_empty
#print axioms Covered.drawStep
#print axioms run_covered
#print axioms run_draws_append
#print axioms run_empty_cache_covered

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledCoverage67
end

/-! The audit cache and real residual cache need agree only on canonical tag-5
inputs. Other oracle domains can be updated without affecting this relation. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledCacheAgree67
open SigGolf OracleComp OracleSpec Reference SecurityRandomOracle
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

def H5Agree (residual ghost : QueryCache HashSpec) : Prop :=
  ∀ message nonce,
    residual (indexInput message nonce) =
      ghost (indexInput message nonce)

theorem empty : H5Agree ∅ ∅ := by
  intro message nonce
  rfl

theorem cacheBoth (residual ghost : QueryCache HashSpec)
    (agree : H5Agree residual ghost) (query : Query)
    (answer : BitVec 256) :
    H5Agree (residual.cacheQuery query answer)
      (ghost.cacheQuery query answer) := by
  intro message nonce
  by_cases same : indexInput message nonce = query
  · rw [same, QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ same,
      QueryCache.cacheQuery_of_ne _ _ same]
    exact agree message nonce

theorem cacheNonH5 (residual ghost : QueryCache HashSpec)
    (agree : H5Agree residual ghost) (query : Query)
    (notH5 : SecurityIndexQuery.parse query = none)
    (answer : BitVec 256) :
    H5Agree (residual.cacheQuery query answer) ghost := by
  intro message nonce
  have distinct :=
    (SecurityIndexQuery.parse_none_iff query).1 notH5 message nonce
  rw [QueryCache.cacheQuery_of_ne _ _ distinct]
  exact agree message nonce

theorem signed (residual ghost : QueryCache HashSpec)
    (agree : H5Agree residual ghost) :
    H5Agree residual ghost := agree

#print axioms cacheBoth
#print axioms cacheNonH5

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledCacheAgree67


/-! H5 cache agreement across the signer’s private index read. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAgreePrivate67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledCacheAgree67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

def Good {α : Type}
    (result : (JointOutcome α × List Draw) × Audit) : Prop :=
  H5Agree result.1.1.value.state.residual result.2.h5cache

theorem private_some_step {α : Type}
    (state : State) (input : Query)
    (pair : Message × Bytes 32)
    (signedMessages : Finset Message) (audit : Audit)
    (agree : H5Agree state.residual audit.h5cache)
    (next : BitVec 256 → State → Finset Message →
      Program (JointOutcome α))
    (child : ∀ answer updated signed audit',
      H5Agree updated.residual audit'.h5cache →
      ∀ result ∈ support (run (next answer updated signed) audit'),
        Good result) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.privateHashStepOn
        (some pair) state input signedMessages next) audit),
      Good result := by
  intro result member
  cases cached : state.residual input with
  | some answer =>
      simp only [GroupedBalancedIndexLabeledJoint67.privateHashStepOn,
        GroupedBalancedIndexLabeledLift67.cachedDraw,
        cached, run] at member
      exact child answer state (insert pair.1 signedMessages)
        (signStep audit pair)
        (by simpa only [signStep] using agree) result member
  | none =>
      simp only [GroupedBalancedIndexLabeledJoint67.privateHashStepOn,
        GroupedBalancedIndexLabeledLift67.cachedDraw,
        cached, run, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      simp only [support_map, Set.mem_image] at member
      obtain ⟨childResult, childMember, same⟩ := member
      subst result
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
        (by simpa only [signStep] using
          (cacheBoth state.residual audit.h5cache agree input answer))
        childResult childMember

theorem private_none_step {α : Type}
    (state : State) (input : Query)
    (notH5 : SecurityIndexQuery.parse input = none)
    (signedMessages : Finset Message) (audit : Audit)
    (agree : H5Agree state.residual audit.h5cache)
    (next : BitVec 256 → State → Finset Message →
      Program (JointOutcome α))
    (child : ∀ answer updated signed audit',
      H5Agree updated.residual audit'.h5cache →
      ∀ result ∈ support (run (next answer updated signed) audit'),
        Good result) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.privateHashStepOn
        none state input signedMessages next) audit),
      Good result := by
  intro result member
  rw [GroupedBalancedIndexLabeledJoint67.privateHashStepOn,
    GroupedBalancedIndexLabeledAuditLift67.run_unmarked,
    mem_support_bind_iff] at member
  obtain ⟨sample, sampled, childMember⟩ := member
  rcases sample with ⟨answer, residual⟩
  cases cached : state.residual input with
  | some known =>
      simp only [randomOracle.run_eq, cached, support_pure,
        Set.mem_singleton_iff] at sampled
      cases sampled
      exact child answer state signedMessages audit agree result childMember
  | none =>
      simp only [randomOracle.run_eq, cached,
        mem_support_bind_iff] at sampled
      obtain ⟨fresh, _, sampled⟩ := sampled
      simp only [support_pure, Set.mem_singleton_iff] at sampled
      cases sampled
      exact child answer
        { state with residual := state.residual.cacheQuery input answer }
        signedMessages audit
        (cacheNonH5 state.residual audit.h5cache agree input notH5 answer)
        result childMember

#print axioms private_some_step
#print axioms private_none_step

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAgreePrivate67
