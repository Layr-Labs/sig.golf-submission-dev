import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledSignedWitness67

/-! Every message recorded as signed has a retained first signer H5 pair. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPairCoverage67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

def PairCoverage (audit : Audit) : Prop :=
  ∀ message ∈ audit.signedMessages,
    ∃ pair ∈ audit.signedPairs, pair.1 = message

theorem empty : PairCoverage {} := by
  intro message member
  simp at member

theorem publicStep (audit : Audit) (pair : Message × Bytes 32)
    (covered : PairCoverage audit) :
    PairCoverage (GroupedBalancedIndexLabeledAudit67.publicStep audit pair) := by
  by_cases signed : pair.1 ∈ audit.signedMessages <;>
    simpa [PairCoverage, GroupedBalancedIndexLabeledAudit67.publicStep,
      signed] using covered

theorem signStep (audit : Audit) (pair : Message × Bytes 32)
    (covered : PairCoverage audit) :
    PairCoverage (GroupedBalancedIndexLabeledAudit67.signStep audit pair) := by
  intro message member
  by_cases signed : pair.1 ∈ audit.signedMessages
  · have old : message ∈ audit.signedMessages := by
      simpa [GroupedBalancedIndexLabeledAudit67.signStep, signed] using member
    obtain ⟨earlier, pairMember, eq⟩ := covered message old
    exact ⟨earlier, by simpa
      [GroupedBalancedIndexLabeledAudit67.signStep, signed] using pairMember, eq⟩
  · have split : message = pair.1 ∨ message ∈ audit.signedMessages := by
      simpa [GroupedBalancedIndexLabeledAudit67.signStep, signed] using member
    rcases split with same | old
    · exact ⟨pair, by simp
        [GroupedBalancedIndexLabeledAudit67.signStep, signed], same.symm⟩
    · obtain ⟨earlier, pairMember, eq⟩ := covered message old
      exact ⟨earlier, by simp
        [GroupedBalancedIndexLabeledAudit67.signStep, signed, pairMember], eq⟩

theorem run_coverage {α : Type} (program : Program α)
    (audit : Audit) (covered : PairCoverage audit) :
    ∀ result ∈ support (run program audit), PairCoverage result.2 := by
  induction program generalizing audit with
  | pure value =>
      intro result member
      simp only [run, support_pure, Set.mem_singleton_iff] at member
      subst result
      exact covered
  | recordPublic pair next ih =>
      exact ih (GroupedBalancedIndexLabeledAudit67.publicStep audit pair)
        (publicStep audit pair covered)
  | recordSign pair next ih =>
      exact ih (GroupedBalancedIndexLabeledAudit67.signStep audit pair)
        (signStep audit pair covered)
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
      exact ih answer _
        (by simpa only [PairCoverage] using covered)
        child childMember

theorem run_empty_coverage {α : Type} (program : Program α)
    (result : (α × List Draw) × Audit)
    (member : result ∈ support (run program {})) :
    PairCoverage result.2 :=
  run_coverage program {} empty result member

#print axioms run_coverage
#print axioms run_empty_coverage

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPairCoverage67
