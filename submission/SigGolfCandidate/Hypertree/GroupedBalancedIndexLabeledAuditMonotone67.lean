import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAudit67

/-! Signed messages remain in the passive audit throughout every continuation. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAuditMonotone67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open scoped Classical

theorem run_signed_subset {α : Type} (program : Program α)
    (audit : Audit) (result : (α × List Draw) × Audit)
    (member : result ∈ support (run program audit)) :
    audit.signedMessages ⊆ result.2.signedMessages := by
  induction program generalizing audit result with
  | pure value =>
      simp only [run, support_pure, Set.mem_singleton_iff] at member
      subst result
      exact Finset.Subset.rfl
  | coin n next ih =>
      simp only [run, mem_support_bind_iff] at member
      obtain ⟨answer, _, child⟩ := member
      exact ih answer audit result child
  | recordPublic pair next ih =>
      change result ∈ support (run next (publicStep audit pair)) at member
      have step : audit.signedMessages ⊆
          (publicStep audit pair).signedMessages := by
        simp only [publicStep]
        split <;> exact Finset.Subset.rfl
      exact step.trans (ih (publicStep audit pair) result member)
  | recordSign pair next ih =>
      change result ∈ support (run next (signStep audit pair)) at member
      have step : audit.signedMessages ⊆
          (signStep audit pair).signedMessages := by
        simpa only [signStep] using
          (Finset.subset_insert pair.1 audit.signedMessages)
      exact step.trans (ih (signStep audit pair) result member)
  | draw input mark next ih =>
      simp only [run, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      simp only [support_map, Set.mem_image] at member
      obtain ⟨child, childMember, same⟩ := member
      have step : audit.signedMessages ⊆
          ({ audit with
            h5cache := audit.h5cache.cacheQuery input answer
            draws := audit.draws ++
              [(input, (mark, answer.extractLsb' 0 160))] } : Audit).signedMessages :=
        Finset.Subset.rfl
      have childSubset := ih answer
        { audit with
          h5cache := audit.h5cache.cacheQuery input answer
          draws := audit.draws ++
            [(input, (mark, answer.extractLsb' 0 160))] }
        child childMember
      have auditEq := congrArg (fun x : (α × List Draw) × Audit => x.2) same
      rw [← auditEq]
      exact step.trans childSubset

theorem run_signed_mem {α : Type} (program : Program α)
    (audit : Audit) (result : (α × List Draw) × Audit)
    (message : Message) (present : message ∈ audit.signedMessages)
    (member : result ∈ support (run program audit)) :
    message ∈ result.2.signedMessages :=
  run_signed_subset program audit result member present

#print axioms run_signed_subset

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAuditMonotone67
