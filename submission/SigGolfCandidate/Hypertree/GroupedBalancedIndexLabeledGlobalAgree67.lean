import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledCompilerAgree67

/-! The sampled labelled experiment keeps its actual and ghost H5 caches in
agreement. Every actual cached H5 answer therefore has a labelled draw. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledGlobalAgree67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledCacheAgree67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option linter.constructorNameAsVariable false
open scoped Classical

theorem global_h5_agree {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledGlobal67.global view remaining) {}),
      H5Agree result.1.1.value.state.residual result.2.h5cache := by
  intro result member
  rw [GroupedBalancedIndexLabeledGlobal67.global,
    GroupedBalancedIndexLabeledAuditLift67.run_unmarked,
    mem_support_bind_iff] at member
  obtain ⟨table, _, child⟩ := member
  exact GroupedBalancedIndexLabeledCompilerAgree67.start_h5_agree
    table view remaining result child

theorem global_cache_provenance {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat)
    (result : (GroupedBalancedGraphIndexJoint67.JointOutcome α ×
      List GroupedBalancedIndexLabeledProgram67.Draw) × Audit)
    (member : result ∈ support (run
      (GroupedBalancedIndexLabeledGlobal67.global view remaining) {})) :
    ∀ message nonce answer,
      result.1.1.value.state.residual
        (SecurityRandomOracle.indexInput message nonce) = some answer →
      ∃ mark,
        (SecurityRandomOracle.indexInput message nonce,
          (mark, answer.extractLsb' 0 160)) ∈ result.1.2 := by
  intro message nonce answer cached
  have agree := global_h5_agree view remaining result member
  have ghost : result.2.h5cache
      (SecurityRandomOracle.indexInput message nonce) = some answer := by
    rw [← agree message nonce]
    exact cached
  exact GroupedBalancedIndexLabeledCoverage67.run_empty_cache_covered
    (GroupedBalancedIndexLabeledGlobal67.global view remaining)
    result member _ _ ghost

theorem audited_h5_agree {α : Type}
    (interaction : QueryCache PointSpec →
      GroupedBalancedGraphInteraction67.Interaction α)
    (budget : Nat) :
    ∀ result ∈ support
      (GroupedBalancedIndexLabeledAudit67.auditedAnnotatedGlobal
        interaction budget),
      H5Agree result.1.1.value.state.residual
        result.2.h5cache := by
  intro result member
  unfold GroupedBalancedIndexLabeledAudit67.auditedAnnotatedGlobal at member
  simp only [mem_support_bind_iff] at member
  obtain ⟨answers, _, child⟩ := member
  exact global_h5_agree _ budget result child

#print axioms global_h5_agree
#print axioms global_cache_provenance
#print axioms audited_h5_agree

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledGlobalAgree67
