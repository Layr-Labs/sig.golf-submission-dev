import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledSignedCompiler67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPairedGlobal67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledGlobalAgree67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPairCoverage67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledHistory67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledSignedGlobal67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPairedProvenance67. -/
section
/-! First-signer evidence holds after sampling graph and private tables. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledSignedGlobal67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledSignedWitness67
open GroupedBalancedIndexLabeledDrawFaithful67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option linter.constructorNameAsVariable false
open scoped Classical

theorem global_signed_witness {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledGlobal67.global view remaining) {}),
      SignedWitness result.2 := by
  intro result member
  rw [GroupedBalancedIndexLabeledGlobal67.global,
    GroupedBalancedIndexLabeledAuditLift67.run_unmarked,
    mem_support_bind_iff] at member
  obtain ⟨table, _, child⟩ := member
  exact GroupedBalancedIndexLabeledSignedCompiler67.start_signed_witness
    table view remaining result child

theorem global_draw_faithful {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledGlobal67.global view remaining) {}),
      DrawFaithful result.2 := by
  intro result member
  rw [GroupedBalancedIndexLabeledGlobal67.global,
    GroupedBalancedIndexLabeledAuditLift67.run_unmarked,
    mem_support_bind_iff] at member
  obtain ⟨table, _, child⟩ := member
  exact GroupedBalancedIndexLabeledSignedCompiler67.start_draw_faithful
    table view remaining result child

theorem audited_signed_witness {α : Type}
    (interaction : QueryCache PointSpec →
      GroupedBalancedGraphInteraction67.Interaction α)
    (budget : Nat) :
    ∀ result ∈ support
      (GroupedBalancedIndexLabeledAudit67.auditedAnnotatedGlobal
        interaction budget),
      SignedWitness result.2 := by
  intro result member
  unfold GroupedBalancedIndexLabeledAudit67.auditedAnnotatedGlobal at member
  simp only [mem_support_bind_iff] at member
  obtain ⟨answers, _, child⟩ := member
  exact global_signed_witness _ budget result child

theorem paired_signed_witness {α : Type}
    (interaction : QueryCache PointSpec →
      GroupedBalancedGraphInteraction67.Interaction α)
    (budget : Nat) :
    ∀ result ∈ support
      (GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
        interaction budget),
      SignedWitness result.2.2 := by
  intro result member
  unfold GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal at member
  simp only [mem_support_bind_iff] at member
  obtain ⟨answers, _, child⟩ := member
  obtain ⟨auditResult, auditMember, same⟩ := child
  simp only [support_pure, Set.mem_singleton_iff] at same
  subst result
  exact global_signed_witness _ budget auditResult auditMember

theorem paired_draw_faithful {α : Type}
    (interaction : QueryCache PointSpec →
      GroupedBalancedGraphInteraction67.Interaction α)
    (budget : Nat) :
    ∀ result ∈ support
      (GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
        interaction budget),
      DrawFaithful result.2.2 := by
  intro result member
  unfold GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal at member
  simp only [mem_support_bind_iff] at member
  obtain ⟨answers, _, child⟩ := member
  obtain ⟨auditResult, auditMember, same⟩ := child
  simp only [support_pure, Set.mem_singleton_iff] at same
  subst result
  exact global_draw_faithful _ budget auditResult auditMember

#print axioms global_signed_witness
#print axioms audited_signed_witness
#print axioms paired_signed_witness
#print axioms paired_draw_faithful

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledSignedGlobal67

end

/-! Exact input-labelled H5 provenance for the stopped paired direct67 game. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPairedProvenance67
open SigGolf OracleComp OracleSpec Reference SecurityRandomOracle
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledHistory67
open GroupedBalancedIndexLabeledPairConsistent67
open GroupedBalancedIndexLabeledPairCoverage67
open GroupedBalancedIndexLabeledSignedWitness67
open GroupedBalancedIndexLabeledDrawFaithful67
open GroupedBalancedIndexLabeledCacheAgree67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false
open scoped Classical

theorem provenance_of_facts {α : Type}
    (nonces : Message → Bytes 32)
    (result : (GroupedBalancedGraphIndexJoint67.JointOutcome α ×
      List Draw) × Audit)
    (consistent : Consistent nonces result.2)
    (pairs : PairCoverage result.2)
    (witness : SignedWitness result.2)
    (faithful : DrawFaithful result.2)
    (agree : H5Agree result.1.1.value.state.residual
      result.2.h5cache)
    (drawsEq : result.2.draws = result.1.2)
    (cached : ∀ message nonce answer,
      result.1.1.value.state.residual
        (indexInput message nonce) = some answer →
      ∃ mark, (indexInput message nonce,
        (mark, answer.extractLsb' 0 160)) ∈ result.1.2) :
    SecurityMonitorIndexContact.Provenance nonces
      result.1.1.value.state.residual
      (history result.2 result.1.2) result.1.2 := by
  apply provenance_of_audit nonces
    result.1.1.value.state.residual result.2 result.1.2 cached
  intro message signed
  obtain ⟨pair, pairMember, messageEq⟩ := pairs message signed
  have nonceEq := consistent pair pairMember
  have pairEq : pair = (message, nonces message) := by
    cases pair with
    | mk signer nonce =>
        simp only at messageEq nonceEq
        cases messageEq
        cases nonceEq
        rfl
  subst pair
  rcases witness (message, nonces message) pairMember with guess | ⟨index, marked⟩
  · left
    refine ⟨message, ?_⟩
    change (message, nonces message) ∈ result.2.nonceGuesses
    exact guess
  · right
    obtain ⟨answer, ghostCached, indexEq⟩ :=
      faithful (indexInput message (nonces message)) true index marked
    have actualCached : result.1.1.value.state.residual
        (indexInput message (nonces message)) = some answer := by
      rw [agree message (nonces message)]
      exact ghostCached
    refine ⟨answer, ?_, ?_⟩
    · exact actualCached
    · rw [drawsEq] at marked
      rw [indexEq] at marked
      exact marked

theorem paired_provenance {α : Type}
    (interaction : QueryCache PointSpec →
      GroupedBalancedGraphInteraction67.Interaction α)
    (budget : Nat) :
    ∀ result ∈ support
      (GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
        interaction budget),
      SecurityMonitorIndexContact.Provenance
        (fun message => result.1 (.randomizer message))
        result.2.1.1.value.state.residual
        (history result.2.2 result.2.1.2) result.2.1.2 := by
  intro result member
  have consistent :=
    GroupedBalancedIndexLabeledPairedGlobal67.paired_consistent
      interaction budget result member
  unfold GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal at member
  simp only [mem_support_bind_iff] at member
  obtain ⟨answers, _, child⟩ := member
  obtain ⟨auditResult, auditMember, same⟩ := child
  simp only [support_pure, Set.mem_singleton_iff] at same
  subst result
  have pairs : PairCoverage auditResult.2 :=
    GroupedBalancedIndexLabeledPairCoverage67.run_empty_coverage
      _ auditResult auditMember
  have witness : SignedWitness auditResult.2 :=
    GroupedBalancedIndexLabeledSignedGlobal67.global_signed_witness
      _ budget auditResult auditMember
  have faithful : DrawFaithful auditResult.2 :=
    GroupedBalancedIndexLabeledSignedGlobal67.global_draw_faithful
      _ budget auditResult auditMember
  have agree : H5Agree auditResult.1.1.value.state.residual
      auditResult.2.h5cache :=
    GroupedBalancedIndexLabeledGlobalAgree67.global_h5_agree
      _ budget auditResult auditMember
  have drawsEq : auditResult.2.draws = auditResult.1.2 := by
    have sameDraws :=
      GroupedBalancedIndexLabeledCoverage67.run_draws_append
        _ {} auditResult auditMember
    simpa using sameDraws
  have cached :=
    GroupedBalancedIndexLabeledGlobalAgree67.global_cache_provenance
      _ budget auditResult auditMember
  exact provenance_of_facts
    (fun message => answers (.randomizer message)) auditResult
    consistent pairs witness faithful agree drawsEq cached

#print axioms provenance_of_facts
#print axioms paired_provenance

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPairedProvenance67
