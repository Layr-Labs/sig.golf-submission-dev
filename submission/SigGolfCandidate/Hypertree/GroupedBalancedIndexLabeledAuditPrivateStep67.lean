import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledMapView67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAuditMonotone67

/-! Invert a parsed private H5 step and expose the audit at its continuation. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAuditPrivateStep67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledJoint67
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem private_step {α : Type}
    (state : State) (input : Query) (pair : Message × Bytes 32)
    (signedMessages : Finset Message)
    (next : BitVec 256 → State → Finset Message → Program α)
    (audit : Audit) (result : (α × List Draw) × Audit)
    (member : result ∈ support (run
      (privateHashStepOn (some pair) state input signedMessages next) audit)) :
    ∃ answer residual nextAudit child,
      child ∈ support (run
        (next answer { state with residual := residual }
          (insert pair.1 signedMessages)) nextAudit) ∧
      nextAudit.signedMessages = insert pair.1 audit.signedMessages ∧
      child.1.1 = result.1.1 ∧
      child.2 = result.2 ∧
      pair.1 ∈ nextAudit.signedMessages := by
  cases cached : state.residual input with
  | some answer =>
      let nextAudit := signStep audit pair
      refine ⟨answer, state.residual, nextAudit, result,
        ?_, ?_, rfl, rfl, ?_⟩
      · simpa only [privateHashStepOn,
          GroupedBalancedIndexLabeledLift67.cachedDraw, cached, run,
          nextAudit] using member
      · rfl
      · simp [nextAudit, signStep]
  | none =>
      simp only [privateHashStepOn,
        GroupedBalancedIndexLabeledLift67.cachedDraw, cached,
        run, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      simp only [support_map, Set.mem_image] at member
      obtain ⟨child, childMember, same⟩ := member
      let drawn : Audit :=
        { audit with
          h5cache := audit.h5cache.cacheQuery input answer
          draws := audit.draws ++
            [(input, (decide (pair.1 ∉ signedMessages),
              answer.extractLsb' 0 160))] }
      let nextAudit := signStep drawn pair
      refine ⟨answer, state.residual.cacheQuery input answer,
        nextAudit, child, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [drawn, nextAudit] using childMember
      · rfl
      · simpa only [] using
          (congrArg (fun x : (α × List Draw) × Audit => x.1.1) same)
      · simpa only [] using
          (congrArg (fun x : (α × List Draw) × Audit => x.2) same)
      · simp [nextAudit, signStep]

#print axioms private_step

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAuditPrivateStep67
