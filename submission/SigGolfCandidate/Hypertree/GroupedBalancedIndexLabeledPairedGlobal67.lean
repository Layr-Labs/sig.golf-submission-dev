import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPairConsistent67

/-! Retain the sampled private table alongside the audited stopped execution,
so signed H5 pairs can be tied to the actual deterministic nonce function. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPairedGlobal67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphInteraction67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledPairConsistent67
open SecurityGraphIdeal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option linter.constructorNameAsVariable false
open scoped Classical

noncomputable def pairedAuditedGlobal {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) : ProbComp
      (PrivateTable ×
        ((GroupedBalancedGraphIndexJoint67.JointOutcome
          ((Option α × List GroupedBalancedGameQueryTrace67.Action) × Nat) ×
          List GroupedBalancedIndexLabeledProgram67.Draw) × Audit)) := do
  let answers ← $ᵗ PrivateTable
  let result ← run (GroupedBalancedIndexLabeledGlobal67.global
    (fun cache =>
      GroupedBalancedGraphIndexJointClassTrace67.annotate
        (GroupedBalancedPlantedEagerGraphProjection67.viewOf
          answers interaction budget cache) 0) budget) {}
  pure (answers, result)

theorem paired_projection {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    Prod.snd <$> pairedAuditedGlobal interaction budget =
      GroupedBalancedIndexLabeledAudit67.auditedAnnotatedGlobal
        interaction budget := by
  unfold pairedAuditedGlobal
    GroupedBalancedIndexLabeledAudit67.auditedAnnotatedGlobal
  rw [map_bind]
  apply bind_congr
  intro answers
  simp only [map_bind, map_pure, bind_pure]

theorem paired_consistent {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    ∀ result ∈ support (pairedAuditedGlobal interaction budget),
      Consistent (fun message => result.1 (.randomizer message)) result.2.2 := by
  intro result member
  unfold pairedAuditedGlobal at member
  simp only [mem_support_bind_iff] at member
  obtain ⟨answers, _, member⟩ := member
  obtain ⟨tableResult, tableMember, same⟩ := member
  simp only [support_pure, Set.mem_singleton_iff] at same
  subst result
  rw [GroupedBalancedIndexLabeledGlobal67.global,
    GroupedBalancedIndexLabeledAuditLift67.run_unmarked,
    mem_support_bind_iff] at tableMember
  obtain ⟨table, _, child⟩ := tableMember
  apply GroupedBalancedIndexLabeledPairConsistent67.start_consistent
    table (fun message => answers (.randomizer message))
    (fun cache =>
      GroupedBalancedGraphIndexJointClassTrace67.annotate
        (GroupedBalancedPlantedEagerGraphProjection67.viewOf
          answers interaction budget cache) 0) budget
  · exact GroupedBalancedIndexFixedNonce67.annotate
      (fun message => answers (.randomizer message)) _ 0
      (GroupedBalancedIndexFixedNonce67.eagerCutoffView_fixed
        answers (GroupedBalancedGraphMonitorSetup67.cache table)
        (interaction (GroupedBalancedGraphMonitorSetup67.cache table)) budget)
  · exact child

#print axioms paired_projection
#print axioms paired_consistent

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPairedGlobal67
