import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCost67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPairedGlobal67
import SigGolfCandidate.Hypertree.GroupedBalancedNonceSafeCorrect67
import SigGolfCandidate.Hypertree.GroupedBalancedNonceExecuteValue67
import SigGolfCandidate.Hypertree.GroupedBalancedNonceGlobalSafe67
import SigGolfCandidate.Hypertree.GroupedBalancedNonceExperiment67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledHistory67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedNonceAnnotatedProjection67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedNonceRisk67. -/
section
/-! Exact flag and count law for a safe passive nonce program, first with a
fixed randomizer table and then under the eager uniform sample. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceSafeExecute67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedNonceProgram67
open GroupedBalancedNonceInterpreter67
open GroupedBalancedNonceSafeProgram67
open GroupedBalancedNonceTrack67
open GroupedBalancedNonceSafeCorrect67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

@[simp] theorem accumulate_empty {α : Type}
    (nonces : SecurityGraphFactor.NonceTable)
    (result : SecurityNonceProgram.Outcome α) :
    accumulate nonces {} result = result := by
  cases result
  simp [accumulate, hits]

theorem run_safe_empty {α : Type}
    (program : Program α) (safe : Safe program)
    (nonces : SecurityGraphFactor.NonceTable) :
    SecurityNonceProgram.run nonces ∅
      (GroupedBalancedNonceInterpreter67.execute program) =
    annotate nonces <$> GroupedBalancedIndexLabeledAudit67.run
      (erase nonces program) {} := by
  have identity : accumulate (α := ((α × List
      GroupedBalancedIndexLabeledProgram67.Draw) × Audit)) nonces {} = id := by
    funext result
    exact accumulate_empty nonces result
  simpa only [GroupedBalancedNonceInterpreter67.execute,
    identity, id_map] using
    (correctSafe safe nonces ∅ {} tracks_empty)

theorem execute_safe {α : Type}
    (program : Program α) (safe : Safe program) :
    SecurityNonceProgram.execute
      (GroupedBalancedNonceInterpreter67.execute program) ∅ =
    (do
      let nonces ← GroupedBalancedNonceExecuteValue67.nonceSample
      annotate nonces <$> GroupedBalancedIndexLabeledAudit67.run
        (erase nonces program) {}) := by
  change (do
    let nonces ← GroupedBalancedNonceExecuteValue67.nonceSample
    SecurityNonceProgram.run
      (SecurityNonceMonitor.complete ∅ nonces) ∅
      (GroupedBalancedNonceInterpreter67.execute program)) = _
  apply bind_congr
  intro nonces
  have empty : SecurityNonceMonitor.complete ∅ nonces = nonces := rfl
  rw [empty]
  exact run_safe_empty program safe nonces

#print axioms run_safe_empty
#print axioms execute_safe

end SigGolfCandidate.Hypertree.GroupedBalancedNonceSafeExecute67


/-! Joint output/flag/count distribution of the passive nonce experiment is
the actual stopped paired H5 audit annotated with its prereveal nonce hits. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceAnnotatedProjection67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphPassive67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedNonceTrack67
open SecurityGraphIdeal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem annotated_projection {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    𝒮[GroupedBalancedNonceExperiment67.nonceExperiment interaction budget] =
    𝒮[(fun result =>
      annotate (fun message => result.1 (.randomizer message)) result.2) <$>
      GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
        interaction budget] := by
  let program := GroupedBalancedNonceGlobal67.global interaction budget
  calc
    _ = 𝒮[do
      let nonces ← GroupedBalancedNonceExecuteValue67.nonceSample
      annotate nonces <$> GroupedBalancedIndexLabeledAudit67.run
        (GroupedBalancedNonceProgram67.erase nonces program) {}] := by
          exact congrArg (fun distribution => 𝒮[distribution])
            (GroupedBalancedNonceSafeExecute67.execute_safe program
              (GroupedBalancedNonceGlobalSafe67.safe_global interaction budget))
    _ = 𝒮[do
      let nonces ← $ᵗ GroupedBalancedNonceTableUniform67.NonceTable
      annotate nonces <$> GroupedBalancedIndexLabeledAudit67.run
        (GroupedBalancedNonceProgram67.erase nonces program) {}] := by
          rw [evalSPMF_bind,
            GroupedBalancedNonceExperiment67.same_nonce_samples,
            ← evalSPMF_bind]
    _ = 𝒮[do
      let answers ← $ᵗ PrivateTable
      annotate (fun message => answers (.randomizer message)) <$>
        GroupedBalancedIndexLabeledAudit67.run
          (GroupedBalancedNonceProgram67.erase
            (fun message => answers (.randomizer message)) program) {}] :=
          (GroupedBalancedNonceTableUniform67.nonce_uniform_bind
            (fun nonces => annotate nonces <$>
              GroupedBalancedIndexLabeledAudit67.run
                (GroupedBalancedNonceProgram67.erase nonces program) {})).symm
    _ = _ := by
      unfold GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
      simp only [evalSPMF_map, map_bind]
      apply evalSPMF_bind_congr
      intro answers _
      simp only [program, GroupedBalancedNonceGlobal67.erase_global,
        Functor.map_map, Function.comp_def, map_pure, bind_pure,
        map_eq_pure_bind, bind_assoc, pure_bind]

#print axioms annotated_projection

end SigGolfCandidate.Hypertree.GroupedBalancedNonceAnnotatedProjection67
end

/-! The stopped direct67 audit's prereveal nonce-guess count is paid by its
actual H5 draw trace, including the independently sampled point table. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCostGlobal67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledNonceCost67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem global_affordable {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    ∀ result ∈ support
      (run (GroupedBalancedIndexLabeledGlobal67.global view remaining) {}),
      result.2.nonceGuesses.length ≤ result.1.2.length := by
  intro result member
  rw [GroupedBalancedIndexLabeledGlobal67.global,
    GroupedBalancedIndexLabeledAuditLift67.run_unmarked,
    mem_support_bind_iff] at member
  obtain ⟨table, _, child⟩ := member
  exact start_affordable table view remaining result child

theorem paired_affordable {α : Type}
    (interaction : QueryCache PointSpec →
      GroupedBalancedGraphInteraction67.Interaction α)
    (budget : Nat) :
    ∀ result ∈ support
      (GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
        interaction budget),
      result.2.2.nonceGuesses.length ≤ result.2.1.2.length := by
  intro result member
  unfold GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal at member
  simp only [mem_support_bind_iff] at member
  obtain ⟨answers, _, member⟩ := member
  obtain ⟨auditResult, auditMember, same⟩ := member
  simp only [support_pure, Set.mem_singleton_iff] at same
  subst result
  exact global_affordable _ budget auditResult auditMember

#print axioms global_affordable
#print axioms paired_affordable

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCostGlobal67


/-! The nonce hit probability for the actual stopped paired audit is charged
to its expected number of prereveal H5 guesses. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceRisk67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphPassive67
open GroupedBalancedNonceTrack67
open SecurityGraphIdeal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem paired_nonce_bad_le_expected {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    Pr[fun result =>
      hits (fun message => result.1 (.randomizer message)) result.2.2 = true |
      GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
        interaction budget] ≤
    expectedValue
      (GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
        interaction budget)
      (fun result => (result.2.2.nonceGuesses.length : ENNReal)) /
        (2 : ENNReal)^256 := by
  have bound := SecurityNonceProgram.prob_bad_le_expected
    (GroupedBalancedNonceInterpreter67.execute
      (GroupedBalancedNonceGlobal67.global interaction budget)) ∅
  change
    Pr[fun result => result.bad = true |
      GroupedBalancedNonceExperiment67.nonceExperiment interaction budget] ≤
    expectedValue
      (GroupedBalancedNonceExperiment67.nonceExperiment interaction budget)
      (fun result => (result.guesses : ENNReal)) /
        (2 : ENNReal)^256 at bound
  have dist := GroupedBalancedNonceAnnotatedProjection67.annotated_projection
    interaction budget
  have eventEq :
      Pr[fun result => result.bad = true |
        GroupedBalancedNonceExperiment67.nonceExperiment interaction budget] =
      Pr[fun result => result.bad = true |
        (fun result => annotate
          (fun message => result.1 (.randomizer message)) result.2) <$>
          GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
            interaction budget] := by
    rw [probEvent_def, probEvent_def, dist]
  have expectationEq :
      expectedValue
        (GroupedBalancedNonceExperiment67.nonceExperiment interaction budget)
        (fun result => (result.guesses : ENNReal)) =
      expectedValue
        ((fun result => annotate
          (fun message => result.1 (.randomizer message)) result.2) <$>
          GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
            interaction budget)
        (fun result => (result.guesses : ENNReal)) := by
    apply expectedValue_congr
    intro result
    rw [probOutput_def, probOutput_def, dist]
  rw [eventEq, expectationEq, probEvent_map, expectedValue_map] at bound
  simpa only [Function.comp_def, GroupedBalancedNonceTrack67.annotate]
    using bound

theorem hits_true_iff (nonces : SecurityGraphFactor.NonceTable)
    (audit : GroupedBalancedIndexLabeledAudit67.Audit) :
    hits nonces audit = true ↔
      ∃ pair ∈ audit.nonceGuesses, nonces pair.1 = pair.2 := by
  simp only [hits, List.any_eq_true, decide_eq_true_eq]

theorem paired_nonce_hit_le_draws {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    Pr[fun result =>
      SecurityMonitorIndexContact.NonceHit
        (fun message => result.1 (.randomizer message))
        (GroupedBalancedIndexLabeledHistory67.history
          result.2.2 result.2.1.2) |
      GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
        interaction budget] ≤
    expectedValue
      (GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
        interaction budget)
      (fun result => (result.2.1.2.length : ENNReal)) /
        (2 : ENNReal)^256 := by
  let simulation :=
    GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
      interaction budget
  let PairedResult : Type := SecurityGraphIdeal.PrivateTable ×
    ((GroupedBalancedGraphIndexJoint67.JointOutcome
      ((Option α × List GroupedBalancedGameQueryTrace67.Action) × Nat) ×
      List GroupedBalancedIndexLabeledProgram67.Draw) ×
      GroupedBalancedIndexLabeledAudit67.Audit)
  have eventEq :
      (fun result : PairedResult =>
        SecurityMonitorIndexContact.NonceHit
          (fun message => result.1 (.randomizer message))
          (GroupedBalancedIndexLabeledHistory67.history
            result.2.2 result.2.1.2)) =
      (fun result =>
        hits (fun message => result.1 (.randomizer message))
          result.2.2 = true) := by
    funext result
    apply propext
    exact (GroupedBalancedIndexLabeledHistory67.nonceHit_iff
      (fun message => result.1 (.randomizer message))
      result.2.2 result.2.1.2).trans
      (hits_true_iff
        (fun message => result.1 (.randomizer message))
        result.2.2).symm
  rw [eventEq]
  calc
    _ ≤ expectedValue simulation
        (fun result => (result.2.2.nonceGuesses.length : ENNReal)) /
          (2 : ENNReal)^256 :=
        paired_nonce_bad_le_expected interaction budget
    _ ≤ expectedValue simulation
        (fun result => (result.2.1.2.length : ENNReal)) /
          (2 : ENNReal)^256 := by
        apply ENNReal.div_le_div_right
          (expectedValue_mono_of_support (fun result member => by
            exact_mod_cast
              GroupedBalancedIndexLabeledNonceCostGlobal67.paired_affordable
                interaction budget result member))

#print axioms paired_nonce_bad_le_expected
#print axioms paired_nonce_hit_le_draws

end SigGolfCandidate.Hypertree.GroupedBalancedNonceRisk67
