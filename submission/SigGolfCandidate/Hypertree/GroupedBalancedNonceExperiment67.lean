import SigGolfCandidate.Hypertree.GroupedBalancedNonceGlobal67
import SigGolfCandidate.Hypertree.GroupedBalancedNonceExecuteValue67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedNonceTableUniform67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedNonceExperiment67. -/
section
/-! The old private slot table factors bijectively into independent chain
sources and message randomizers. Its randomizer projection is uniform. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceTableUniform67
open SigGolf OracleComp OracleSpec Reference SecurityDerivation
open SecurityGraphIdeal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

abbrev ChainTable := ChainAddress → BitVec 256
abbrev NonceTable := Message → BitVec 256
abbrev Factors := NonceTable × ChainTable
noncomputable instance : Fintype ChainAddress := Fintype.ofFinite ChainAddress
noncomputable instance : SampleableType ChainTable :=
  SampleableType.ofFintype ChainTable

def factor (answers : PrivateTable) : Factors :=
  (fun message => answers (.randomizer message),
    fun address => answers (.chain address))

def assemble (factors : Factors) : PrivateTable
  | .chain address => factors.2 address
  | .randomizer message => factors.1 message

def tableEquiv : PrivateTable ≃ Factors where
  toFun := factor
  invFun := assemble
  left_inv := by
    intro answers
    funext slot
    cases slot <;> rfl
  right_inv := by
    intro factors
    apply Prod.ext
    · funext message
      rfl
    · funext address
      rfl

theorem uniform_factors :
    𝒮[factor <$> ($ᵗ PrivateTable)] = 𝒮[$ᵗ Factors] :=
  evalSPMF_map_bijective_uniform_cross PrivateTable factor
    tableEquiv.bijective

theorem nonce_uniform_bind {α : Type}
    (next : NonceTable → ProbComp α) :
    𝒮[do
      let answers ← $ᵗ PrivateTable
      next (fun message => answers (.randomizer message))] =
    𝒮[do let nonces ← $ᵗ NonceTable; next nonces] := by
  have projected :
      𝒮[(fun answers : PrivateTable => (factor answers).1) <$>
        ($ᵗ PrivateTable)] = 𝒮[$ᵗ NonceTable] := by
    calc
      _ = Prod.fst <$> 𝒮[factor <$> ($ᵗ PrivateTable)] := by
        simp only [evalSPMF_map, Functor.map_map, Function.comp_def]
      _ = Prod.fst <$> 𝒮[$ᵗ Factors] := congrArg _ uniform_factors
      _ = _ := by
        simpa only [evalSPMF_map] using
          (evalSPMF_map_fst_uniformSample_prod
            (α := NonceTable) (β := ChainTable))
  calc
    _ = 𝒮[do
      let nonces ← (fun answers : PrivateTable => (factor answers).1) <$>
        ($ᵗ PrivateTable)
      next nonces] := by
        simp only [map_eq_pure_bind, bind_assoc, pure_bind, factor]
    _ = _ := by
      rw [evalSPMF_bind, projected, ← evalSPMF_bind]

#print axioms nonce_uniform_bind

end SigGolfCandidate.Hypertree.GroupedBalancedNonceTableUniform67
end

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceExperimentFirst67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphInteraction67
open GroupedBalancedIndexLabeledAudit67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

private theorem interpreter_projection {β : Type}
    (program : GroupedBalancedNonceProgram67.Program β) :
    𝒮[do
      let nonces ← GroupedBalancedNonceExecuteValue67.nonceSample
      SecurityMonitorNonceLift.observe nonces ∅
        (GroupedBalancedNonceInterpreter67.execute program)] =
    𝒮[do
      let nonces ← GroupedBalancedNonceExecuteValue67.nonceSample
      run (GroupedBalancedNonceProgram67.erase nonces program) {}] := by
  apply evalSPMF_bind_congr
  intro nonces _
  exact congrArg _
    (GroupedBalancedNonceInterpreterObserve67.observe_execute
      nonces ∅ program)

theorem projection {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    𝒮[SecurityNonceProgram.Outcome.value <$>
      SecurityNonceProgram.execute
        (GroupedBalancedNonceInterpreter67.execute
          (GroupedBalancedNonceGlobal67.global interaction budget)) ∅] =
    𝒮[do
      let nonces ← GroupedBalancedNonceExecuteValue67.nonceSample
      run (GroupedBalancedNonceProgram67.erase nonces
        (GroupedBalancedNonceGlobal67.global interaction budget)) {}] := by
  let program := GroupedBalancedNonceInterpreter67.execute
    (GroupedBalancedNonceGlobal67.global interaction budget)
  have first := congrArg
    (fun distribution : ProbComp _ => 𝒮[distribution])
    (GroupedBalancedNonceExecuteValue67.execute_value_projection program)
  apply Eq.trans first
  exact interpreter_projection
    (GroupedBalancedNonceGlobal67.global interaction budget)

#print axioms projection

end SigGolfCandidate.Hypertree.GroupedBalancedNonceExperimentFirst67


/-! The passive nonce program and the exact stopped paired/audited direct67
simulation have the same ordinary output distribution. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceExperiment67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphInteraction67
open GroupedBalancedIndexLabeledAudit67
open SecurityGraphIdeal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem same_nonce_samples :
    𝒮[GroupedBalancedNonceExecuteValue67.nonceSample] =
    𝒮[$ᵗ GroupedBalancedNonceTableUniform67.NonceTable] := by
  apply evalSPMF_ext
  intro nonces
  simp only [GroupedBalancedNonceExecuteValue67.nonceSample,
    probOutput_uniformSample]

noncomputable def nonceExperiment {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) : ProbComp
      (SecurityNonceProgram.Outcome
        ((GroupedBalancedGraphIndexJoint67.JointOutcome
          ((Option α × List GroupedBalancedGameQueryTrace67.Action) × Nat) ×
          List GroupedBalancedIndexLabeledProgram67.Draw) × Audit)) :=
  SecurityNonceProgram.execute
    (GroupedBalancedNonceInterpreter67.execute
      (GroupedBalancedNonceGlobal67.global interaction budget)) ∅

theorem sampled_projection {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    𝒮[SecurityNonceProgram.Outcome.value <$>
      nonceExperiment interaction budget] =
    𝒮[Prod.snd <$>
      GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
        interaction budget] := by
  calc
    _ = 𝒮[do
      let nonces ← GroupedBalancedNonceExecuteValue67.nonceSample
      run (GroupedBalancedNonceProgram67.erase nonces
        (GroupedBalancedNonceGlobal67.global interaction budget)) {}] :=
          GroupedBalancedNonceExperimentFirst67.projection
            interaction budget
    _ = 𝒮[do
      let nonces ← $ᵗ GroupedBalancedNonceTableUniform67.NonceTable
      run (GroupedBalancedNonceProgram67.erase nonces
        (GroupedBalancedNonceGlobal67.global interaction budget)) {}] := by
          rw [evalSPMF_bind, same_nonce_samples, ← evalSPMF_bind]
    _ = 𝒮[do
      let answers ← $ᵗ PrivateTable
      run (GroupedBalancedNonceProgram67.erase
        (fun message => answers (.randomizer message))
        (GroupedBalancedNonceGlobal67.global interaction budget)) {}] :=
          (GroupedBalancedNonceTableUniform67.nonce_uniform_bind
            (fun nonces => run (GroupedBalancedNonceProgram67.erase nonces
              (GroupedBalancedNonceGlobal67.global interaction budget)) {})).symm
    _ = _ := by
      rw [GroupedBalancedIndexLabeledPairedGlobal67.paired_projection]
      unfold GroupedBalancedIndexLabeledAudit67.auditedAnnotatedGlobal
      apply evalSPMF_bind_congr
      intro answers _
      simp only [GroupedBalancedNonceGlobal67.erase_global,
        map_pure, bind_pure]

#print axioms sampled_projection

end SigGolfCandidate.Hypertree.GroupedBalancedNonceExperiment67
