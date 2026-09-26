import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledJoint67
import SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerGraphProjection67
import SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerAnnotated67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledGlobal67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAudit67. -/
section
/-! Sampled input-labelled H5 traces project exactly to the common direct67
graph/H5 monitor, including its returned attacker value and counters. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledGlobal67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedGraphInteraction67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

noncomputable def global {α : Type} (view : QueryCache PointSpec → View α)
    (remaining : Nat) : Program (JointOutcome α) :=
  GroupedBalancedIndexLabeledLift67.unmarked ($ᵗ PointTable)
    (fun table => GroupedBalancedIndexLabeledJoint67.start table view remaining)

theorem erase_global {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    erase (global view remaining) =
      GroupedBalancedGraphIndexJointGlobal67.global view remaining := by
  rw [global, GroupedBalancedIndexLabeledLift67.erase_unmarked]
  change _ = GroupedBalancedGraphIndexLift67.unmarked ($ᵗ PointTable)
    (fun table => GroupedBalancedGraphIndexJoint67.start table view remaining)
  congr 1
  funext table
  exact GroupedBalancedIndexLabeledJoint67.erase_start table view remaining

theorem global_projection {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    (fun result => (result.1, result.2.map Prod.snd)) <$>
      execute (global view remaining) =
        SecurityIndexProgram.execute
          (GroupedBalancedGraphIndexJointGlobal67.global view remaining) := by
  rw [execute_erasure, erase_global]

noncomputable def labeledJointGlobal {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) : ProbComp
      (JointOutcome (Option α ×
        List GroupedBalancedGameQueryTrace67.Action) ×
        List Draw) := do
  let answers ← $ᵗ SecurityGraphIdeal.PrivateTable
  execute (global
    (GroupedBalancedPlantedEagerGraphProjection67.viewOf
      answers interaction budget) budget)

theorem labeled_joint_projection {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    (fun result => (result.1, result.2.map Prod.snd)) <$>
      labeledJointGlobal interaction budget =
        GroupedBalancedPlantedEagerGraphProjection67.jointGlobal
          interaction budget := by
  unfold labeledJointGlobal
    GroupedBalancedPlantedEagerGraphProjection67.jointGlobal
  rw [map_bind]
  exact bind_congr fun answers => global_projection _ _

noncomputable def labeledAnnotatedJointGlobal {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) : ProbComp
      (JointOutcome ((Option α ×
        List GroupedBalancedGameQueryTrace67.Action) × Nat) ×
        List Draw) := do
  let answers ← $ᵗ SecurityGraphIdeal.PrivateTable
  execute (global
    (fun cache =>
      GroupedBalancedGraphIndexJointClassTrace67.annotate
        (GroupedBalancedPlantedEagerGraphProjection67.viewOf
          answers interaction budget cache) 0) budget)

theorem labeled_annotated_projection {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    (fun result => (result.1, result.2.map Prod.snd)) <$>
      labeledAnnotatedJointGlobal interaction budget =
        GroupedBalancedPlantedEagerAnnotated67.annotatedJointGlobal
          interaction budget := by
  unfold labeledAnnotatedJointGlobal
    GroupedBalancedPlantedEagerAnnotated67.annotatedJointGlobal
  rw [map_bind]
  exact bind_congr fun answers => global_projection _ _

#print axioms erase_global
#print axioms global_projection
#print axioms labeled_joint_projection
#print axioms labeled_annotated_projection

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledGlobal67

end

/-! Passive H5 provenance: retain every fresh input-labelled draw, every
public H5 pair queried before its message was signed, and signed-message set.
The annotation is invisible to the direct67 joint monitor. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAudit67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphIndexJoint67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

structure Audit where
  signedMessages : Finset Message := ∅
  signedPairs : List (Message × Bytes 32) := []
  nonceGuesses : List (Message × Bytes 32) := []
  h5cache : QueryCache HashSpec := ∅
  draws : List Draw := []

def publicStep (audit : Audit) (pair : Message × Bytes 32) : Audit :=
  if pair.1 ∈ audit.signedMessages then audit
  else { audit with nonceGuesses := pair :: audit.nonceGuesses }

def signStep (audit : Audit) (pair : Message × Bytes 32) : Audit :=
  { audit with
    signedMessages := insert pair.1 audit.signedMessages
    signedPairs := if pair.1 ∈ audit.signedMessages
      then audit.signedPairs else pair :: audit.signedPairs }

noncomputable def run {α : Type} :
    Program α → Audit → ProbComp ((α × List Draw) × Audit)
  | .pure value, audit => pure ((value, []), audit)
  | .draw input mark next, audit => do
      let answer ← $ᵗ BitVec 256
      let entry : Draw := (input, (mark, answer.extractLsb' 0 160))
      let updated : Audit :=
        { audit with
          h5cache := audit.h5cache.cacheQuery input answer
          draws := audit.draws ++ [entry] }
      (fun result =>
        ((result.1.1,
          entry :: result.1.2),
          result.2)) <$> run (next answer) updated
  | .recordPublic pair next, audit => run next (publicStep audit pair)
  | .recordSign pair next, audit => run next (signStep audit pair)
  | .coin n next, audit => do
      let answer ← $ᵗ Fin (n + 1)
      run (next answer) audit

theorem run_projection {α : Type} (program : Program α) (audit : Audit) :
    Prod.fst <$> run program audit = execute program := by
  induction program generalizing audit with
  | pure value => rfl
  | recordPublic pair next ih => exact ih (publicStep audit pair)
  | recordSign pair next ih => exact ih (signStep audit pair)
  | coin n next ih =>
      simp only [run, execute, map_bind]
      exact bind_congr fun answer => ih answer audit
  | draw input mark next ih =>
      simp only [run, execute, map_bind, Functor.map_map]
      apply bind_congr
      intro answer
      rw [← ih answer
        { audit with
          h5cache := audit.h5cache.cacheQuery input answer
          draws := audit.draws ++
            [(input, (mark, answer.extractLsb' 0 160))] }]
      simp only [Functor.map_map, Function.comp_def]

theorem run_unlabelled_projection {α : Type}
    (program : Program α) (audit : Audit) :
    (fun result => (result.1.1, result.1.2.map Prod.snd)) <$>
      run program audit =
        SecurityIndexProgram.execute (erase program) := by
  calc
    _ = (fun result => (result.1, result.2.map Prod.snd)) <$>
        (Prod.fst <$> run program audit) := by
          simp only [Functor.map_map, Function.comp_def]
    _ = _ := by rw [run_projection, execute_erasure]

noncomputable def auditedAnnotatedGlobal {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) : ProbComp
      (((JointOutcome ((Option α ×
        List GroupedBalancedGameQueryTrace67.Action) × Nat)) ×
        List Draw) × Audit) := do
  let answers ← $ᵗ SecurityGraphIdeal.PrivateTable
  run (GroupedBalancedIndexLabeledGlobal67.global
    (fun cache =>
      GroupedBalancedGraphIndexJointClassTrace67.annotate
        (GroupedBalancedPlantedEagerGraphProjection67.viewOf
          answers interaction budget cache) 0) budget) {}

theorem audited_annotated_projection {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    (fun result => (result.1.1, result.1.2.map Prod.snd)) <$>
      auditedAnnotatedGlobal interaction budget =
        GroupedBalancedPlantedEagerAnnotated67.annotatedJointGlobal
          interaction budget := by
  unfold auditedAnnotatedGlobal
  rw [map_bind]
  apply Eq.trans
    (bind_congr fun answers =>
      run_unlabelled_projection _ {})
  unfold GroupedBalancedPlantedEagerAnnotated67.annotatedJointGlobal
  apply bind_congr
  intro answers
  rw [GroupedBalancedIndexLabeledGlobal67.erase_global]

#print axioms run_projection
#print axioms run_unlabelled_projection
#print axioms audited_annotated_projection

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAudit67
