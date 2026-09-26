import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPairedGlobal67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAuditLift67
import SigGolfCandidate.Hypertree.GroupedBalancedStoppedStateSafe67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointGlobal67
import SigGolfCandidate.Hypertree.GroupedBalancedResidualNoPrivate67
import SigGolfCandidate.Hypertree.GroupedBalancedEagerLogCount67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedJointStoppedWitness67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedPairedStoppedFresh67. -/
section
/-! A no-contact joint graph/H5 run ends with an authorized exposure cache. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedJointStateSafe67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedGraphIndexObserve67
open GroupedBalancedGraphMonitorInvariant67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem start_safe {α : Type} (table : PointTable)
    (view : QueryCache PointSpec → View α) (remaining : Nat)
    (result : JointOutcome α × List SecurityIndexTrace.Entry)
    (member : result ∈ support
      (SecurityIndexProgram.execute
        (GroupedBalancedGraphIndexJoint67.start table view remaining)))
    (clean : result.1.bad = false) :
    Safe table result.1.value.state.signedBottom
      result.1.value.state.exposed result.1.value.state.residual := by
  have mapped : result.1 ∈ support
      (GroupedBalancedGraphMonitorProgram67.run table
        (GroupedBalancedGraphMonitorSetup67.cache table)
        (GroupedBalancedGraphMetered67.limited
          (view (GroupedBalancedGraphMonitorSetup67.cache table))
          remaining
          (GroupedBalancedGraphMonitorSignBound67.initial
            (GroupedBalancedGraphMonitorSetup67.cache table)) 0)) := by
    have same :=
      GroupedBalancedGraphIndexJointGlobal67.observe_start table view remaining
    simp only [observe] at same
    rw [← same, support_map]
    exact ⟨result, member, rfl⟩
  exact GroupedBalancedStoppedStateSafe67.run_metered_safe table
    (view (GroupedBalancedGraphMonitorSetup67.cache table)) remaining
    (GroupedBalancedGraphMonitorSignBound67.initial
      (GroupedBalancedGraphMonitorSetup67.cache table)) 0
    (GroupedBalancedGraphMonitorSetup67.cache_safe table)
    result.1 mapped clean

#print axioms start_safe

end SigGolfCandidate.Hypertree.GroupedBalancedJointStateSafe67


/-! A clean joint graph/H5 outcome is an exact stopped execution of the
underlying View, retaining its terminal value and both monitor caches. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedJointStoppedWitness67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedGraphMonitorStop67
open GroupedBalancedGraphMonitorSignCoupling67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem start_clean_execute {α : Type} (table : PointTable)
    (view : QueryCache PointSpec → View α) (budget : Nat)
    (result : JointOutcome α × List SecurityIndexTrace.Entry)
    (member : result ∈ support
      (SecurityIndexProgram.execute
        (GroupedBalancedGraphIndexJoint67.start table view budget)))
    (clean : result.1.bad = false) :
    some (result.1.value.value, result.1.value.remaining,
      result.1.value.state) ∈ support
        (execute table
          (view (GroupedBalancedGraphMonitorSetup67.cache table))
          budget
          (GroupedBalancedGraphMonitorSignBound67.initial
            (GroupedBalancedGraphMonitorSetup67.cache table))) := by
  let exposed := GroupedBalancedGraphMonitorSetup67.cache table
  let initial := GroupedBalancedGraphMonitorSignBound67.initial exposed
  have metered : result.1 ∈ support
      (GroupedBalancedGraphMonitorProgram67.run table exposed
        (GroupedBalancedGraphMetered67.limited
          (view exposed) budget initial 0)) := by
    have same :=
      GroupedBalancedGraphIndexJointGlobal67.observe_start
        table view budget
    simp only [GroupedBalancedGraphIndexObserve67.observe] at same
    rw [← same, support_map]
    exact ⟨result, member, rfl⟩
  have unmetered :
      GroupedBalancedGraphProgramMap67.mapOutcome
        GroupedBalancedGraphMeteredErase67.drop result.1 ∈ support
          (GroupedBalancedGraphMonitorProgram67.run table exposed
            (GroupedBalancedGraphMonitorSignCompiler67.limited
              (view exposed) budget initial)) := by
    rw [← GroupedBalancedGraphMeteredErase67.map_limited
      (view exposed) budget initial 0]
    rw [GroupedBalancedGraphProgramMap67.run_map, support_map]
    exact ⟨result.1, metered, rfl⟩
  have stoppedMember : some
      (result.1.value.value, result.1.value.remaining,
        result.1.value.state) ∈ support
      (stopped table exposed
        (GroupedBalancedGraphMonitorSignCompiler67.limited
          (view exposed) budget initial)) := by
    apply (mem_support_iff_of_evalSPMF_eq
      (GroupedBalancedGraphMonitorStop67.stopped_eq table exposed _) _).mpr
    rw [support_map]
    exact ⟨GroupedBalancedGraphProgramMap67.mapOutcome
      GroupedBalancedGraphMeteredErase67.drop result.1,
      unmetered,
      by simp only [GroupedBalancedGraphProgramMap67.mapOutcome,
          GroupedBalancedGraphMeteredErase67.drop,
          GroupedBalancedGraphMonitorStop67.keep, clean,
          Bool.false_eq_true, if_false]⟩
  exact (mem_support_iff_of_evalSPMF_eq
    (stopped_execute table (view exposed) budget initial
      (GroupedBalancedGraphMonitorSetup67.cache_safe table)) _).mp
    stoppedMember

#print axioms start_clean_execute

end SigGolfCandidate.Hypertree.GroupedBalancedJointStoppedWitness67
end

/-! Recover the graph point table sampled inside the paired audited run.
The table is deliberately existential: it is internal to the simulation,
but support arguments for accepted forgeries may reason with that witness. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPairedTableWitness67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphInteraction67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledPairedGlobal67
open GroupedBalancedIndexLabeledProgram67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem sampled_table {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat)
    (result : SecurityGraphIdeal.PrivateTable ×
      ((GroupedBalancedGraphIndexJoint67.JointOutcome
          ((Option α × List GroupedBalancedGameQueryTrace67.Action) × Nat) ×
          List GroupedBalancedIndexLabeledProgram67.Draw) × Audit))
    (member : result ∈ support (pairedAuditedGlobal interaction budget)) :
    ∃ table : PointTable,
      result.2 ∈ support (run
        (GroupedBalancedIndexLabeledJoint67.start table
          (fun cache =>
            GroupedBalancedGraphIndexJointClassTrace67.annotate
              (GroupedBalancedPlantedEagerGraphProjection67.viewOf
                result.1 interaction budget cache) 0)
          budget) {}) := by
  unfold pairedAuditedGlobal at member
  simp only [mem_support_bind_iff] at member
  obtain ⟨answers, _, child⟩ := member
  obtain ⟨auditResult, auditMember, same⟩ := child
  simp only [support_pure, Set.mem_singleton_iff] at same
  subst result
  rw [GroupedBalancedIndexLabeledGlobal67.global,
    GroupedBalancedIndexLabeledAuditLift67.run_unmarked,
    mem_support_bind_iff] at auditMember
  obtain ⟨table, _, witness⟩ := auditMember
  exact ⟨table, witness⟩

#print axioms sampled_table

end SigGolfCandidate.Hypertree.GroupedBalancedPairedTableWitness67


/-! Transport direct private-source cache freshness from a stopped eager
View to the paired, audited graph/H5 experiment. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPairedStoppedFresh67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphInteraction67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledPairedGlobal67
open GroupedBalancedGameQueryTrace67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

abbrev PairedResult (α : Type) :=
  SecurityGraphIdeal.PrivateTable ×
    ((GroupedBalancedGraphIndexJoint67.JointOutcome
        ((Option α × List Action) × Nat) × List Draw) × Audit)

theorem paired_clean_execute {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) (result : PairedResult α)
    (member : result ∈ support (pairedAuditedGlobal interaction budget))
    (clean : result.2.1.1.bad = false) :
    ∃ table : PointTable,
      some (result.2.1.1.value.value,
        result.2.1.1.value.remaining,
        result.2.1.1.value.state) ∈ support
        (GroupedBalancedGraphMonitorSignCoupling67.execute table
          (GroupedBalancedGraphIndexJointClassTrace67.annotate
            (GroupedBalancedPlantedEagerGraphProjection67.viewOf
              result.1 interaction budget
              (GroupedBalancedGraphMonitorSetup67.cache table)) 0)
          budget
          (GroupedBalancedGraphMonitorSignBound67.initial
            (GroupedBalancedGraphMonitorSetup67.cache table))) := by
  obtain ⟨table, inner⟩ :=
    GroupedBalancedPairedTableWitness67.sampled_table
      interaction budget result member
  let view : QueryCache PointSpec → View
      ((Option α × List Action) × Nat) :=
    fun cache =>
      GroupedBalancedGraphIndexJointClassTrace67.annotate
        (GroupedBalancedPlantedEagerGraphProjection67.viewOf
          result.1 interaction budget cache) 0
  have labeled : result.2.1 ∈ support
      (execute (GroupedBalancedIndexLabeledJoint67.start table view budget)) := by
    rw [← GroupedBalancedIndexLabeledAudit67.run_projection]
    rw [support_map]
    exact ⟨result.2, inner, rfl⟩
  have unlabelled :
      (result.2.1.1, result.2.1.2.map Prod.snd) ∈ support
        (SecurityIndexProgram.execute
          (GroupedBalancedGraphIndexJoint67.start table view budget)) := by
    rw [← GroupedBalancedIndexLabeledJoint67.erase_start,
      ← GroupedBalancedIndexLabeledProgram67.execute_erasure,
      support_map]
    exact ⟨result.2.1, labeled, rfl⟩
  exact ⟨table, GroupedBalancedJointStoppedWitness67.start_clean_execute
    table view budget _ unlabelled clean⟩

theorem annotated_completed_eager {α : Type}
    (answers : SecurityGraphIdeal.PrivateTable) (table : PointTable)
    (cache : QueryCache PointSpec) (interaction : Interaction α)
    (budget remaining : Nat) (state final : State)
    (value : Option α) (trace : List Action)
    (count left : Nat)
    (member : some (some ((value, trace), count), left, final) ∈ support
      (GroupedBalancedGraphMonitorSignCoupling67.execute table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          (GroupedBalancedIdealEagerCutoff67.eagerCutoffView
            answers cache interaction budget) 0)
        remaining state)) :
    some (some (value, trace), left, final) ∈ support
      (GroupedBalancedGraphMonitorSignCoupling67.execute table
        (GroupedBalancedIdealEagerCutoff67.eagerCutoffView
          answers cache interaction budget)
        remaining state) := by
  rw [GroupedBalancedEagerLogCount67.eager_log_count] at member
  rw [GroupedBalancedStoppedMapView67.execute_mapView,
    support_map] at member
  obtain ⟨source, sourceMember, same⟩ := member
  cases source with
  | none => cases same
  | some source =>
      rcases source with ⟨maybe, left', final'⟩
      cases maybe with
      | none => cases same
      | some pair =>
          rcases pair with ⟨value', trace'⟩
          simp only [GroupedBalancedStoppedMapView67.mapResult,
            Option.map_some, GroupedBalancedEagerLogCount67.marked] at same
          cases same
          exact sourceMember

theorem paired_clean_private_fresh {α : Type}
    (secretKey : SecretKey)
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) (result : PairedResult α)
    (value : Option α) (trace : List Action) (count : Nat)
    (member : result ∈ support (pairedAuditedGlobal interaction budget))
    (clean : result.2.1.1.bad = false)
    (completed : result.2.1.1.value.value =
      some ((value, trace), count))
    (noHit : ¬SecuritySecretKey.SecretKeyHitTrace
      (secretInputs trace) secretKey) :
    ∀ slot : GroupedBalancedPrivateDerivation67.Slot,
      result.2.1.1.value.state.residual
        (GroupedBalancedPrivateDerivation67.input secretKey slot) = none := by
  obtain ⟨table, stopped⟩ :=
    paired_clean_execute interaction budget result member clean
  rw [completed] at stopped
  let exposed := GroupedBalancedGraphMonitorSetup67.cache table
  let initial := GroupedBalancedGraphMonitorSignBound67.initial exposed
  have eager : some (some (value, trace),
      result.2.1.1.value.remaining,
      result.2.1.1.value.state) ∈ support
        (GroupedBalancedGraphMonitorSignCoupling67.execute table
          (GroupedBalancedIdealEagerCutoff67.eagerCutoffView
            result.1 exposed (interaction exposed) budget)
          budget initial) := by
    exact annotated_completed_eager result.1 table exposed
      (interaction exposed) budget budget initial
      result.2.1.1.value.state value trace count
      result.2.1.1.value.remaining (by
        simpa only [GroupedBalancedPlantedEagerGraphProjection67.viewOf]
          using stopped)
  exact GroupedBalancedResidualNoPrivate67.eager_private_fresh
    secretKey result.1 table exposed (interaction exposed) budget budget
    initial result.2.1.1.value.state value trace
    result.2.1.1.value.remaining eager
    (by intro slot; rfl) noHit

#print axioms paired_clean_execute
#print axioms annotated_completed_eager
#print axioms paired_clean_private_fresh

end SigGolfCandidate.Hypertree.GroupedBalancedPairedStoppedFresh67
