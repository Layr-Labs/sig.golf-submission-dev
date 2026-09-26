import SigGolfCandidate.Hypertree.GroupedBalancedGraphMeteredErase67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMeteredBound67
import SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerGlobalUnion67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointGlobal67


/-! The class-metered passive experiment projects exactly to the earlier
unmetered monitor used by the stopped planted-oracle coupling. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMeteredCoupling67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphProgramMap67
open GroupedBalancedGraphMeteredErase67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem map_monitored {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    mapProgram drop (GroupedBalancedGraphMeteredBound67.monitored view remaining) =
      GroupedBalancedGraphMonitorSignBound67.monitoredFromCache view remaining := by
  unfold GroupedBalancedGraphMeteredBound67.monitored
    GroupedBalancedGraphMonitorSignBound67.monitoredFromCache
  rw [map_setup]
  congr 1
  funext exposed
  exact map_limited (view exposed) remaining
    (GroupedBalancedGraphMonitorSignBound67.initial exposed) 0

theorem experiment_projection {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    mapOutcome drop <$>
      GroupedBalancedGraphMonitorProgram67.experiment
        (GroupedBalancedGraphMeteredBound67.monitored view remaining) ∅ =
      GroupedBalancedGraphMonitorProgram67.experiment
        (GroupedBalancedGraphMonitorSignBound67.monitoredFromCache
          view remaining) ∅ := by
  unfold GroupedBalancedGraphMonitorProgram67.experiment
  rw [map_bind]
  apply bind_congr
  intro table
  rw [← run_map, map_monitored]

theorem bad_projection {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    Pr[fun result => result.bad = true |
      GroupedBalancedGraphMonitorProgram67.experiment
        (GroupedBalancedGraphMonitorSignBound67.monitoredFromCache
          view remaining) ∅] =
    Pr[fun result => result.bad = true |
      GroupedBalancedGraphMonitorProgram67.experiment
        (GroupedBalancedGraphMeteredBound67.monitored view remaining) ∅] := by
  rw [← experiment_projection]
  simp only [probEvent_map, Function.comp_def, mapOutcome]

#print axioms experiment_projection

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMeteredCoupling67


/-! The graph side of the eager union is the projection of the same joint
graph/H5 monitor used for adaptive query accounting. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerGraphProjection67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedPlantedEagerGlobalUnion67
open GroupedBalancedGraphInteraction67 SecurityGraphIdeal
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def viewOf {α : Type}
    (answers : PrivateTable)
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) (cache : QueryCache PointSpec) :
    View (Option α × List GroupedBalancedGameQueryTrace67.Action) :=
  GroupedBalancedIdealEagerCutoff67.eagerCutoffView answers cache
    (interaction cache) budget

noncomputable def unmeteredGlobal {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) : ProbComp
      (Outcome (Option (Option α ×
        List GroupedBalancedGameQueryTrace67.Action) × Nat × State)) := do
  let answers ← $ᵗ PrivateTable
  GroupedBalancedGraphMonitorProgram67.experiment
    (GroupedBalancedGraphMonitorSignBound67.monitoredFromCache
      (viewOf answers interaction budget) budget) ∅

theorem graphGlobal_eq_unmetered {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    𝒮[graphGlobal interaction budget] =
      𝒮[unmeteredGlobal interaction budget] := by
  unfold graphGlobal unmeteredGlobal
  rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr
  intro answers _
  unfold GroupedBalancedGraphMonitorProgram67.experiment
    GroupedBalancedGraphMonitorSignBound67.monitoredFromCache
  apply evalSPMF_bind_congr
  intro table _
  have emptyComplete :
      complete (∅ : QueryCache PointSpec) table = table := by
    funext point
    simp [complete]
  rw [emptyComplete,
    GroupedBalancedGraphMonitorSetup67.run_setup]
  rfl

noncomputable def jointGlobal {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) : ProbComp
      (GroupedBalancedGraphIndexJoint67.JointOutcome
        (Option α × List GroupedBalancedGameQueryTrace67.Action) ×
        List SecurityIndexTrace.Entry) := do
  let answers ← $ᵗ PrivateTable
  SecurityIndexProgram.execute
    (GroupedBalancedGraphIndexJointGlobal67.global
      (viewOf answers interaction budget) budget)

def dropJoint {α : Type}
    (result : GroupedBalancedGraphIndexJoint67.JointOutcome α ×
      List SecurityIndexTrace.Entry) :
    Outcome (Option α × Nat × State) :=
  GroupedBalancedGraphProgramMap67.mapOutcome
    GroupedBalancedGraphMeteredErase67.drop result.1

theorem unmetered_eq_joint {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    unmeteredGlobal interaction budget =
      dropJoint <$> jointGlobal interaction budget := by
  unfold unmeteredGlobal jointGlobal
  rw [map_bind]
  apply bind_congr
  intro answers
  rw [← GroupedBalancedGraphMeteredCoupling67.experiment_projection
    (viewOf answers interaction budget) budget]
  rw [← GroupedBalancedGraphIndexJointGlobal67.graph_projection
    (viewOf answers interaction budget) budget]
  simp only [Functor.map_map]
  rfl

theorem graphGlobal_eq_joint {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    𝒮[graphGlobal interaction budget] =
      𝒮[dropJoint <$> jointGlobal interaction budget] := by
  rw [graphGlobal_eq_unmetered, unmetered_eq_joint]

theorem eager_global_le_joint_union {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat)
    (event : (Option α ×
      List GroupedBalancedGameQueryTrace67.Action) → Prop) :
    Pr[event | eagerGlobal interaction budget] ≤
      Pr[fun result => result.1.bad = true ∨
        GroupedBalancedPlantedEagerUnion67.optionEvent event
          result.1.value.value |
        jointGlobal interaction budget] := by
  have bound :=
    GroupedBalancedPlantedEagerGlobalUnion67.eager_global_le_graph_union
      interaction budget event
  have same := graphGlobal_eq_joint interaction budget
  have events := probEvent_congr'
    (p := fun result => result.bad = true ∨
      GroupedBalancedPlantedEagerUnion67.optionEvent event result.value.1)
    (q := fun result => result.bad = true ∨
      GroupedBalancedPlantedEagerUnion67.optionEvent event result.value.1)
    (fun _ _ => Iff.rfl) same
  rw [events, probEvent_map] at bound
  simpa only [Function.comp_def, dropJoint,
    GroupedBalancedGraphProgramMap67.mapOutcome,
    GroupedBalancedGraphMeteredErase67.drop] using bound

#print axioms graphGlobal_eq_unmetered
#print axioms graphGlobal_eq_joint
#print axioms eager_global_le_joint_union

end SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerGraphProjection67
