import SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerExecute67
import SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerCutoffBudget67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSetup67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerProjection67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerGlobalUnion67. -/
section
/-! Project the ordinary graph execution back to the exact planted-cache
World interpretation of the eager ideal View. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerProjection67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJointTotalView67
open GroupedBalancedGraphViewWorld67
open GroupedBalancedPlantedEagerExecute67
open GroupedBalancedPlantedCache67
open GroupedBalancedIdealEagerCutoff67
open GroupedBalancedPlantedEagerHop67
open GroupedBalancedGraphInteraction67 SecurityGraphIdeal
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

noncomputable def graphWorld (table : PointTable) :
    QueryImpl World (StateT (QueryCache HashSpec) ProbComp) :=
  GroupedBalancedGraphOracle67.implementation
    (GroupedBalancedGraphMonitorTable67.privateOf table)
    (GroupedBalancedGraphMonitorTable67.labelsOf table)

private theorem world_hash_run {α : Type} (table : PointTable)
    (input : Query) (next : BitVec 256 → View α)
    (residual : QueryCache HashSpec) :
    (simulateQ (graphWorld table)
      (ofView table (.hash input next))).run' residual =
    ((GroupedBalancedGraphOracle67.publicOracle
      (GroupedBalancedGraphMonitorTable67.privateOf table)
      (GroupedBalancedGraphMonitorTable67.labelsOf table) input).run residual
      >>= fun result =>
        (simulateQ (graphWorld table)
          (ofView table (next result.1))).run' result.2) := by
  simp only [ofView, simulateQ_bind, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query,
    id_map, StateT.run'_eq, StateT.run_bind,
    graphWorld, GroupedBalancedGraphOracle67.implementation]
  rw [map_bind]
  rfl

private theorem world_private_run {α : Type} (table : PointTable)
    (input : Query)
    (outside : GroupedBalancedGraphQuery67.locate input = none)
    (next : BitVec 256 → View α)
    (residual : QueryCache HashSpec) :
    (simulateQ (graphWorld table)
      (ofView table (.privateHash input outside next))).run' residual =
    ((GroupedBalancedGraphOracle67.publicOracle
      (GroupedBalancedGraphMonitorTable67.privateOf table)
      (GroupedBalancedGraphMonitorTable67.labelsOf table) input).run residual
      >>= fun result =>
        (simulateQ (graphWorld table)
          (ofView table (next result.1))).run' result.2) := by
  simpa only [ofView] using world_hash_run table input next residual

theorem public_run {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (budget : TotalBudget remaining view) :
    Prod.fst <$> execute table view remaining state =
      Option.some <$> (simulateQ (graphWorld table) (ofView table view)).run'
        state.residual := by
  induction view generalizing remaining state with
  | done value =>
      simp [execute, ofView, graphWorld]
  | coin n next ih =>
      change (do
        let answer ← $ᵗ Fin (n + 1)
        Prod.fst <$> execute table (next answer) remaining state) =
        (do
          let answer ← $ᵗ Fin (n + 1)
          Option.some <$> (simulateQ (graphWorld table)
            (ofView table (next answer))).run' state.residual)
      apply bind_congr
      intro answer
      exact ih answer remaining state (budget answer)
  | sign index next ih =>
      change Prod.fst <$> execute table
          (next (table (.inr (.inl index)))) remaining
          (signed state index (table (.inr (.inl index)))) =
        Option.some <$>
          (simulateQ (graphWorld table)
            (ofView table (next (table (.inr (.inl index)))))).run'
              state.residual
      exact ih _ remaining _ (budget _)
  | privateHash input outside next ih =>
      have graphNone : GroupedBalancedGraphOracle67.canonical
          (GroupedBalancedGraphMonitorTable67.privateOf table)
          (GroupedBalancedGraphMonitorTable67.labelsOf table) input = none := by
        simp [GroupedBalancedGraphOracle67.canonical, outside]
      have publicEq :
          GroupedBalancedGraphOracle67.publicOracle
            (GroupedBalancedGraphMonitorTable67.privateOf table)
            (GroupedBalancedGraphMonitorTable67.labelsOf table) input =
          randomOracle (spec := HashSpec) input := by
        simp [GroupedBalancedGraphOracle67.publicOracle, graphNone]
      rw [world_private_run table input outside next, publicEq, map_bind]
      cases present : state.residual input with
      | some answer =>
          simp only [execute, present, randomOracle.run_eq,
            pure_bind, map_pure]
          exact ih answer remaining state
            (GroupedBalancedIdealEagerCutoffBudget67.total_mono _
              (remaining - 1) remaining (by omega) (budget.2 answer))
      | none =>
          simp only [execute, present, randomOracle.run_eq,
            map_bind, bind_assoc]
          apply bind_congr
          intro answer
          simp only [pure_bind]
          simpa only [privateOpened] using
            ih answer remaining (privateOpened state input answer)
              (GroupedBalancedIdealEagerCutoffBudget67.total_mono _
                (remaining - 1) remaining (by omega) (budget.2 answer))
  | hash input next ih =>
      cases remaining with
      | zero => exact False.elim (Nat.lt_irrefl 0 budget.1)
      | succ remaining =>
          rw [world_hash_run]
          simp only [execute, map_bind]
          apply bind_congr
          intro result
          exact ih result.1 remaining
            (opened state
              (GroupedBalancedGraphMonitorPublicCoupling67.opened
                table state.exposed input) result.2)
            (budget.2 result.1)

theorem public_run_planted {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (budget : TotalBudget remaining view) :
    Prod.fst <$> execute table view remaining state =
      Option.some <$> SecurityGraphHidden.observe (ofView table view)
        (GroupedBalancedGraphOracle67.embed
          (GroupedBalancedGraphMonitorTable67.privateOf table)
          (GroupedBalancedGraphMonitorTable67.labelsOf table)
          state.residual) := by
  rw [public_run table view remaining state budget]
  have embedded := GroupedBalancedGraphOracle67.observe_eq
    (GroupedBalancedGraphMonitorTable67.privateOf table)
    (GroupedBalancedGraphMonitorTable67.labelsOf table)
    (ofView table view) state.residual
  change SecurityGraphHidden.observe (ofView table view)
      (GroupedBalancedGraphOracle67.embed
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        (GroupedBalancedGraphMonitorTable67.labelsOf table) state.residual) =
      (simulateQ (graphWorld table) (ofView table view)).run'
        state.residual at embedded
  rw [embedded]

theorem eagerSimulation_projection {α : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (interaction : Interaction α)
    (budget : Nat) :
    Option.some <$> eagerSimulation table cache interaction budget =
      (do
        let answers ← $ᵗ PrivateTable
        Prod.fst <$> execute table
          (eagerCutoffView answers cache interaction budget) budget
          (GroupedBalancedGraphMonitorSignBound67.initial cache)) := by
  simp only [eagerSimulation, map_bind]
  apply bind_congr
  intro answers
  have total := GroupedBalancedIdealEagerCutoffBudget67.eager_cutoff_total
    answers cache interaction budget
  have projected := public_run_planted table
    (eagerCutoffView answers cache interaction budget) budget
    (GroupedBalancedGraphMonitorSignBound67.initial cache) total
  simpa only [GroupedBalancedGraphMonitorSignBound67.initial,
    GroupedBalancedPlantedCache67.planted] using projected.symm

#print axioms public_run
#print axioms eagerSimulation_projection

end SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerProjection67
end

/-! Transfer any eager ideal event to the one sampled graph monitor, charging
the first hidden-predecessor or output contact in that same run. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerUnion67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphMonitorSignCoupling67
open GroupedBalancedPlantedEagerExecute67
open GroupedBalancedPlantedEagerProjection67
open GroupedBalancedPlantedEagerHop67
open GroupedBalancedGraphInteraction67 SecurityGraphIdeal
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

def optionEvent {α : Type} (event : α → Prop) : Option α → Prop
  | none => False
  | some value => event value

theorem eager_le_graph_union {α : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (interaction : Interaction α)
    (budget : Nat)
    (safe : GroupedBalancedGraphMonitorInvariant67.Safe table ∅ cache ∅)
    (event : (Option α × List GroupedBalancedGameQueryTrace67.Action) → Prop) :
    Pr[event | eagerSimulation table cache interaction budget] ≤
      Pr[fun result => result.bad = true ∨
        optionEvent event result.value.1 |
        (do
          let answers ← $ᵗ PrivateTable
          run table cache
            (GroupedBalancedGraphMonitorSignCompiler67.limited
              (GroupedBalancedIdealEagerCutoff67.eagerCutoffView answers cache
                interaction budget)
              budget
              (GroupedBalancedGraphMonitorSignBound67.initial cache)))] := by
  have projected := eagerSimulation_projection table cache interaction budget
  have first :
      Pr[event | eagerSimulation table cache interaction budget] =
      Pr[optionEvent event |
        Option.some <$> eagerSimulation table cache interaction budget] := by
    rw [probEvent_map]
    rfl
  rw [first, projected]
  simp only [probEvent_bind_eq_tsum, probEvent_map]
  apply ENNReal.tsum_le_tsum
  intro answers
  have bound := execute_le_union table
    (GroupedBalancedIdealEagerCutoff67.eagerCutoffView answers cache
      interaction budget) budget
    (GroupedBalancedGraphMonitorSignBound67.initial cache) safe
    (fun result => optionEvent event result.1)
  exact mul_le_mul' le_rfl bound

#print axioms eager_le_graph_union

end SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerUnion67


/-! Sample the direct67 graph once before the eager ideal interaction. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerGlobalUnion67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedPlantedEagerUnion67
open GroupedBalancedPlantedEagerHop67
open GroupedBalancedGraphInteraction67 SecurityGraphIdeal
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def eagerGlobal {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) : ProbComp (Option α ×
      List GroupedBalancedGameQueryTrace67.Action) := do
  let table ← $ᵗ PointTable
  GroupedBalancedPlantedEagerHop67.eagerSimulation table
    (GroupedBalancedGraphMonitorSetup67.cache table)
    (interaction (GroupedBalancedGraphMonitorSetup67.cache table)) budget

noncomputable def graphGlobal {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) : ProbComp
      (Outcome (Option (Option α ×
        List GroupedBalancedGameQueryTrace67.Action) × Nat × State)) := do
  let table ← $ᵗ PointTable
  let answers ← $ᵗ PrivateTable
  run table (GroupedBalancedGraphMonitorSetup67.cache table)
    (limited
      (GroupedBalancedIdealEagerCutoff67.eagerCutoffView answers
        (GroupedBalancedGraphMonitorSetup67.cache table)
        (interaction (GroupedBalancedGraphMonitorSetup67.cache table)) budget)
      budget
      (GroupedBalancedGraphMonitorSignBound67.initial
        (GroupedBalancedGraphMonitorSetup67.cache table)))

theorem eager_global_le_graph_union {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat)
    (event : (Option α ×
      List GroupedBalancedGameQueryTrace67.Action) → Prop) :
    Pr[event | eagerGlobal interaction budget] ≤
      Pr[fun result => result.bad = true ∨
        optionEvent event result.value.1 | graphGlobal interaction budget] := by
  unfold eagerGlobal graphGlobal
  conv_lhs => rw [probEvent_bind_eq_tsum]
  conv_rhs => rw [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro table
  exact mul_le_mul' le_rfl
    (eager_le_graph_union table
      (GroupedBalancedGraphMonitorSetup67.cache table)
      (interaction (GroupedBalancedGraphMonitorSetup67.cache table)) budget
      (GroupedBalancedGraphMonitorSetup67.cache_safe table) event)

#print axioms eager_global_le_graph_union

end SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerGlobalUnion67
