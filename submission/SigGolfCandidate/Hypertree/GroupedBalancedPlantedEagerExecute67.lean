import SigGolfCandidate.Hypertree.GroupedBalancedPlantedSecretKeyClass67
import SigGolfCandidate.Hypertree.SecurityGraphIdeal
import SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerCutoffBudget67
import SigGolfCandidate.Hypertree.GroupedBalancedGameQueryTrace67
import SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerCutoff67
import SigGolfCandidate.Hypertree.GroupedBalancedPlantedCache67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSignCoupling67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerWinView67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerExecute67. -/
section
/-! The full-H action logger preserves its original GameWorld result. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGameQueryProject67
open SigGolf SigGolfCandidate.Hypertree OracleComp OracleSpec
open GroupedBalancedGameQueryTrace67
open SecurityGameHop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem logged_fst {α : Type} (program : OracleComp GameWorld α) :
    Prod.fst <$> logged program = program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      rw [logged_query_bind]
      simp only [map_bind]
      apply bind_congr
      intro answer
      simpa only [map_eq_pure_bind, bind_assoc, pure_bind] using ih answer

#print axioms logged_fst

end SigGolfCandidate.Hypertree.GroupedBalancedGameQueryProject67


/-! The ideal cutoff game's returned result is exactly the projection of the
eager independent-slot stopped View. This uses the same View as the sharp
secret-key class penalty, including paths ending at the hash-call cutoff. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerWinView67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleComp.EvalDist OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedPlantedCache67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphViewWorld67
open GroupedBalancedGameWorld67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedGameQueryProject67
open GroupedBalancedIdealEagerCutoff67
open SecurityGameHop SecurityGraphIdeal SecurityGraphHidden
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem observe_map {α β : Type} (f : α → β)
    (program : OracleComp World α) (cache : QueryCache HashSpec) :
    observe (f <$> program) cache = f <$> observe program cache := by
  simp only [observe, simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map]

theorem fixPrivate_cutoff {α : Type} (answers : PrivateTable)
    (table : PointTable) (cache : QueryCache PointSpec)
    (interaction : Interaction α) (budget : Nat) :
    fixPrivate answers
      (SecurityBudget.cutoff (gameView table cache interaction) budget) =
      Prod.fst <$> ofView table
        (eagerCutoffView answers cache interaction budget) := by
  let program := SecurityBudget.cutoff
    (gameView table cache interaction) budget
  calc
    fixPrivate answers program =
        fixPrivate answers (Prod.fst <$> logged program) := by
          rw [logged_fst]
    _ = Prod.fst <$> fixPrivate answers (logged program) :=
      fixPrivate_map answers Prod.fst _
    _ = _ := by
      rw [fixPrivate_logged_cutoff]

theorem ideal_cutoff_view {α : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (interaction : Interaction α)
    (budget : Nat) :
    𝒮[idealObserve
      (SecurityBudget.cutoff (gameView table cache interaction) budget)
      ∅ (planted table)] =
      𝒮[do
        let answers ← $ᵗ PrivateTable
        Prod.fst <$> observe
          (ofView table (eagerCutoffView answers cache interaction budget))
          (planted table)] := by
  calc
    _ = 𝒮[do
          let answers ← $ᵗ PrivateTable
          observe
            (fixPrivate answers
              (SecurityBudget.cutoff
                (gameView table cache interaction) budget))
            (planted table)] :=
      ideal_private_table _ ∅ (planted table)
    _ = _ := by
      simp_rw [fixPrivate_cutoff, observe_map]

theorem ideal_counted_event_eq_eager {α : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (interaction : Interaction α)
    (budget : Nat) (event : α → Prop) :
    Pr[fun result => event result.1 ∧ result.2 ≤ budget |
      (simulateQ idealGameOracle
        (SecurityBudget.counted
          (gameView table cache interaction))).run' (∅, planted table)] =
    Pr[fun value => ∃ result,
      value = some result ∧ event result | do
        let answers ← $ᵗ PrivateTable
        Prod.fst <$> observe
          (ofView table (eagerCutoffView answers cache interaction budget))
          (planted table)] := by
  calc
    _ = Pr[fun value => ∃ result,
        value = some result ∧ event result |
          idealObserve
            (SecurityBudget.cutoff
              (gameView table cache interaction) budget)
            ∅ (planted table)] := by
      exact (SecurityBudget.prob_cutoff_eq_counted idealGameOracle
        (gameView table cache interaction)
        (∅, planted table) budget event).symm
    _ = _ := by
      unfold probEvent
      rw [ideal_cutoff_view]

#print axioms fixPrivate_cutoff
#print axioms ideal_cutoff_view
#print axioms ideal_counted_event_eq_eager

end SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerWinView67
end

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerPenaltyView67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerExecute67. -/
section
/-! Move the sharp secret-key class loss from the ideal lazy private oracle
to an independently sampled eager private-slot table, leaving the planted
public graph cache and the full stopped H log unchanged. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPlantedIdealEager67
open SigGolf SigGolfCandidate.Hypertree OracleComp OracleComp.EvalDist OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedPlantedCache67
open GroupedBalancedPlantedSecretKeyClass67
open GroupedBalancedGameQueryTrace67
open SecurityGameHop SecurityGraphIdeal SecurityGraphHidden
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def eagerClassPenalty {α : Type} (table : PointTable)
    (program : OracleComp GameWorld α) (budget : Nat) : ENNReal :=
  expectedValue
    (do
      let answers ← $ᵗ PrivateTable
      observe
        (fixPrivate answers
          (logged (SecurityBudget.cutoff program budget)))
        (planted table))
    (fun result => ((counts result.2).secretKey : ENNReal))

theorem classPenalty_eq_eager {α : Type} (table : PointTable)
    (program : OracleComp GameWorld α) (budget : Nat) :
    classPenalty table program budget =
      eagerClassPenalty table program budget := by
  unfold classPenalty eagerClassPenalty
  apply expectedValue_congr
  intro result
  change evalSPMF
      (idealObserve
        (logged (SecurityBudget.cutoff program budget)) ∅ (planted table))
      result =
    evalSPMF
      (do
        let answers ← $ᵗ PrivateTable
        observe
          (fixPrivate answers
            (logged (SecurityBudget.cutoff program budget)))
          (planted table)) result
  exact congrArg (fun distribution => distribution result)
    (ideal_private_table
      (logged (SecurityBudget.cutoff program budget)) ∅ (planted table))

#print axioms classPenalty_eq_eager

end SigGolfCandidate.Hypertree.GroupedBalancedPlantedIdealEager67


/-! The secret-key-class loss is an expectation over the same exact stopped
ideal signing View whose graph/H5 contact monitor can now be run pointwise. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerPenaltyView67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleComp.EvalDist OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedPlantedCache67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphViewWorld67
open GroupedBalancedGameWorld67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedPlantedSecretKeyClass67
open GroupedBalancedPlantedIdealEager67
open GroupedBalancedIdealEagerCutoff67
open SecurityGameHop SecurityGraphIdeal SecurityGraphHidden
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem eagerClassPenalty_interaction {α : Type}
    (table : PointTable) (cache : QueryCache PointSpec)
    (interaction : Interaction α) (budget : Nat) :
    eagerClassPenalty table (gameView table cache interaction) budget =
      expectedValue
        (do
          let answers ← $ᵗ PrivateTable
          observe
            (ofView table
              (eagerCutoffView answers cache interaction budget))
            (planted table))
        (fun result => ((counts result.2).secretKey : ENNReal)) := by
  unfold eagerClassPenalty
  simp_rw [fixPrivate_logged_cutoff]

theorem classPenalty_interaction {α : Type}
    (table : PointTable) (cache : QueryCache PointSpec)
    (interaction : Interaction α) (budget : Nat) :
    classPenalty table (gameView table cache interaction) budget =
      expectedValue
        (do
          let answers ← $ᵗ PrivateTable
          observe
            (ofView table
              (eagerCutoffView answers cache interaction budget))
            (planted table))
        (fun result => ((counts result.2).secretKey : ENNReal)) := by
  rw [classPenalty_eq_eager]
  exact eagerClassPenalty_interaction table cache interaction budget

#print axioms classPenalty_interaction

end SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerPenaltyView67
end

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerHop67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerExecute67. -/
section
/-! The planted real organizer hop has both its ideal win event and its sharp
secret-key loss measured on one exact eager-slot stopped View simulation. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerHop67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleComp.EvalDist OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedPlantedCache67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphViewWorld67
open GroupedBalancedGameWorld67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedPlantedSecretKeyClass67
open GroupedBalancedIdealEagerPenaltyView67
open GroupedBalancedIdealEagerWinView67
open GroupedBalancedIdealEagerCutoff67
open SecurityGameHop SecurityGraphIdeal SecurityGraphHidden
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def eagerSimulation {α : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (interaction : Interaction α)
    (budget : Nat) : ProbComp (Option α × List Action) := do
  let answers ← $ᵗ PrivateTable
  observe (ofView table
    (eagerCutoffView answers cache interaction budget)) (planted table)

theorem ideal_event_simulation {α : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (interaction : Interaction α)
    (budget : Nat) (event : α → Prop) :
    Pr[fun result => event result.1 ∧ result.2 ≤ budget |
      (simulateQ idealGameOracle
        (SecurityBudget.counted
          (gameView table cache interaction))).run' (∅, planted table)] =
    Pr[fun result => ∃ value,
      result.1 = some value ∧ event value |
      eagerSimulation table cache interaction budget] := by
  rw [ideal_counted_event_eq_eager]
  have projection : Prod.fst <$> eagerSimulation table cache interaction budget =
      (do
        let answers ← $ᵗ PrivateTable
        Prod.fst <$> observe
          (ofView table (eagerCutoffView answers cache interaction budget))
          (planted table)) := by
    simp only [eagerSimulation, map_bind]
  rw [← projection, probEvent_map]
  rfl

theorem classPenalty_simulation {α : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (interaction : Interaction α)
    (budget : Nat) :
    classPenalty table (gameView table cache interaction) budget =
      expectedValue (eagerSimulation table cache interaction budget)
        (fun result => ((counts result.2).secretKey : ENNReal)) :=
  classPenalty_interaction table cache interaction budget

/-- Both the ideal win event and the exact secret-key-class loss are now
expressed on the same eager-slot View run. -/
theorem planted_hop_eager {α : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (interaction : Interaction α)
    (budget : Nat) (event : α → Prop) :
    Pr[fun result => event result.1 ∧ result.2 ≤ budget |
      sampleSecretKey >>= fun secretKey =>
        (simulateQ (realGameOracle secretKey)
          (SecurityBudget.counted
            (gameView table cache interaction))).run' (planted table)] ≤
    Pr[fun result => ∃ value,
      result.1 = some value ∧ event value |
      eagerSimulation table cache interaction budget] +
      expectedValue (eagerSimulation table cache interaction budget)
        (fun result => ((counts result.2).secretKey : ENNReal)) /
          (2 : ENNReal) ^ 128 := by
  have hop := planted_counted_hop_class table
    (gameView table cache interaction) budget event
  simpa only [ideal_event_simulation, classPenalty_simulation] using hop

#print axioms ideal_event_simulation
#print axioms planted_hop_eager

end SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerHop67

end

/-! The eager ideal View executed against the planted public graph has the same
answers as an explicit public-graph oracle.  The stopped monitor retains every
contact-free path of this execution. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerExecute67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphMonitorInvariant67
open GroupedBalancedGraphMonitorPublicCoupling67
open GroupedBalancedGraphMonitorSignCoupling67
open GroupedBalancedPlantedEagerHop67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

/-- The full public-graph execution, including the state needed for later
contact tests, but without stopping at a contact. -/
noncomputable def execute {α : Type} (table : PointTable) :
    View α → Nat → State → ProbComp (Option α × Nat × State)
  | .done value, remaining, state => pure (some value, remaining, state)
  | .coin n next, remaining, state => do
      let answer ← $ᵗ Fin (n + 1)
      execute table (next answer) remaining state
  | .sign index next, remaining, state =>
      let answer := table (.inr (.inl index))
      execute table (next answer) remaining (signed state index answer)
  | .privateHash input _ next, remaining, state =>
      match state.residual input with
      | some answer => execute table (next answer) remaining state
      | none => do
          let answer ← $ᵗ BitVec 256
          execute table (next answer) remaining
            (privateOpened state input answer)
  | .hash input next, remaining, state =>
      match remaining with
      | 0 => pure (none, 0, state)
      | remaining + 1 => do
          let result ← (GroupedBalancedGraphOracle67.publicOracle
            (GroupedBalancedGraphMonitorTable67.privateOf table)
            (GroupedBalancedGraphMonitorTable67.labelsOf table) input).run
              state.residual
          execute table (next result.1) remaining
            (opened state
              (GroupedBalancedGraphMonitorPublicCoupling67.opened
                table state.exposed input) result.2)

def stoppedEvent {α : Type}
    (event : Option α × Nat × State → Prop) :
    Option (Option α × Nat × State) → Prop
  | none => True
  | some result => event result

/-- The ordinary public-graph execution is covered by the same event in the
stopped execution, or by its first contact. -/
theorem execute_le_stopped {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (safe : Safe table state.signedBottom state.exposed state.residual)
    (event : Option α × Nat × State → Prop) :
    Pr[event | execute table view remaining state] ≤
      Pr[stoppedEvent event |
        GroupedBalancedGraphMonitorSignCoupling67.execute table view
          remaining state] := by
  induction view generalizing remaining state with
  | done value =>
      simp only [execute, GroupedBalancedGraphMonitorSignCoupling67.execute,
        probEvent_pure, stoppedEvent, le_refl]
  | coin n next ih =>
      simp only [execute, GroupedBalancedGraphMonitorSignCoupling67.execute,
        probEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro answer
      exact mul_le_mul' le_rfl (ih answer remaining state safe)
  | sign index next ih =>
      change Pr[event | execute table
          (next (table (.inr (.inl index)))) remaining
          (signed state index (table (.inr (.inl index))))] ≤
        Pr[stoppedEvent event |
          GroupedBalancedGraphMonitorSignCoupling67.execute table
            (next (table (.inr (.inl index)))) remaining
            (signed state index (table (.inr (.inl index))))]
      exact ih _ remaining _
        (GroupedBalancedGraphSignExposure67.safe_reveal_bottom
          table state.signedBottom state.exposed state.residual safe index)
  | privateHash input outside next ih =>
      simp only [execute, GroupedBalancedGraphMonitorSignCoupling67.execute]
      cases present : state.residual input with
      | some answer =>
          simp only [present]
          exact ih answer remaining state safe
      | none =>
          simp only [present, probEvent_bind_eq_tsum]
          apply ENNReal.tsum_le_tsum
          intro answer
          have residualSafe : ResidualSafe table
              (state.residual.cacheQuery input answer) := by
            apply GroupedBalancedGraphMonitorInvariant67.ResidualSafe.cacheQuery
              table state.residual safe.2.2 input answer
            intro position located
            rw [outside] at located
            cases located
          exact mul_le_mul' le_rfl
            (ih answer remaining (privateOpened state input answer)
              ⟨safe.1, safe.2.1, residualSafe⟩)
  | hash input next ih =>
      cases remaining with
      | zero =>
          simp only [execute, GroupedBalancedGraphMonitorSignCoupling67.execute,
            probEvent_pure, stoppedEvent, le_refl]
      | succ remaining =>
          simp only [execute, GroupedBalancedGraphMonitorSignCoupling67.execute]
          by_cases first : inputHit table state.exposed input
          · simp only [if_pos first, probEvent_pure, stoppedEvent, if_true]
            exact probEvent_le_one
          · simp only [if_neg first, probEvent_bind_eq_tsum]
            apply ENNReal.tsum_le_tsum
            intro result
            by_cases member : result ∈ support
                ((GroupedBalancedGraphOracle67.publicOracle
                  (GroupedBalancedGraphMonitorTable67.privateOf table)
                  (GroupedBalancedGraphMonitorTable67.labelsOf table) input).run
                    state.residual)
            · by_cases second : outputHit table input result.1
              · simp only [if_pos second, probEvent_pure, stoppedEvent, if_true]
                exact mul_le_mul' le_rfl probEvent_le_one
              · simp only [if_neg second]
                have queried :=
                  GroupedBalancedGraphMonitorCompileCoupling67.read_supported
                    table state.signedBottom state.exposed state.residual safe
                    input result member first second
                have nextSafe :=
                  GroupedBalancedGraphMonitorPublicUnified67.public_read_safe
                    table state.signedBottom state.exposed state.residual safe
                    input
                    (result.1,
                      GroupedBalancedGraphMonitorPublicCoupling67.opened
                        table state.exposed input,
                      result.2) queried
                exact mul_le_mul' le_rfl
                  (ih result.1 remaining
                    (opened state
                      (GroupedBalancedGraphMonitorPublicCoupling67.opened
                        table state.exposed input) result.2) nextSafe)
            · have zero := (probOutput_eq_zero_iff _ _).mpr member
              simp only [zero, zero_mul, le_refl]

/-- The contact flag and the ordinary event are evaluated in the same
sampled graph run. -/
theorem execute_le_union {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (safe : Safe table state.signedBottom state.exposed state.residual)
    (event : Option α × Nat × State → Prop) :
    Pr[event | execute table view remaining state] ≤
      Pr[fun result => result.bad = true ∨ event result.value |
        run table state.exposed
          (GroupedBalancedGraphMonitorSignCompiler67.limited
            view remaining state)] := by
  have bound := execute_le_stopped table view remaining state safe event
  have same :=
    GroupedBalancedGraphMonitorSignCoupling67.stopped_execute
      table view remaining state safe
  have sameStopped :=
    (GroupedBalancedGraphMonitorStop67.stopped_eq table state.exposed
      (GroupedBalancedGraphMonitorSignCompiler67.limited
        view remaining state)).symm.trans same
  have events := probEvent_congr'
    (p := stoppedEvent event) (q := stoppedEvent event)
    (fun _ _ => Iff.rfl) sameStopped
  rw [← events, probEvent_map] at bound
  apply bound.trans_eq
  apply probEvent_congr' _ rfl
  intro result _
  cases bad : result.bad <;>
    simp [GroupedBalancedGraphMonitorStop67.keep, bad, stoppedEvent]

#print axioms execute_le_stopped
#print axioms execute_le_union

end SigGolfCandidate.Hypertree.GroupedBalancedPlantedEagerExecute67
