import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSignCoupling67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMeteredErase67

/-! The stopped graph execution retains the authorization and residual-cache
invariants on every completed path. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedStoppedStateSafe67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphMonitorInvariant67
open GroupedBalancedGraphMonitorSignCoupling67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem execute_safe {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (initial : Safe table state.signedBottom state.exposed state.residual) :
    ∀ result ∈ support (execute table view remaining state),
      ∀ value left final, result = some (value, left, final) →
        Safe table final.signedBottom final.exposed final.residual := by
  induction view generalizing remaining state with
  | done value =>
      intro result member output left final same
      simp only [execute, support_pure, Set.mem_singleton_iff] at member
      rw [member] at same
      cases Option.some.inj same
      exact initial
  | coin n next ih =>
      intro result member output left final same
      simp only [execute, mem_support_bind_iff] at member
      obtain ⟨answer, _, child⟩ := member
      exact ih answer remaining state initial result child output left final same
  | sign index next ih =>
      intro result member output left final same
      simp only [execute] at member
      exact ih (table (.inr (.inl index))) remaining
        (signed state index (table (.inr (.inl index))))
        (GroupedBalancedGraphSignExposure67.safe_reveal_bottom
          table state.signedBottom state.exposed state.residual initial index)
        result member output left final same
  | privateHash input outside next ih =>
      intro result member output left final same
      cases present : state.residual input with
      | some answer =>
          simp only [execute, present] at member
          exact ih answer remaining state initial result member output left final same
      | none =>
          simp only [execute, present, mem_support_bind_iff] at member
          obtain ⟨answer, _, child⟩ := member
          have residualSafe : ResidualSafe table
              (state.residual.cacheQuery input answer) := by
            apply GroupedBalancedGraphMonitorInvariant67.ResidualSafe.cacheQuery
              table state.residual initial.2.2 input answer
            intro position located
            rw [outside] at located
            cases located
          exact ih answer remaining (privateOpened state input answer)
            ⟨initial.1, initial.2.1, residualSafe⟩
            result child output left final same
  | hash input next ih =>
      intro result member output left final same
      cases remaining with
      | zero =>
          simp only [execute, support_pure, Set.mem_singleton_iff] at member
          rw [member] at same
          cases Option.some.inj same
          exact initial
      | succ remaining =>
          simp only [execute] at member
          by_cases first : GroupedBalancedGraphMonitorPublicCoupling67.inputHit
              table state.exposed input
          · simp only [if_pos first, support_pure,
              Set.mem_singleton_iff] at member
            rw [member] at same
            cases same
          · rw [if_neg first, mem_support_bind_iff] at member
            obtain ⟨answer, queried, child⟩ := member
            by_cases second : GroupedBalancedGraphMonitorPublicCoupling67.outputHit
                table input answer.1
            · simp only [if_pos second, support_pure,
                Set.mem_singleton_iff] at child
              rw [child] at same
              cases same
            · rw [if_neg second] at child
              have queriedState :=
                GroupedBalancedGraphMonitorCompileCoupling67.read_supported
                  table state.signedBottom state.exposed state.residual initial
                  input answer queried first second
              have nextSafe :=
                GroupedBalancedGraphMonitorPublicUnified67.public_read_safe
                  table state.signedBottom state.exposed state.residual initial
                  input
                  (answer.1,
                    GroupedBalancedGraphMonitorPublicCoupling67.opened
                      table state.exposed input,
                    answer.2) queriedState
              exact ih answer.1 remaining
                (opened state
                  (GroupedBalancedGraphMonitorPublicCoupling67.opened
                    table state.exposed input) answer.2)
                nextSafe result child output left final same

theorem stopped_limited_safe {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (initial : Safe table state.signedBottom state.exposed state.residual)
    (value : Option α) (left : Nat) (final : State)
    (member : some (value, left, final) ∈ support
      (GroupedBalancedGraphMonitorStop67.stopped table state.exposed
        (GroupedBalancedGraphMonitorSignCompiler67.limited
          view remaining state))) :
    Safe table final.signedBottom final.exposed final.residual := by
  have executed :=
    (mem_support_iff_of_evalSPMF_eq
      (GroupedBalancedGraphMonitorSignCoupling67.stopped_execute
        table view remaining state initial)
      (some (value, left, final))).mp member
  exact execute_safe table view remaining state initial
    _ executed value left final rfl

theorem run_limited_safe {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (initial : Safe table state.signedBottom state.exposed state.residual)
    (result : GroupedBalancedGraphMonitorProgram67.Outcome
      (Option α × Nat × State))
    (member : result ∈ support
      (GroupedBalancedGraphMonitorProgram67.run table state.exposed
        (GroupedBalancedGraphMonitorSignCompiler67.limited
          view remaining state)))
    (clean : result.bad = false) :
    Safe table result.value.2.2.signedBottom
      result.value.2.2.exposed result.value.2.2.residual := by
  apply stopped_limited_safe table view remaining state initial
    result.value.1 result.value.2.1 result.value.2.2
  apply (mem_support_iff_of_evalSPMF_eq
    (GroupedBalancedGraphMonitorStop67.stopped_eq table state.exposed _) _).mpr
  rw [support_map]
  exact ⟨result, member,
    by simp only [GroupedBalancedGraphMonitorStop67.keep, clean,
      Bool.false_eq_true, if_false]⟩

theorem run_metered_safe {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (calls : Nat)
    (initial : Safe table state.signedBottom state.exposed state.residual)
    (result : GroupedBalancedGraphMonitorProgram67.Outcome
      (GroupedBalancedGraphMetered67.Result α))
    (member : result ∈ support
      (GroupedBalancedGraphMonitorProgram67.run table state.exposed
        (GroupedBalancedGraphMetered67.limited
          view remaining state calls)))
    (clean : result.bad = false) :
    Safe table result.value.state.signedBottom
      result.value.state.exposed result.value.state.residual := by
  have mapped : GroupedBalancedGraphProgramMap67.mapOutcome
      GroupedBalancedGraphMeteredErase67.drop result ∈ support
        (GroupedBalancedGraphMonitorProgram67.run table state.exposed
          (GroupedBalancedGraphMonitorSignCompiler67.limited
            view remaining state)) := by
    rw [← GroupedBalancedGraphMeteredErase67.map_limited view remaining state calls]
    rw [GroupedBalancedGraphProgramMap67.run_map, support_map]
    exact ⟨result, member, rfl⟩
  exact run_limited_safe table view remaining state initial
    (GroupedBalancedGraphProgramMap67.mapOutcome
      GroupedBalancedGraphMeteredErase67.drop result)
    mapped clean

#print axioms execute_safe
#print axioms run_limited_safe
#print axioms run_metered_safe

end SigGolfCandidate.Hypertree.GroupedBalancedStoppedStateSafe67
