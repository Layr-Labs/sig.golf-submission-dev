import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCompile67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCompose67

/-! The stopped direct67 compiler follows the actual planted public graph
oracle, preserving its answer and both caches until the first contact. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCompileCoupling67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorStop67 GroupedBalancedGraphMonitorInvariant67
open GroupedBalancedGraphMonitorPublicCoupling67
open GroupedBalancedGraphMonitorCompile67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

noncomputable def execute {α : Type} (table : PointTable)
    (program : OracleComp World α) :
    Nat → State → ProbComp (Option (Option α × Nat × State)) :=
  OracleComp.construct
    (fun value remaining state => pure (some (some value, remaining, state)))
    (fun query _ next remaining state => match query with
      | .inl n => do
          let answer ← $ᵗ Fin (n + 1)
          next answer remaining state
      | .inr input => match remaining with
        | 0 => pure (some (none, 0, state))
        | remaining + 1 =>
            if inputHit table state.1 input then pure none else do
              let result ← (GroupedBalancedGraphOracle67.publicOracle
                (GroupedBalancedGraphMonitorTable67.privateOf table)
                (GroupedBalancedGraphMonitorTable67.labelsOf table) input).run state.2
              if outputHit table input result.1 then pure none else
                next result.1 remaining (opened table state.1 input, result.2)) program

theorem read_supported (table : PointTable)
    (signedBottom : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (safe : Safe table signedBottom exposed cache) (query : Query)
    (result : BitVec 256 × QueryCache HashSpec)
    (member : result ∈ support ((GroupedBalancedGraphOracle67.publicOracle
      (GroupedBalancedGraphMonitorTable67.privateOf table)
      (GroupedBalancedGraphMonitorTable67.labelsOf table) query).run cache))
    (first : ¬inputHit table exposed query)
    (second : ¬outputHit table query result.1) :
    some (result.1, opened table exposed query, result.2) ∈
      support (stopped table exposed
        (GroupedBalancedGraphMonitorOracle67.publicStep exposed cache query
          (fun answer opened residual => .done (answer, opened, residual)))) := by
  rw [stopped_public_oracle table exposed cache query _ safe.1 safe.2.2,
    if_neg first, mem_support_bind_iff]
  refine ⟨result, member, ?_⟩
  simp only [if_neg second, stopped, support_pure, Set.mem_singleton_iff]

/-- The cutoff compiler is an exact coupling to the planted graph oracle up to
the first hidden-predecessor or output contact. Both caches remain in the
returned state, and the safety invariant is propagated along every supported
contact-free query. -/
theorem stopped_execute {α : Type} (table : PointTable)
    (signedBottom : Finset (BitVec 160))
    (program : OracleComp World α) (remaining : Nat) (state : State)
    (safe : Safe table signedBottom state.1 state.2) :
    𝒮[stopped table state.1 (limited program remaining state)] =
      𝒮[execute table program remaining state] := by
  induction program using OracleComp.inductionOn generalizing remaining state with
  | pure value => rfl
  | query_bind query next ih =>
      cases query with
      | inl n =>
          simp only [limited, execute, stopped]
          apply evalSPMF_bind_congr
          intro answer _
          exact ih answer remaining state safe
      | inr input =>
          cases remaining with
          | zero => rfl
          | succ remaining =>
              change 𝒮[stopped table state.1
                (GroupedBalancedGraphMonitorOracle67.publicStep state.1 state.2 input
                  (fun answer exposed residual =>
                    limited (next answer) remaining (exposed, residual)))] =
                𝒮[if inputHit table state.1 input then pure none else
                  ((GroupedBalancedGraphOracle67.publicOracle
                    (GroupedBalancedGraphMonitorTable67.privateOf table)
                    (GroupedBalancedGraphMonitorTable67.labelsOf table) input).run state.2 >>=
                    fun result =>
                      if outputHit table input result.1 then pure none else
                        execute table (next result.1) remaining
                          (opened table state.1 input, result.2))]
              rw [stopped_public_oracle table state.1 state.2 input _
                safe.1 safe.2.2]
              by_cases first : inputHit table state.1 input
              · simp only [if_pos first]
              · simp only [if_neg first]
                apply evalSPMF_bind_congr
                intro result member
                by_cases second : outputHit table input result.1
                · simp only [if_pos second]
                · simp only [if_neg second]
                  have queried := read_supported table signedBottom state.1
                    state.2 safe input result member first second
                  have nextSafe :=
                    GroupedBalancedGraphMonitorPublicUnified67.public_read_safe
                      table signedBottom state.1 state.2 safe input
                      (result.1, opened table state.1 input, result.2) queried
                  exact ih result.1 remaining
                    (opened table state.1 input, result.2) nextSafe

theorem stopped_experiment_none {α : Type} (program : Program α)
    (cache : QueryCache PointSpec) :
    Pr[= none | do
      let table ← $ᵗ PointTable
      stopped (complete cache table) cache program] =
    Pr[fun result => result.bad = true |
      GroupedBalancedGraphMonitorProgram67.experiment program cache] := by
  unfold GroupedBalancedGraphMonitorProgram67.experiment
  change Pr[= none | ($ᵗ PointTable) >>= fun table =>
      stopped (complete cache table) cache program] =
    Pr[fun result => result.bad = true | ($ᵗ PointTable) >>= fun table =>
      run (complete cache table) cache program]
  rw [probOutput_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro table
  rw [stopped_none]

theorem stopped_limited_empty_le {α : Type}
    (program : OracleComp World α) (remaining : Nat) :
    Pr[= none | do
      let table ← $ᵗ PointTable
      stopped table ∅ (limited program remaining (∅, ∅))] ≤
      (2 * remaining : Nat) / (2 : ENNReal) ^ 128 := by
  have emptyComplete (table : PointTable) :
      complete (∅ : QueryCache PointSpec) table = table := by
    funext point
    simp [complete]
  calc
    _ = Pr[fun result => result.bad = true |
          GroupedBalancedGraphMonitorProgram67.experiment
            (limited program remaining (∅, ∅)) ∅] := by
          rw [← stopped_experiment_none]
          simp only [emptyComplete]
    _ ≤ _ := limited_bad_le program remaining (∅, ∅)

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCompileCoupling67
