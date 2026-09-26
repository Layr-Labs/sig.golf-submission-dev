import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSignCompiler67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCompileCoupling67

/-! Exact stopped coupling for an adaptive interaction that interleaves public
hashes and honest-index source disclosures. A sign step changes the authorized
bottom set and reveals that source, with no contact test. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSignCoupling67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorStop67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphMonitorInvariant67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

noncomputable def execute {α : Type} (table : PointTable) :
    View α → Nat → State → ProbComp (Option (Option α × Nat × State))
  | .done value, remaining, state => pure (some (some value, remaining, state))
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
      | 0 => pure (some (none, 0, state))
      | remaining + 1 =>
          if GroupedBalancedGraphMonitorPublicCoupling67.inputHit
              table state.exposed input then pure none else do
            let result ← (GroupedBalancedGraphOracle67.publicOracle
              (GroupedBalancedGraphMonitorTable67.privateOf table)
              (GroupedBalancedGraphMonitorTable67.labelsOf table) input).run
                state.residual
            if GroupedBalancedGraphMonitorPublicCoupling67.outputHit
                table input result.1 then pure none else
              execute table (next result.1) remaining
                (opened state
                  (GroupedBalancedGraphMonitorPublicCoupling67.opened
                    table state.exposed input) result.2)

theorem stopped_execute {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (safe : Safe table state.signedBottom state.exposed state.residual) :
    𝒮[stopped table state.exposed (limited view remaining state)] =
      𝒮[execute table view remaining state] := by
  induction view generalizing remaining state with
  | done value => rfl
  | coin n next ih =>
      simp only [limited, execute, stopped]
      apply evalSPMF_bind_congr
      intro answer _
      exact ih answer remaining state safe
  | sign index next ih =>
      change 𝒮[stopped table
          (state.exposed.cacheQuery (.inr (.inl index))
            (table (.inr (.inl index))))
          (limited (next (table (.inr (.inl index)))) remaining
            (signed state index (table (.inr (.inl index)))))] =
        𝒮[execute table (next (table (.inr (.inl index)))) remaining
          (signed state index (table (.inr (.inl index))))]
      exact ih (table (.inr (.inl index))) remaining
        (signed state index (table (.inr (.inl index))))
        (GroupedBalancedGraphSignExposure67.safe_reveal_bottom
          table state.signedBottom state.exposed state.residual safe index)
  | privateHash input outside next ih =>
      cases present : state.residual input with
      | some answer =>
          simp only [limited, execute, present]
          exact ih answer remaining state safe
      | none =>
          simp only [limited, execute, present, stopped]
          apply evalSPMF_bind_congr
          intro answer _
          have residualSafe : ResidualSafe table
              (state.residual.cacheQuery input answer) := by
            apply GroupedBalancedGraphMonitorInvariant67.ResidualSafe.cacheQuery
              table state.residual safe.2.2 input answer
            intro position located
            rw [outside] at located
            cases located
          exact ih answer remaining (privateOpened state input answer)
            ⟨safe.1, safe.2.1, residualSafe⟩
  | hash input next ih =>
      cases remaining with
      | zero => rfl
      | succ remaining =>
          change 𝒮[stopped table state.exposed
            (GroupedBalancedGraphMonitorOracle67.publicStep
              state.exposed state.residual input
              (fun answer exposed residual =>
                limited (next answer) remaining (opened state exposed residual)))] =
            𝒮[if GroupedBalancedGraphMonitorPublicCoupling67.inputHit
                table state.exposed input then pure none else
              ((GroupedBalancedGraphOracle67.publicOracle
                (GroupedBalancedGraphMonitorTable67.privateOf table)
                (GroupedBalancedGraphMonitorTable67.labelsOf table) input).run
                  state.residual >>= fun result =>
                if GroupedBalancedGraphMonitorPublicCoupling67.outputHit
                    table input result.1 then pure none else
                  execute table (next result.1) remaining
                    (opened state
                      (GroupedBalancedGraphMonitorPublicCoupling67.opened
                        table state.exposed input) result.2))]
          rw [GroupedBalancedGraphMonitorPublicCoupling67.stopped_public_oracle
            table state.exposed state.residual input _ safe.1 safe.2.2]
          by_cases first : GroupedBalancedGraphMonitorPublicCoupling67.inputHit
              table state.exposed input
          · simp only [if_pos first]
          · simp only [if_neg first]
            apply evalSPMF_bind_congr
            intro result member
            by_cases second : GroupedBalancedGraphMonitorPublicCoupling67.outputHit
                table input result.1
            · simp only [if_pos second]
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
              exact ih result.1 remaining
                (opened state
                  (GroupedBalancedGraphMonitorPublicCoupling67.opened
                    table state.exposed input) result.2) nextSafe

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSignCoupling67
