import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCredit67

/-! A finite public-oracle compiler for the direct 67-chain monitor. The
continuation sees the actual public answer and both caches, while passive
contact flags remain unavailable to it. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCompile67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorCredit67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev State := QueryCache PointSpec × QueryCache HashSpec

noncomputable def compile {α : Type} (program : OracleComp World α) :
    State → Program (α × State) :=
  OracleComp.construct
    (fun value state => .done (value, state))
    (fun query _ next state => match query with
      | .inl n => .coin n (fun answer => next answer state)
      | .inr input => GroupedBalancedGraphMonitorOracle67.publicStep
          state.1 state.2 input
          (fun answer exposed residual => next answer (exposed, residual))) program

@[simp] theorem compile_pure {α : Type} (value : α) (state : State) :
    compile (pure value) state = .done (value, state) := rfl

@[simp] theorem compile_hash {α : Type} (query : Query)
    (next : BitVec 256 → OracleComp World α) (state : State) :
    compile (liftM (World.query (.inr query)) >>= next) state =
      GroupedBalancedGraphMonitorOracle67.publicStep state.1 state.2 query
        (fun answer exposed residual => compile (next answer) (exposed, residual)) := rfl

@[simp] theorem compile_coin {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp World α) (state : State) :
    compile (liftM (World.query (.inl n)) >>= next) state =
      .coin n (fun answer => compile (next answer) state) := rfl

noncomputable def limited {α : Type} (program : OracleComp World α) :
    Nat → State → Program (Option α × Nat × State) :=
  OracleComp.construct
    (fun value remaining state => .done (some value, remaining, state))
    (fun query _ next remaining state => match query with
      | .inl n => .coin n (fun answer => next answer remaining state)
      | .inr input => match remaining with
        | 0 => .done (none, 0, state)
        | remaining + 1 => GroupedBalancedGraphMonitorOracle67.publicStep
            state.1 state.2 input
            (fun answer exposed residual => next answer remaining (exposed, residual))) program

/-- The passive ledger charges at most two tests for each actual public hash
call, along every adaptive path of the compiled computation. -/
theorem limited_credit {α : Type} (program : OracleComp World α)
    (remaining spent limit : Nat) (state : State)
    (bound : spent + 2 * remaining ≤ limit) :
    Credit (fun _ : Option α × Nat × State => limit) spent
      (limited program remaining state) := by
  induction program using OracleComp.inductionOn generalizing remaining spent limit state with
  | pure value =>
      change spent ≤ limit
      omega
  | query_bind query next ih =>
    cases query with
    | inl n =>
        exact fun answer => ih answer remaining spent limit state bound
    | inr input =>
        cases remaining with
        | zero =>
            change spent ≤ limit
            omega
        | succ remaining =>
            change Credit (fun _ : Option α × Nat × State => limit) spent
              (GroupedBalancedGraphMonitorOracle67.publicStep state.1 state.2 input
                (fun answer exposed residual =>
                  limited (next answer) remaining (exposed, residual)))
            apply publicStep_credit
            intro answer exposed residual
            exact ih answer remaining (spent + 2) limit (exposed, residual) (by omega)

theorem credit_spent {α : Type} (program : Program α)
    (spent limit : Nat) (credit : Credit (fun _ : α => limit) spent program) :
    spent ≤ limit := by
  induction program generalizing spent with
  | done value => exact credit
  | reveal point next ih | bits next ih =>
      exact (ih 0 spent (credit 0))
  | coin n next ih =>
      exact ih 0 spent (credit 0)
  | guess point value next ih =>
      have later := ih (spent + 1) credit
      omega
  | collision target next ih =>
      have later := ih 0 (spent + 1) (credit 0)
      omega

/-- Any pathwise constant allowance supplies the structural passive test cap
needed by the uniform guessing theorem. -/
theorem credit_within {α : Type} (program : Program α)
    (spent limit : Nat) (credit : Credit (fun _ : α => limit) spent program) :
    Within (limit - spent) (erase program) := by
  induction program generalizing spent with
  | done value => exact Within.done _
  | reveal point next ih =>
      exact Within.reveal (fun answer => ih answer spent (credit answer))
  | coin n next ih =>
      exact Within.coin (fun answer => ih answer spent (credit answer))
  | bits next ih =>
      exact Within.bits (fun answer => ih answer spent (credit answer))
  | guess point value next ih =>
      have room : spent + 1 ≤ limit := credit_spent next (spent + 1) limit credit
      have size : limit - spent = (limit - (spent + 1)) + 1 := by omega
      rw [size]
      exact Within.guess (ih (spent + 1) credit)
  | collision target next ih =>
      have room : spent + 1 ≤ limit := credit_spent (next 0) (spent + 1) limit (credit 0)
      have size : limit - spent = (limit - (spent + 1)) + 1 := by omega
      rw [size]
      exact Within.collision (fun answer => ih answer (spent + 1) (credit answer))

theorem limited_within {α : Type} (program : OracleComp World α)
    (remaining : Nat) (state : State) :
    Within (2 * remaining) (erase (limited program remaining state)) := by
  simpa only [Nat.sub_zero] using
    credit_within (limited program remaining state) 0 (2 * remaining)
      (limited_credit program remaining 0 (2 * remaining) state (by omega))

theorem limited_bad_le {α : Type} (program : OracleComp World α)
    (remaining : Nat) (state : State) :
    Pr[fun result => result.bad = true |
      experiment (limited program remaining state) state.1] ≤
      (2 * remaining : Nat) / (2 : ENNReal) ^ 128 := by
  have bound := prob_playAll_le (limited_within program remaining state) state.1
  change Pr[fun hit => hit = true |
    GroupedBalancedGraphPassiveCost67.fullExperiment
      (erase (limited program remaining state)) state.1] ≤ _ at bound
  rw [← experiment_bad, probEvent_map] at bound
  exact bound

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCompile67
