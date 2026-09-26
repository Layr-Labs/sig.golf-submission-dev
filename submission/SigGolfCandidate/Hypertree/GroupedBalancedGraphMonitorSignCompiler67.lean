import SigGolfCandidate.Hypertree.GroupedBalancedGraphSignExposure67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCompile67

/-! An adaptive public-oracle interaction with an abstract, stronger signing
action. A signing action chooses a full index, reveals its entire 256-bit
bottom source, and records the index. This grants at least the information
contained in the honest 128-bit bottom seed and lets future choices depend on
all earlier answers. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSignCompiler67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorCredit67
open GroupedBalancedGraphSignExposure67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

inductive View (α : Type) where
  | done (value : α)
  | hash (query : Query) (next : BitVec 256 → View α)
  | privateHash (query : Query)
      (outside : GroupedBalancedGraphQuery67.locate query = none)
      (next : BitVec 256 → View α)
  | sign (index : BitVec 160) (next : BitVec 256 → View α)
  | coin (n : Nat) (next : Fin (n + 1) → View α)

structure State where
  signedBottom : Finset (BitVec 160)
  exposed : QueryCache PointSpec
  residual : QueryCache HashSpec

def signed (state : State) (index : BitVec 160) (answer : BitVec 256) : State :=
  { state with
    signedBottom := insert index state.signedBottom
    exposed := state.exposed.cacheQuery (.inr (.inl index)) answer }

def opened (state : State) (exposed : QueryCache PointSpec)
    (residual : QueryCache HashSpec) : State :=
  { state with exposed := exposed, residual := residual }

def privateOpened (state : State) (query : Query)
    (answer : BitVec 256) : State :=
  { state with residual := state.residual.cacheQuery query answer }

noncomputable def limited {α : Type} : View α →
    Nat → State → Program (Option α × Nat × State)
  | .done value, remaining, state => .done (some value, remaining, state)
  | .coin n next, remaining, state =>
      .coin n (fun answer => limited (next answer) remaining state)
  | .sign index next, remaining, state =>
      .reveal (.inr (.inl index)) (fun answer =>
        limited (next answer) remaining (signed state index answer))
  | .privateHash input _ next, remaining, state =>
      match state.residual input with
      | some answer => limited (next answer) remaining state
      | none => .bits (fun answer =>
          limited (next answer) remaining (privateOpened state input answer))
  | .hash input next, remaining, state =>
      match remaining with
      | 0 => .done (none, 0, state)
      | remaining + 1 =>
          GroupedBalancedGraphMonitorOracle67.publicStep
            state.exposed state.residual input
            (fun answer exposed residual =>
              limited (next answer) remaining (opened state exposed residual))

theorem limited_credit {α : Type} (view : View α)
    (remaining spent limit : Nat) (state : State)
    (bound : spent + 2 * remaining ≤ limit) :
    Credit (fun _ : Option α × Nat × State => limit) spent
      (limited view remaining state) := by
  induction view generalizing remaining spent limit state with
  | done value =>
      change spent ≤ limit
      omega
  | coin n next ih =>
      exact fun answer => ih answer remaining spent limit state bound
  | sign index next ih =>
      exact fun answer => ih answer remaining spent limit
        (signed state index answer) bound
  | privateHash input outside next ih =>
      cases present : state.residual input with
      | some answer =>
          simp only [limited, present]
          exact ih answer remaining spent limit state bound
      | none =>
          simp only [limited, present]
          exact fun answer => ih answer remaining spent limit
            (privateOpened state input answer) bound
  | hash input next ih =>
      cases remaining with
      | zero =>
          change spent ≤ limit
          omega
      | succ remaining =>
          change Credit (fun _ : Option α × Nat × State => limit) spent
            (GroupedBalancedGraphMonitorOracle67.publicStep
              state.exposed state.residual input
              (fun answer exposed residual =>
                limited (next answer) remaining (opened state exposed residual)))
          apply GroupedBalancedGraphMonitorCredit67.publicStep_credit
          intro answer exposed residual
          exact ih answer remaining (spent + 2) limit
            (opened state exposed residual) (by omega)

theorem limited_within {α : Type} (view : View α)
    (remaining : Nat) (state : State) :
    Within (2 * remaining) (erase (limited view remaining state)) := by
  simpa only [Nat.sub_zero] using
    GroupedBalancedGraphMonitorCompile67.credit_within
      (limited view remaining state) 0 (2 * remaining)
      (limited_credit view remaining 0 (2 * remaining) state (by omega))

theorem limited_bad_le {α : Type} (view : View α)
    (remaining : Nat) (state : State) :
    Pr[fun result => result.bad = true |
      experiment (limited view remaining state) state.exposed] ≤
      (2 * remaining : Nat) / (2 : ENNReal) ^ 128 := by
  have bound := prob_playAll_le (limited_within view remaining state)
    state.exposed
  change Pr[fun hit => hit = true |
    GroupedBalancedGraphPassiveCost67.fullExperiment
      (erase (limited view remaining state)) state.exposed] ≤ _ at bound
  rw [← experiment_bad, probEvent_map] at bound
  exact bound

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSignCompiler67
