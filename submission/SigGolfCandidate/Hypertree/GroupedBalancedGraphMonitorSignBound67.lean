import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSignCoupling67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSetupBound67

/-! The keyed adaptive signing view has the same two-tests-per-public-hash
contact bound. It may choose and reveal bottom sources during the run, and it
may adapt every later query and signing index to prior answers. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSignBound67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorCredit67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphMonitorSignCoupling67
open GroupedBalancedGraphMonitorSetup67
open GroupedBalancedGraphMonitorSetupBound67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

def initial (exposed : QueryCache PointSpec) : State :=
  ⟨∅, exposed, ∅⟩

noncomputable def monitoredKeyed {α : Type}
    (view : Reference.Digest → View α)
    (remaining : Nat) : Program (Option α × Nat × State) :=
  setup (fun exposed => limited (view (rootFrom exposed))
    remaining (initial exposed))

theorem monitoredKeyed_credit {α : Type}
    (view : Reference.Digest → View α)
    (remaining : Nat) :
    Credit (fun _ : Option α × Nat × State => 2 * remaining) 0
      (monitoredKeyed view remaining) := by
  unfold monitoredKeyed setup
  apply disclose_credit
  intro metadata
  apply disclose_credit
  intro exposed
  exact limited_credit (view (rootFrom exposed)) remaining 0
    (2 * remaining) (initial exposed) (by omega)

theorem monitoredKeyed_within {α : Type}
    (view : Reference.Digest → View α)
    (remaining : Nat) :
    Within (2 * remaining) (erase (monitoredKeyed view remaining)) := by
  simpa only [Nat.sub_zero] using
    GroupedBalancedGraphMonitorCompile67.credit_within
      (monitoredKeyed view remaining) 0 (2 * remaining)
      (monitoredKeyed_credit view remaining)

theorem monitoredKeyed_bad_le {α : Type}
    (view : Reference.Digest → View α)
    (remaining : Nat) :
    Pr[fun result => result.bad = true |
      experiment (monitoredKeyed view remaining) ∅] ≤
      (2 * remaining : Nat) / (2 : ENNReal) ^ 128 := by
  have bound := prob_playAll_le (monitoredKeyed_within view remaining) ∅
  change Pr[fun hit => hit = true |
    GroupedBalancedGraphPassiveCost67.fullExperiment
      (erase (monitoredKeyed view remaining)) ∅] ≤ _ at bound
  rw [← experiment_bad, probEvent_map] at bound
  exact bound

theorem planted_keyed_sign_contact_le {α : Type}
    (view : Reference.Digest → View α) (remaining : Nat) :
    Pr[= none | do
      let table ← $ᵗ PointTable
      execute table (view (rootPublic table)) remaining
        (initial (cache table))] ≤
      (2 * remaining : Nat) / (2 : ENNReal) ^ 128 := by
  have dist :
      𝒮[do
        let table ← $ᵗ PointTable
        execute table (view (rootPublic table)) remaining
          (initial (cache table))] =
      𝒮[do
        let table ← $ᵗ PointTable
        GroupedBalancedGraphMonitorStop67.stopped table ∅
          (monitoredKeyed view remaining)] := by
    apply evalSPMF_bind_congr
    intro table _
    calc
      _ = 𝒮[GroupedBalancedGraphMonitorStop67.stopped table
            (cache table)
            (limited (view (rootPublic table)) remaining
              (initial (cache table)))] :=
          (stopped_execute table (view (rootPublic table)) remaining
            (initial (cache table)) (cache_safe table)).symm
      _ = _ := by
        rw [← rootFrom_cache table]
        simpa only [monitoredKeyed] using congrArg (fun p => 𝒮[p])
          (stopped_setup table
            (fun exposed => limited (view (rootFrom exposed))
              remaining (initial exposed))).symm
  have emptyComplete (table : PointTable) :
      complete (∅ : QueryCache PointSpec) table = table := by
    funext point
    simp [complete]
  calc
    _ = Pr[= none | do
          let table ← $ᵗ PointTable
          GroupedBalancedGraphMonitorStop67.stopped table ∅
            (monitoredKeyed view remaining)] := by
          simp only [probOutput_def]
          exact congrArg (fun distribution => distribution none) dist
    _ = Pr[fun result => result.bad = true |
          experiment (monitoredKeyed view remaining) ∅] := by
          rw [← GroupedBalancedGraphMonitorCompileCoupling67.stopped_experiment_none]
          simp only [emptyComplete]
    _ ≤ _ := monitoredKeyed_bad_le view remaining

noncomputable def monitoredFromCache {α : Type}
    (view : QueryCache PointSpec → View α)
    (remaining : Nat) : Program (Option α × Nat × State) :=
  setup (fun exposed => limited (view exposed)
    remaining (initial exposed))

theorem monitoredFromCache_credit {α : Type}
    (view : QueryCache PointSpec → View α)
    (remaining : Nat) :
    Credit (fun _ : Option α × Nat × State => 2 * remaining) 0
      (monitoredFromCache view remaining) := by
  unfold monitoredFromCache setup
  apply disclose_credit
  intro metadata
  apply disclose_credit
  intro exposed
  exact limited_credit (view exposed) remaining 0
    (2 * remaining) (initial exposed) (by omega)

theorem monitoredFromCache_bad_le {α : Type}
    (view : QueryCache PointSpec → View α)
    (remaining : Nat) :
    Pr[fun result => result.bad = true |
      experiment (monitoredFromCache view remaining) ∅] ≤
      (2 * remaining : Nat) / (2 : ENNReal) ^ 128 := by
  have within : Within (2 * remaining)
      (erase (monitoredFromCache view remaining)) := by
    simpa only [Nat.sub_zero] using
      GroupedBalancedGraphMonitorCompile67.credit_within
        (monitoredFromCache view remaining) 0 (2 * remaining)
        (monitoredFromCache_credit view remaining)
  have bound := prob_playAll_le within ∅
  change Pr[fun hit => hit = true |
    GroupedBalancedGraphPassiveCost67.fullExperiment
      (erase (monitoredFromCache view remaining)) ∅] ≤ _ at bound
  rw [← experiment_bad, probEvent_map] at bound
  exact bound

theorem planted_from_cache_contact_le {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    Pr[= none | do
      let table ← $ᵗ PointTable
      execute table (view (cache table)) remaining
        (initial (cache table))] ≤
      (2 * remaining : Nat) / (2 : ENNReal) ^ 128 := by
  have dist :
      𝒮[do
        let table ← $ᵗ PointTable
        execute table (view (cache table)) remaining
          (initial (cache table))] =
      𝒮[do
        let table ← $ᵗ PointTable
        GroupedBalancedGraphMonitorStop67.stopped table ∅
          (monitoredFromCache view remaining)] := by
    apply evalSPMF_bind_congr
    intro table _
    calc
      _ = 𝒮[GroupedBalancedGraphMonitorStop67.stopped table
            (cache table)
            (limited (view (cache table)) remaining
              (initial (cache table)))] :=
          (stopped_execute table (view (cache table)) remaining
            (initial (cache table)) (cache_safe table)).symm
      _ = _ := by
        simpa only [monitoredFromCache] using congrArg (fun p => 𝒮[p])
          (stopped_setup table
            (fun exposed => limited (view exposed)
              remaining (initial exposed))).symm
  have emptyComplete (table : PointTable) :
      complete (∅ : QueryCache PointSpec) table = table := by
    funext point
    simp [complete]
  calc
    _ = Pr[= none | do
          let table ← $ᵗ PointTable
          GroupedBalancedGraphMonitorStop67.stopped table ∅
            (monitoredFromCache view remaining)] := by
          simp only [probOutput_def]
          exact congrArg (fun distribution => distribution none) dist
    _ = Pr[fun result => result.bad = true |
          experiment (monitoredFromCache view remaining) ∅] := by
          rw [← GroupedBalancedGraphMonitorCompileCoupling67.stopped_experiment_none]
          simp only [emptyComplete]
    _ ≤ _ := monitoredFromCache_bad_le view remaining

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSignBound67
