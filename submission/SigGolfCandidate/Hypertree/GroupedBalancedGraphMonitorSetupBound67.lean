import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSetup67

/-! A public-only adaptive graph view, including its value-dependent initial
frontier, pays at most two passive tests per public hash query. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSetupBound67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorCredit67 GroupedBalancedGraphMonitorCompile67
open GroupedBalancedGraphMonitorCompileCoupling67
open GroupedBalancedGraphMonitorSetup67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

noncomputable def monitored {α : Type} (program : OracleComp World α)
    (remaining : Nat) : Program (Option α × Nat × State) :=
  setup (fun exposed => limited program remaining (exposed, ∅))

theorem monitored_credit {α : Type} (program : OracleComp World α)
    (remaining : Nat) :
    Credit (fun _ : Option α × Nat × State => 2 * remaining) 0
      (monitored program remaining) := by
  unfold monitored setup
  apply disclose_credit
  intro metadata
  apply disclose_credit
  intro exposed
  exact limited_credit program remaining 0 (2 * remaining)
    (exposed, ∅) (by omega)

theorem monitored_within {α : Type} (program : OracleComp World α)
    (remaining : Nat) :
    Within (2 * remaining) (erase (monitored program remaining)) := by
  simpa only [Nat.sub_zero] using
    credit_within (monitored program remaining) 0 (2 * remaining)
      (monitored_credit program remaining)

theorem monitored_bad_le {α : Type} (program : OracleComp World α)
    (remaining : Nat) :
    Pr[fun result => result.bad = true |
      GroupedBalancedGraphMonitorProgram67.experiment
        (monitored program remaining) ∅] ≤
      (2 * remaining : Nat) / (2 : ENNReal) ^ 128 := by
  have bound := prob_playAll_le (monitored_within program remaining) ∅
  change Pr[fun hit => hit = true |
    GroupedBalancedGraphPassiveCost67.fullExperiment
      (erase (monitored program remaining)) ∅] ≤ _ at bound
  rw [← experiment_bad, probEvent_map] at bound
  exact bound

/-- The same bound applies to the stopped planted-graph oracle after the
initial tree-node and WOTS frontier disclosures. -/
theorem planted_public_contact_le {α : Type}
    (program : OracleComp World α) (remaining : Nat) :
    Pr[= none | do
      let table ← $ᵗ PointTable
      execute table program remaining (cache table, ∅)] ≤
      (2 * remaining : Nat) / (2 : ENNReal) ^ 128 := by
  have dist :
      𝒮[do
        let table ← $ᵗ PointTable
        execute table program remaining (cache table, ∅)] =
      𝒮[do
        let table ← $ᵗ PointTable
        GroupedBalancedGraphMonitorStop67.stopped table ∅
          (monitored program remaining)] := by
    apply evalSPMF_bind_congr
    intro table _
    calc
      _ = 𝒮[GroupedBalancedGraphMonitorStop67.stopped table
            (cache table) (limited program remaining (cache table, ∅))] :=
          (stopped_execute table ∅ program remaining
            (cache table, ∅) (cache_safe table)).symm
      _ = _ := by
        simpa only [monitored] using congrArg (fun program => 𝒮[program])
          (stopped_setup table
            (fun exposed => limited program remaining (exposed, ∅))).symm
  have emptyComplete (table : PointTable) :
      complete (∅ : QueryCache PointSpec) table = table := by
    funext point
    simp [complete]
  calc
    _ = Pr[= none | do
          let table ← $ᵗ PointTable
          GroupedBalancedGraphMonitorStop67.stopped table ∅
            (monitored program remaining)] := by
          simp only [probOutput_def]
          exact congrArg (fun distribution => distribution none) dist
    _ = Pr[fun result => result.bad = true |
          GroupedBalancedGraphMonitorProgram67.experiment
            (monitored program remaining) ∅] := by
          rw [← stopped_experiment_none]
          simp only [emptyComplete]
    _ ≤ _ := monitored_bad_le program remaining

def rootPoint : Point :=
  .inl (GroupedBalancedSecurityGraph67.upperNode ⟨149, by decide⟩ 0)

def rootPublic (table : PointTable) : Reference.Digest :=
  truncate (table rootPoint)

def rootFrom (exposed : QueryCache PointSpec) : Reference.Digest :=
  truncate ((exposed rootPoint).getD 0)

theorem rootFrom_cache (table : PointTable) :
    rootFrom (cache table) = rootPublic table := by
  have covered := cache_covers table rootPoint
    (node_authorized (GroupedBalancedGraphMonitorTable67.labelsOf table)
      ∅ (GroupedBalancedSecurityGraph67.upperNode ⟨149, by decide⟩ 0) rfl)
  simp [rootFrom, rootPublic, covered]

noncomputable def monitoredKeyed {α : Type}
    (program : Reference.Digest → OracleComp World α)
    (remaining : Nat) : Program (Option α × Nat × State) :=
  setup (fun exposed => limited (program (rootFrom exposed))
    remaining (exposed, ∅))

theorem monitoredKeyed_credit {α : Type}
    (program : Reference.Digest → OracleComp World α)
    (remaining : Nat) :
    Credit (fun _ : Option α × Nat × State => 2 * remaining) 0
      (monitoredKeyed program remaining) := by
  unfold monitoredKeyed setup
  apply disclose_credit
  intro metadata
  apply disclose_credit
  intro exposed
  exact limited_credit (program (rootFrom exposed)) remaining 0
    (2 * remaining) (exposed, ∅) (by omega)

theorem monitoredKeyed_bad_le {α : Type}
    (program : Reference.Digest → OracleComp World α)
    (remaining : Nat) :
    Pr[fun result => result.bad = true |
      GroupedBalancedGraphMonitorProgram67.experiment
        (monitoredKeyed program remaining) ∅] ≤
      (2 * remaining : Nat) / (2 : ENNReal) ^ 128 := by
  have within : Within (2 * remaining)
      (erase (monitoredKeyed program remaining)) := by
    simpa only [Nat.sub_zero] using
      credit_within (monitoredKeyed program remaining) 0
        (2 * remaining) (monitoredKeyed_credit program remaining)
  have bound := prob_playAll_le within ∅
  change Pr[fun hit => hit = true |
    GroupedBalancedGraphPassiveCost67.fullExperiment
      (erase (monitoredKeyed program remaining)) ∅] ≤ _ at bound
  rw [← experiment_bad, probEvent_map] at bound
  exact bound

/-- The adaptive public program may be chosen after seeing the actual keygen
root digest. That choice is made from disclosed setup data, so it does not
affect the passive contact bound. -/
theorem planted_keyed_contact_le {α : Type}
    (program : Reference.Digest → OracleComp World α)
    (remaining : Nat) :
    Pr[= none | do
      let table ← $ᵗ PointTable
      execute table (program (rootPublic table)) remaining
        (cache table, ∅)] ≤
      (2 * remaining : Nat) / (2 : ENNReal) ^ 128 := by
  have dist :
      𝒮[do
        let table ← $ᵗ PointTable
        execute table (program (rootPublic table)) remaining
          (cache table, ∅)] =
      𝒮[do
        let table ← $ᵗ PointTable
        GroupedBalancedGraphMonitorStop67.stopped table ∅
          (monitoredKeyed program remaining)] := by
    apply evalSPMF_bind_congr
    intro table _
    calc
      _ = 𝒮[GroupedBalancedGraphMonitorStop67.stopped table
            (cache table)
            (limited (program (rootPublic table)) remaining (cache table, ∅))] :=
          (stopped_execute table ∅ (program (rootPublic table)) remaining
            (cache table, ∅) (cache_safe table)).symm
      _ = _ := by
        rw [← rootFrom_cache table]
        simpa only [monitoredKeyed] using congrArg (fun p => 𝒮[p])
          (stopped_setup table
            (fun exposed => limited (program (rootFrom exposed))
              remaining (exposed, ∅))).symm
  have emptyComplete (table : PointTable) :
      complete (∅ : QueryCache PointSpec) table = table := by
    funext point
    simp [complete]
  calc
    _ = Pr[= none | do
          let table ← $ᵗ PointTable
          GroupedBalancedGraphMonitorStop67.stopped table ∅
            (monitoredKeyed program remaining)] := by
          simp only [probOutput_def]
          exact congrArg (fun distribution => distribution none) dist
    _ = Pr[fun result => result.bad = true |
          GroupedBalancedGraphMonitorProgram67.experiment
            (monitoredKeyed program remaining) ∅] := by
          rw [← stopped_experiment_none]
          simp only [emptyComplete]
    _ ≤ _ := monitoredKeyed_bad_le program remaining

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSetupBound67
