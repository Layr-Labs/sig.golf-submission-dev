import SigGolfCandidate.Hypertree.GroupedBalancedOrganizerFinalRisk67
import SigGolfCandidate.Hypertree.GroupedBalancedProgram67ByteSign
import SigGolfCandidate.Hypertree.GroupedBalancedSecurityCounterRisk67

/-! The remaining security boundary is a counted coupling from the submitted
four-program experiment to the planted direct67 graph experiment. The latter
already has a complete quantitative bound. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityConditional67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec
open GroupedBalancedGraphPassive67
open scoped Classical

private abbrev submission := GroupedBalancedProgram67ByteSign.submission

noncomputable def plantedExperiment
    (adversary : Adversary submission.sizes) (rounds : Nat) :
    ProbComp (GroupedBalancedGraphOrganizerView67.Result submission.sizes × Nat) := do
  let table ← $ᵗ PointTable
  let secretKey ← sampleSecretKey
  (simulateQ (SecurityGameHop.realGameOracle secretKey)
    (SecurityBudget.counted
      (GroupedBalancedGameWorldBudget67.organizerProgram
        submission.sizes GroupedBalancedWire67.wire
        GroupedBalancedWire67.decode GroupedBalancedWire67.decode
        adversary (0 : Cache) rounds table))).run'
      (GroupedBalancedPlantedCache67.planted table)

/-- A joint simulation must keep the winning bit and bound the graph-game
counter by the official hash-call counter on every corresponding outcome. -/
def CountedCoupling : Prop :=
  ∀ (adversary : Adversary submission.sizes) (rounds budget : Nat),
    Pr[fun result => result.won = true ∧ result.hashCalls ≤ budget |
      submission.securityExperiment adversary rounds] ≤
    Pr[fun result => result.1.won = true ∧ result.2 ≤ budget |
      plantedExperiment adversary rounds]

/-- A constructive way to establish `CountedCoupling`: a single joint
experiment retains both outcomes. Every real win maps to a graph win, and
the graph query count cannot exceed the official charged hash calls. -/
def JointCoupling : Prop :=
  ∀ (adversary : Adversary submission.sizes) (rounds : Nat),
    ∃ joint : ProbComp (AttackResult ×
        (GroupedBalancedGraphOrganizerView67.Result submission.sizes × Nat)),
      𝒮[Prod.fst <$> joint] =
        𝒮[submission.securityExperiment adversary rounds] ∧
      𝒮[Prod.snd <$> joint] =
        𝒮[plantedExperiment adversary rounds] ∧
      ∀ pair ∈ support joint, pair.1.won = true →
        pair.2.1.won = true ∧ pair.2.2 ≤ pair.1.hashCalls

theorem countedCoupling_of_joint (coupling : JointCoupling) :
    CountedCoupling := by
  intro adversary rounds budget
  obtain ⟨joint,left,right,preserves⟩ := coupling adversary rounds
  calc
    Pr[fun result => result.won = true ∧ result.hashCalls ≤ budget |
      submission.securityExperiment adversary rounds] =
      Pr[fun pair => pair.1.won = true ∧ pair.1.hashCalls ≤ budget |
        joint] := by
        have same := probEvent_congr'
          (p := fun result : AttackResult =>
            result.won = true ∧ result.hashCalls ≤ budget)
          (q := fun result : AttackResult =>
            result.won = true ∧ result.hashCalls ≤ budget)
          (fun _ _ => Iff.rfl) left.symm
        simpa only [probEvent_map,Function.comp_def] using same
    _ ≤ Pr[fun pair => pair.2.1.won = true ∧ pair.2.2 ≤ budget |
      joint] := by
        apply probEvent_mono
        intro pair member event
        obtain ⟨won,count⟩ := preserves pair member event.1
        exact ⟨won,le_trans count event.2⟩
    _ = Pr[fun result => result.1.won = true ∧ result.2 ≤ budget |
      plantedExperiment adversary rounds] := by
        have same := probEvent_congr'
          (p := fun result :
            GroupedBalancedGraphOrganizerView67.Result submission.sizes × Nat =>
            result.1.won = true ∧ result.2 ≤ budget)
          (q := fun result :
            GroupedBalancedGraphOrganizerView67.Result submission.sizes × Nat =>
            result.1.won = true ∧ result.2 ≤ budget)
          (fun _ _ => Iff.rfl) right
        simpa only [probEvent_map,Function.comp_def] using same

theorem secure_of_countedCoupling (coupling : CountedCoupling) :
    submission.Secure := by
  intro adversary rounds budget _
  exact (coupling adversary rounds budget).trans
    (GroupedBalancedOrganizerFinalRisk67.planted_counted_winning_le_budget
      adversary (0 : Cache) rounds budget)

/-- The budget-aware source hybrid has a separate stopped secret-input event.
Its single four-risk theorem bounds the completed graph cutoff winner directly,
without requiring a win-only planted counted coupling. -/
def BudgetCutoffCoupling : Prop :=
  ∀ (adversary : Adversary submission.sizes) (rounds budget : Nat),
    Pr[fun result => result.won = true ∧ result.hashCalls ≤ budget |
      submission.securityExperiment adversary rounds] ≤
    Pr[fun value : Option
        (GroupedBalancedGraphOrganizerView67.Result submission.sizes) =>
      ∃ outcome, value = some outcome ∧ outcome.won = true |
      GroupedBalancedSecurityVerifyAvoids67.jointProgram
        (fun secretKey table =>
          GroupedBalancedGameWorld67.resolve secretKey
            (SecurityBudget.cutoff
              (GroupedBalancedGameWorld67.gameView table
                (GroupedBalancedGraphMonitorSetup67.cache table)
                ((GroupedBalancedPlantedEagerOrganizerRisk67.organizerInteraction
                  submission.sizes GroupedBalancedWire67.wire
                  GroupedBalancedWire67.decode GroupedBalancedWire67.decode
                  adversary (0 : Cache) rounds)
                    (GroupedBalancedGraphMonitorSetup67.cache table)))
              budget))]

theorem secure_of_budgetCutoffCoupling
    (coupling : BudgetCutoffCoupling) : submission.Secure := by
  intro adversary rounds budget _
  exact (coupling adversary rounds budget).trans
    (GroupedBalancedSecurityCounterRisk67.joint_graph_cutoff_winner_le_budget
      adversary rounds budget)

theorem budgetCutoffCoupling_of_verifierRefinement
    (refinement :
      GroupedBalancedSecurityCheckConditional67.VerifierRefinement) :
    BudgetCutoffCoupling := by
  intro adversary rounds budget
  exact GroupedBalancedSecurityVerifyAvoids67.official_bounded_le_joint_cutoff
    refinement adversary rounds budget

theorem secure_of_verifierRefinement
    (refinement :
      GroupedBalancedSecurityCheckConditional67.VerifierRefinement) :
    submission.Secure :=
  secure_of_budgetCutoffCoupling
    (budgetCutoffCoupling_of_verifierRefinement refinement)

#print axioms countedCoupling_of_joint
#print axioms secure_of_countedCoupling
#print axioms secure_of_budgetCutoffCoupling
#print axioms budgetCutoffCoupling_of_verifierRefinement
#print axioms secure_of_verifierRefinement

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityConditional67
