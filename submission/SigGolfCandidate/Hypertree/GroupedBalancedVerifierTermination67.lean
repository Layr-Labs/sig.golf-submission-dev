import SigGolfCandidate.Hypertree.GroupedBalancedTerminationConditional67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyRun67

/-! The completed verifier execution discharges the last termination premise. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifierTermination67
open SigGolf
open SigGolfCandidate.Hypertree

theorem verifier_terminates :
    GroupedBalancedTerminationConditional67.VerifierTerminates := by
  intro hash input
  change (GroupedBalancedProgram67ByteSign.submission.runWith hash .verify input).finished = true ∧
    (GroupedBalancedProgram67ByteSign.submission.runWith hash .verify input).cycles < CYCLE_LIMIT
  have observed := GroupedBalancedVerifyRun67.run_observation hash input
  rcases observed with ⟨_, _, cycles, _, bound, finished, exactCycles, _, _, _, _⟩
  exact ⟨finished, by rw [exactCycles]; exact lt_of_le_of_lt bound (by decide)⟩

theorem termination : GroupedBalancedProgram67ByteSign.submission.Terminates :=
  GroupedBalancedTerminationConditional67.termination verifier_terminates

#print axioms verifier_terminates
#print axioms termination
end SigGolfCandidate.Hypertree.GroupedBalancedVerifierTermination67
