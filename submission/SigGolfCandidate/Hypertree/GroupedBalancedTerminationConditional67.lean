import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRunFunctional67
import SigGolfCandidate.Hypertree.GroupedBalancedSignRunWire67
import SigGolfCandidate.Hypertree.GroupedBalancedExpand67

/-! The three completed program traces reduce universal termination to the
remaining verifier trace. The verifier premise includes arbitrary witnesses. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedTerminationConditional67
open SigGolf
open SigGolfCandidate.Hypertree

private abbrev submission := GroupedBalancedProgram67ByteSign.submission

def VerifierTerminates : Prop :=
  ∀ (hash : Hash) (input : Input submission.sizes .verify),
    let result := submission.runWith hash .verify input
    result.finished = true ∧ result.cycles < CYCLE_LIMIT

theorem termination (verifier : VerifierTerminates) :
    submission.Terminates := by
  intro hash phase input
  cases phase with
  | keygen =>
      dsimp only
      rw [GroupedBalancedKeygenRunFunctional67.run_exact hash input]
      constructor
      · rfl
      · change 221107 < CYCLE_LIMIT
        decide
  | sign =>
      obtain ⟨secretKey, cache, message⟩ := input
      obtain ⟨cycles, bound, run⟩ :=
        GroupedBalancedSignRunWire67.run_refines hash secretKey cache message
      dsimp only
      rw [run]
      exact ⟨rfl, lt_of_le_of_lt bound (by decide)⟩
  | expand =>
      obtain ⟨finished, _, cycles, _, _⟩ :=
        Expansion67.run_bound hash input
      exact ⟨finished, by rw [cycles]; decide⟩
  | verify =>
      exact verifier hash input

#print axioms termination

end SigGolfCandidate.Hypertree.GroupedBalancedTerminationConditional67
