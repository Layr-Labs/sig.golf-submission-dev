import SigGolfCandidate.Hypertree.GroupedBalancedVerifyRun67

/-! Small resource projection of the complete arbitrary-input verifier run. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyRunSummary67
open SigGolf
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev submission := GroupedBalancedProgram67ByteSign.submission

theorem finish_cycles (hash : Hash)
    (input : Input submission.sizes .verify) :
    ∃ cycles : Nat, cycles ≤ 156325 ∧
      (submission.runWith hash .verify input).finished = true ∧
      (submission.runWith hash .verify input).cycles = cycles :=
  (GroupedBalancedVerifyRun67.run_observation hash input).elim
    (fun _ hinit => hinit.elim fun _ hentry =>
      hentry.elim fun cycles h =>
        ⟨cycles,h.2.1,h.2.2.1,h.2.2.2.1⟩)

theorem finished (hash : Hash)
    (input : Input submission.sizes .verify) :
    (submission.runWith hash .verify input).finished = true :=
  (finish_cycles hash input).elim fun _ h => h.2.1

theorem cycles_le (hash : Hash)
    (input : Input submission.sizes .verify) :
    (submission.runWith hash .verify input).cycles ≤ 156325 :=
  (finish_cycles hash input).elim fun cycles h => by
    rw [h.2.2]
    exact h.1

#print axioms finish_cycles
#print axioms finished
#print axioms cycles_le
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyRunSummary67
