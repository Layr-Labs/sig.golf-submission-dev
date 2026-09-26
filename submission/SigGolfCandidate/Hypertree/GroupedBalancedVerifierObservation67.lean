import SigGolfCandidate.Hypertree.GroupedBalancedVerifyRun67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifierRefinementFromObservation67

/-! The complete loaded RISC-V verifier supplies the semantic observation
used by correctness and counted adaptive security. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifierObservation67
open SigGolf
open SigGolfCandidate.Hypertree

theorem entry_observation :
    GroupedBalancedVerifierRefinementFromObservation67.EntryObservation := by
  intro hash pk message wire
  obtain ⟨initial,entry,_,loaded,_,_,_,value,calls,_,low,indexEq,rootEq⟩ :=
    GroupedBalancedVerifyRun67.run_observation hash (message,pk,wire)
  exact ⟨initial,entry,loaded,low,value,calls,indexEq,rootEq⟩

#print axioms entry_observation
end SigGolfCandidate.Hypertree.GroupedBalancedVerifierObservation67
