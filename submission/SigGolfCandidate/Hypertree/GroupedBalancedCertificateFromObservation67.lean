import SigGolfCandidate.Hypertree.GroupedBalancedCertificateConditional67
import SigGolfCandidate.Hypertree.GroupedBalancedHonestVerifierFromRefinement67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifierTermination67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifierRefinementFromObservation67

/-! The direct67 certificate has only the concrete loaded verifier observation
as a remaining machine-level input. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedCertificateFromObservation67
open SigGolf
open SigGolfCandidate.Hypertree

theorem certificate_of_observation
    (observation :
      GroupedBalancedVerifierRefinementFromObservation67.EntryObservation) :
    SigGolf.Certificate GroupedBalancedProgram67ByteSign.submission 156325 := by
  have refinement :=
    GroupedBalancedVerifierRefinementFromObservation67.verifier_refinement
      observation
  exact GroupedBalancedCertificateConditional67.certificate_of_verifierRefinement
    156325
    (GroupedBalancedHonestVerifierFromRefinement67.honestVerifier_of_refinement
      refinement)
    GroupedBalancedVerifierTermination67.verifier_terminates
    refinement

#print axioms certificate_of_observation
end SigGolfCandidate.Hypertree.GroupedBalancedCertificateFromObservation67
