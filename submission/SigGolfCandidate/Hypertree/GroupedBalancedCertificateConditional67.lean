import SigGolfCandidate.Hypertree.GroupedBalancedHonestConditional67
import SigGolfCandidate.Hypertree.GroupedBalancedSecurityConditional67
import SigGolfCandidate.Hypertree.GroupedBalancedTerminationConditional67

/-! The final candidate certificate requires the verifier trace and the
counted security coupling. These are explicit premises until proved. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedCertificateConditional67
open SigGolf
open SigGolfCandidate.Hypertree

private abbrev submission := GroupedBalancedProgram67ByteSign.submission

theorem certificate (C : Nat)
    (honestVerifier : GroupedBalancedHonestConditional67.HonestVerifier C)
    (verifierTerminates :
      GroupedBalancedTerminationConditional67.VerifierTerminates)
    (countedCoupling : GroupedBalancedSecurityConditional67.CountedCoupling) :
    SigGolf.Certificate submission C := by
  exact ⟨GroupedBalancedProgram67ByteSign.admissible,
    GroupedBalancedTerminationConditional67.termination verifierTerminates,
    GroupedBalancedHonestConditional67.completeness C honestVerifier,
    GroupedBalancedHonestConditional67.compressionBounds C honestVerifier,
    GroupedBalancedSecurityConditional67.secure_of_countedCoupling countedCoupling,
    GroupedBalancedHonestConditional67.verificationBound C honestVerifier⟩

theorem certificate_of_budgetCutoffCoupling (C : Nat)
    (honestVerifier : GroupedBalancedHonestConditional67.HonestVerifier C)
    (verifierTerminates :
      GroupedBalancedTerminationConditional67.VerifierTerminates)
    (budgetCoupling :
      GroupedBalancedSecurityConditional67.BudgetCutoffCoupling) :
    SigGolf.Certificate submission C := by
  exact ⟨GroupedBalancedProgram67ByteSign.admissible,
    GroupedBalancedTerminationConditional67.termination verifierTerminates,
    GroupedBalancedHonestConditional67.completeness C honestVerifier,
    GroupedBalancedHonestConditional67.compressionBounds C honestVerifier,
    GroupedBalancedSecurityConditional67.secure_of_budgetCutoffCoupling
      budgetCoupling,
    GroupedBalancedHonestConditional67.verificationBound C honestVerifier⟩

theorem certificate_of_verifierRefinement (C : Nat)
    (honestVerifier : GroupedBalancedHonestConditional67.HonestVerifier C)
    (verifierTerminates :
      GroupedBalancedTerminationConditional67.VerifierTerminates)
    (verifierRefinement :
      GroupedBalancedSecurityCheckConditional67.VerifierRefinement) :
    SigGolf.Certificate submission C :=
  certificate_of_budgetCutoffCoupling C honestVerifier verifierTerminates
    (GroupedBalancedSecurityConditional67.budgetCutoffCoupling_of_verifierRefinement
      verifierRefinement)

#print axioms certificate
#print axioms certificate_of_budgetCutoffCoupling
#print axioms certificate_of_verifierRefinement

end SigGolfCandidate.Hypertree.GroupedBalancedCertificateConditional67
