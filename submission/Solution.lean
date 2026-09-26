import SigGolfCandidate.Hypertree.GroupedBalancedCertificateFromObservation67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifierObservation67

namespace SigGolf.Challenge

noncomputable def submission : SigGolf.Submission :=
  SigGolfCandidate.Hypertree.GroupedBalancedProgram67ByteSign.submission

theorem signature_bytes : submission.sizes.signature = 50848 := by rfl

theorem witness_bytes : submission.sizes.witness = 50848 := by rfl

theorem layout_offsets : submission.layout =
  { message := 0, secretKey := 32, publicKey := 64, cache := 96,
    signature := 131168, witness := 182016 } := by rfl

theorem certificate : SigGolf.Certificate submission 156325 :=
  SigGolfCandidate.Hypertree.GroupedBalancedCertificateFromObservation67.certificate_of_observation
    SigGolfCandidate.Hypertree.GroupedBalancedVerifierObservation67.entry_observation

end SigGolf.Challenge
