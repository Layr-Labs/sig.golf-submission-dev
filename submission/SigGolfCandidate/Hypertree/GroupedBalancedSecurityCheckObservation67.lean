import SigGolfCandidate.Hypertree.GroupedBalancedSecurityCheckConditional67
import SigGolfCandidate.Hypertree.GroupedBalancedExpandCopy67

/-! Conditional fixed-oracle observation of both forgery forms. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityCheckObservation67
open SigGolf OracleComp SecurityVerifyCost
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

private abbrev submission := GroupedBalancedProgram67ByteSign.submission
private abbrev verifierProgram := GroupedBalancedSecurityCheckConditional67.program

def referenceOutcome (hash : Hash) (pk : PublicKey)
    (transcript : Transcript submission.sizes) :
    Forgery submission.sizes → AttackResult
  | .witness message wire =>
      ⟨evalWithAnswerFn hash (verifierProgram pk message wire) &&
        transcript.freshMessage message,
        transcript.hashCalls + calls hash (verifierProgram pk message wire)⟩
  | .signature message wire =>
      ⟨evalWithAnswerFn hash (verifierProgram pk message wire) &&
        transcript.freshSignature message wire,
        transcript.hashCalls + calls hash (verifierProgram pk message wire)⟩

theorem witness (refinement : GroupedBalancedSecurityCheckConditional67.VerifierRefinement)
    (hash : Hash) (pk : PublicKey)
    (transcript : Transcript submission.sizes)
    (message : Message) (wire : Bytes submission.sizes.witness) :
    evalWithAnswerFn hash
      (submission.checkForgery pk transcript (.witness message wire)) =
        referenceOutcome hash pk transcript (.witness message wire) := by
  obtain ⟨value,cost⟩ := refinement hash pk message wire
  unfold Submission.runWith at value cost
  have result := congrArg₂ AttackResult.mk
    (congrArg (fun b => b && transcript.freshMessage message) value)
    (congrArg (fun n => transcript.hashCalls + n) cost)
  simpa only [Submission.checkForgery, referenceOutcome,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure] using result

private theorem signature_case (hash : Hash) (pk : PublicKey)
    (transcript : Transcript submission.sizes)
    (message : Message) (wire : Bytes submission.sizes.signature)
    (accepted : Bool) (count : Nat)
    (expandValue : (submission.runWith hash .expand (message,pk,wire)).value = some wire)
    (expandCalls : (submission.runWith hash .expand (message,pk,wire)).hashCalls = 0)
    (verifyValue : (submission.runWith hash .verify (message,pk,wire)).value.isSome = accepted)
    (verifyCalls : (submission.runWith hash .verify (message,pk,wire)).hashCalls = count) :
    evalWithAnswerFn hash
      (submission.checkForgery pk transcript (.signature message wire)) =
        ⟨accepted && transcript.freshSignature message wire,
          transcript.hashCalls + count⟩ := by
  unfold Submission.runWith at expandValue expandCalls verifyValue verifyCalls
  simp only [Submission.checkForgery,evalWithAnswerFn_bind]
  rw [expandValue]
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
  rw [expandCalls,verifyValue,verifyCalls]
  simp only [Nat.add_zero]

theorem signature (refinement : GroupedBalancedSecurityCheckConditional67.VerifierRefinement)
    (hash : Hash) (pk : PublicKey)
    (transcript : Transcript submission.sizes)
    (message : Message) (wire : Bytes submission.sizes.signature) :
    evalWithAnswerFn hash
      (submission.checkForgery pk transcript (.signature message wire)) =
        referenceOutcome hash pk transcript (.signature message wire) := by
  obtain ⟨value,cost⟩ := refinement hash pk message wire
  have expandValue := Expansion67.run_identity hash (message,pk,wire)
  have expandCalls := (Expansion67.run_bound hash (message,pk,wire)).2.2.2.1
  simpa only [referenceOutcome] using
    signature_case hash pk transcript message wire
      (evalWithAnswerFn hash (GroupedBalancedSecurityCheckConditional67.program pk message wire))
      (calls hash (GroupedBalancedSecurityCheckConditional67.program pk message wire))
      expandValue expandCalls value cost

theorem check (refinement : GroupedBalancedSecurityCheckConditional67.VerifierRefinement)
    (hash : Hash) (pk : PublicKey)
    (transcript : Transcript submission.sizes)
    (forgery : Forgery submission.sizes) :
    evalWithAnswerFn hash (submission.checkForgery pk transcript forgery) =
      referenceOutcome hash pk transcript forgery := by
  cases forgery with
  | witness message wire => exact witness refinement hash pk transcript message wire
  | signature message wire => exact signature refinement hash pk transcript message wire

#print axioms witness
#print axioms signature
#print axioms check

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityCheckObservation67
