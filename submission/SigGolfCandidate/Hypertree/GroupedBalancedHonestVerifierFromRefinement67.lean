import SigGolfCandidate.Hypertree.GroupedBalancedHonestConditional67
import SigGolfCandidate.Hypertree.GroupedBalancedSecurityCheckConditional67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyRunSummary67

/-! Honest verifier success follows from arbitrary-wire refinement and the
machine trace's cycle bound. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedHonestVerifierFromRefinement67
open SigGolf OracleComp
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev submission := GroupedBalancedProgram67ByteSign.submission

private theorem result_success (result : RunResult Unit) (cycles : Nat)
    (accepted : result.value.isSome = true)
    (finished : result.finished = true)
    (cyclesEq : result.cycles = cycles) :
    result = ⟨some (),true,cycles,result.hashCalls,
      result.hashCompressions⟩ := by
  cases result with
  | mk v f c calls blocks =>
    cases v with
    | none => simp at accepted
    | some witness =>
        cases witness
        cases f with
        | false => simp at finished
        | true =>
            simp only at cyclesEq
            cases cyclesEq
            rfl

private theorem exact_result (result : RunResult Unit)
    (accepted : result.value.isSome = true)
    (finished : result.finished = true)
    (cycleBound : result.cycles ≤ 161485) :
    ∃ cycles calls blocks : Nat, cycles ≤ 161485 ∧
      result =
        ⟨some (),true,cycles,calls,blocks⟩ := by
  refine ⟨result.cycles,result.hashCalls,result.hashCompressions,
    cycleBound,?_⟩
  exact result_success result result.cycles accepted finished rfl

private theorem oracle_success (hash : Hash) (secretKey : SecretKey)
    (message : Message) :
    evalWithAnswerFn hash
      (GroupedBalancedSecurityCheckConditional67.program
        (GroupedBalancedScheme67.keygen hash secretKey) message
        (GroupedBalancedWire67.wire
          (GroupedBalancedScheme67.sign hash secretKey message))) = true := by
  let pk := GroupedBalancedScheme67.keygen hash secretKey
  let signature := GroupedBalancedScheme67.sign hash secretKey message
  let wire := GroupedBalancedWire67.wire signature
  change evalWithAnswerFn hash
    (GroupedBalancedVerifyOracle67.verify pk message
      (GroupedBalancedWire67.decode wire)) = true
  rw [GroupedBalancedWire67.wire_decode]
  exact (GroupedBalancedVerifyOracle67.eval_verify_iff
    hash pk message signature).2
      (GroupedBalancedScheme67.correct hash secretKey message)

private theorem accepted_of_refinement
    (refinement : GroupedBalancedSecurityCheckConditional67.VerifierRefinement)
    (hash : Hash) (pk : PublicKey) (message : Message)
    (wire : Bytes submission.sizes.witness)
    (oracleSuccess : evalWithAnswerFn hash
      (GroupedBalancedSecurityCheckConditional67.program pk message wire) = true) :
    (submission.runWith hash .verify (message,pk,wire)).value.isSome = true :=
  (refinement hash pk message wire).1.trans oracleSuccess

theorem honestVerifier_of_refinement
    (refinement : GroupedBalancedSecurityCheckConditional67.VerifierRefinement) :
    GroupedBalancedHonestConditional67.HonestVerifier 161485 := by
  intro hash secretKey message
  let pk := GroupedBalancedScheme67.keygen hash secretKey
  let wire := GroupedBalancedWire67.wire
    (GroupedBalancedScheme67.sign hash secretKey message)
  have accepted := accepted_of_refinement refinement hash pk message wire
    (oracle_success hash secretKey message)
  have finished := GroupedBalancedVerifyRunSummary67.finished hash
    (message,pk,wire)
  have cycleBound := GroupedBalancedVerifyRunSummary67.cycles_le hash
    (message,pk,wire)
  exact exact_result (submission.runWith hash .verify (message,pk,wire))
    accepted finished cycleBound

#print axioms honestVerifier_of_refinement
end SigGolfCandidate.Hypertree.GroupedBalancedHonestVerifierFromRefinement67
