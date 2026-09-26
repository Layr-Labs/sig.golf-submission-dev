import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRunFunctional67
import SigGolfCandidate.Hypertree.GroupedBalancedSignRunWire67

/-! The organizer's security game observes keygen and signing values and exact
hash-call counts. Their cycle and compression fields are private to this game. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityObservedPhases67
open SigGolf OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

private abbrev submission := GroupedBalancedProgram67ByteSign.submission

def view {α : Type} (result : RunResult α) : Option α × Nat :=
  (result.value,result.hashCalls)

theorem keygen (hash : Hash) (secretKey : SecretKey) :
    evalWithAnswerFn hash (view <$> submission.run .keygen secretKey) =
      (some (GroupedBalancedScheme67.keygen hash secretKey,
        (0 : Cache)),3983) := by
  simp only [evalWithAnswerFn_map]
  change view (submission.runWith hash .keygen secretKey) = _
  rw [GroupedBalancedKeygenRunFunctional67.run_exact]
  rfl

theorem sign (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    evalWithAnswerFn hash (view <$>
      submission.run .sign (secretKey,cache,message)) =
      (some (GroupedBalancedWire67.wire
        (GroupedBalancedScheme67.sign hash secretKey message)),
        122548) := by
  obtain ⟨cycles,_,run⟩ :=
    GroupedBalancedSignRunWire67.run_refines hash secretKey
      cache message
  simp only [evalWithAnswerFn_map]
  change view (submission.runWith hash .sign
    (secretKey,cache,message)) = _
  rw [run]
  rfl

theorem signing (hash : Hash) (secretKey : SecretKey)
    (request : SigningRequest) :
    evalWithAnswerFn hash (view <$>
      submission.signingOracle secretKey request) =
      (some (GroupedBalancedWire67.wire
        (GroupedBalancedScheme67.sign hash secretKey request.message)),
        122548) := by
  simpa only [Submission.signingOracle,Output] using
    sign hash secretKey request.cache request.message

#print axioms keygen
#print axioms sign
#print axioms signing

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityObservedPhases67
