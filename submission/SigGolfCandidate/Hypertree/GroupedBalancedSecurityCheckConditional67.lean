import SigGolfCandidate.Hypertree.GroupedBalancedProgram67ByteSign
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyOracle67
import SigGolfCandidate.Hypertree.GroupedBalancedWire67
import SigGolfCandidate.Hypertree.SecurityVerifyCost

/-! Security needs verifier refinement on every attacker-supplied wire, not only
honest signatures. Both its acceptance bit and exact hash-call count matter. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityCheckConditional67
open SigGolf OracleComp SecurityVerifyCost

private abbrev submission := GroupedBalancedProgram67ByteSign.submission

def program (pk : PublicKey) (message : Message)
    (wire : Bytes submission.sizes.witness) : OracleComp HashSpec Bool :=
  GroupedBalancedVerifyOracle67.verify pk message
    (GroupedBalancedWire67.decode wire)

def VerifierRefinement : Prop :=
  ∀ (hash : Hash) (pk : PublicKey) (message : Message)
    (wire : Bytes submission.sizes.witness),
    let machine := submission.runWith hash .verify (message,pk,wire)
    machine.value.isSome = evalWithAnswerFn hash (program pk message wire) ∧
      machine.hashCalls = calls hash (program pk message wire)

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityCheckConditional67
