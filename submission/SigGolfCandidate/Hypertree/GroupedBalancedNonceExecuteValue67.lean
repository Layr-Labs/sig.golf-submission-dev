import SigGolfCandidate.Hypertree.SecurityMonitorNonceLift

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceExecuteValue67
open SigGolf OracleComp OracleSpec Reference
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

noncomputable def nonceSample : ProbComp SecurityGraphFactor.NonceTable :=
  $ᵗ SecurityGraphFactor.NonceTable

theorem execute_value_projection {β : Type}
    (program : SecurityNonceProgram.Program β) :
    SecurityNonceProgram.Outcome.value <$>
      SecurityNonceProgram.execute program ∅ =
    (do let nonces ← nonceSample
        SecurityMonitorNonceLift.observe nonces ∅ program) := by
  unfold SecurityNonceProgram.execute
  rw [map_bind]
  apply bind_congr
  intro nonces
  rfl

#print axioms execute_value_projection

end SigGolfCandidate.Hypertree.GroupedBalancedNonceExecuteValue67
