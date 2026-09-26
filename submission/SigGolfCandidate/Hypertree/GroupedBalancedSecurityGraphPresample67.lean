import SigGolfCandidate.Hypertree.SecurityGraphHidden
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorTable67

/-! Presampling the direct67 public graph is distribution preserving for any
observable continuation of the shared lazy random oracle. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityGraphPresample67
open SigGolf OracleComp OracleSpec Reference SecurityCache
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphSampling67
open GroupedBalancedGraphOrder67

/-- The direct67 graph's complete set of public labels and its programmed
query cache can be sampled before any observable oracle computation. The
precomputation is hidden, so its queries are not charged to the continuation. -/
theorem graph_presampling {α : Type}
    (privateAnswers : GroupedBalancedGraphPayload67.PrivateAnswers)
    (program : OracleComp World α) (initial : Labels) :
    𝒮[SecurityGraphHidden.observe program ∅] =
      𝒮[do
        let labels ← $ᵗ Labels
        SecurityGraphHidden.observe program
          (graphCache privateAnswers positions labels ∅)] := by
  rw [← SecurityGraphHidden.insert_prefix
    (GroupedSecurityGraph.readGraph
      (GroupedBalancedGraphPayload67.payload privateAnswers) positions initial)
    program ∅]
  rw [evalSPMF_bind, GroupedBalancedGraphUniform67.run_complete_graph]
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]

#print axioms graph_presampling

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityGraphPresample67
