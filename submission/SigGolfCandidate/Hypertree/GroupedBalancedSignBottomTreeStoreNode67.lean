import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeStoreData67
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeStoreNode67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
theorem store_node (s : MachineState) (digest : Reference.Digest)
    (answer : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80300 i.val) =
        digest.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (GroupedBalancedSignBottomTreeStoreData67.storedState s).getMem
        ((GroupedBalancedSignBottomTreeHashStorePtr67.storeState s).getReg .x7 +
          BitVec.ofNat 64 (8*i.val)) =
        digest.extractLsb' (64*i.val) 64 := by
  intro i
  fin_cases i
  · simpa [Signing.wordAddress] using
      (GroupedBalancedSignBottomTreeStoreData67.stored_low s).trans (answer 0)
  · simpa [Signing.wordAddress] using
      (GroupedBalancedSignBottomTreeStoreData67.stored_high s).trans (answer 1)
#print axioms store_node
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeStoreNode67
