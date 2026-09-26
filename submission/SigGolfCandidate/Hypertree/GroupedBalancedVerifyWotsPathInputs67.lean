import SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsReadyInput67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastWotsProtected67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeNat67

/-! The WOTS loop retains the index and sibling words for the Merkle path. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsPathInputs67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyWotsReady67
open GroupedBalancedVerifyWotsHeaderFields67
open GroupedBalancedByteFastWotsProtected67
open GroupedBalancedByteFastEdgeIndexRefine67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private theorem original_word (s : MachineState) (a : Word)
    (h30 : a ≠ 0x81030) (h38 : a ≠ 0x81038)
    (h00 : a ≠ 0x90000) (h08 : a ≠ 0x90008)
    (h10 : a ≠ 0x90010) (h18 : a ≠ 0x90018) :
    (readyState s).getMem a = s.getMem a := by
  rw [ready_mem]
  exact header_mem_frame s a h30 h38 h00 h08 h10 h18

theorem path_inputs (s final : MachineState)
    (base leaf start height : Nat)
    (siblings : Nat → Reference.Digest)
    (baseWord : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (index : StoredIndex s (BitVec.ofNat 192 leaf))
    (heightWord : s.getMem 0x81060 = BitVec.ofNat 64 height)
    (wireBound : start + 16*67 + 16*height ≤ 0x38da0)
    (witness : ∀ j, j < height → ∀ half : Fin 2,
      s.getMem (BitVec.ofNat 64
        (start+16*67+16*j+8*half.val)) =
        (siblings j).extractLsb' (64*half.val) 64)
    (frame : ∀ a : Word, Protected a →
      final.getMem a = (readyState s).getMem a) :
    final.getMem 0x81000 = BitVec.ofNat 64 base ∧
    StoredIndex final (BitVec.ofNat 192 leaf) ∧
    final.getMem 0x81060 = BitVec.ofNat 64 height ∧
    (∀ j, j < height → ∀ half : Fin 2,
      final.getMem (BitVec.ofNat 64
        (start+16*67+16*j+8*half.val)) =
        (siblings j).extractLsb' (64*half.val) 64) := by
  constructor
  · exact (frame 0x81000 (Or.inr (by decide))).trans
      ((original_word s 0x81000 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)).trans
          baseWord)
  constructor
  · intro i
    have address : (Signing.wordAddress 0x81008 i.val).toNat =
        0x81008+8*i.val := by
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x81008+8*i.val < 2^64)]
    have safeIndex : Protected (Signing.wordAddress 0x81008 i.val) := by
      right
      constructor <;> omega
    rw [frame _ safeIndex,
      original_word s _ (by fin_cases i <;> decide)
        (by fin_cases i <;> decide)
        (by fin_cases i <;> decide)
        (by fin_cases i <;> decide)
        (by fin_cases i <;> decide)
        (by fin_cases i <;> decide)]
    exact index i
  constructor
  · exact (frame 0x81060 (Or.inr (by decide))).trans
      ((original_word s 0x81060 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)).trans
          heightWord)
  · intro j hj half
    let a : Word := BitVec.ofNat 64
      (start+16*67+16*j+8*half.val)
    have low : a.toNat < 0x80000 := by
      simp only [a,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega :
          start+16*67+16*j+8*half.val < 2^64)]
      omega
    exact (frame a (Or.inl low)).trans
      ((ready_mem s a).trans
        ((header_low_frame s a (by omega)).trans (witness j hj half)))

#print axioms path_inputs
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsPathInputs67
