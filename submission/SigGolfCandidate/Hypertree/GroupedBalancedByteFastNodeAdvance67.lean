import SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeCoreWords67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeProgress67

/-! A node hash followed by its exact pointer and edge-count advance. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeAdvance67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeProgress67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private theorem high_disjoint (a : Word) (high : 0x81000 ≤ a.toNat)
    (base : Nat) (below : base + 8*4 < 0x81000) (i : Fin 4) :
    a ≠ Signing.wordAddress base i.val := by
  intro eq
  have h := congrArg BitVec.toNat eq
  simp only [Signing.wordAddress,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : base+8*i.val < 2^64)] at h
  omega

theorem node_advance (hash : Hash) (s : MachineState)
    (level tree : Nat) (left right : Reference.Digest)
    (pc : s.pc = 0x1880)
    (hlevel : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (hindex : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (hchildren : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x80520 i.val) =
        if i.val < 2 then left.extractLsb' (64*i.val) 64
        else right.extractLsb' (64*(i.val-2)) 64) :
    ∃ final,
      Trace hash GroupedBalancedVerifyImage67Fast2Byte.image s
        105 112 1 1 final ∧
      (final.pc = if final.getReg .x6 ≠ final.getReg .x7
        then 0x1758 else 0x19c4) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80500 i.val) =
          (Reference.node hash level tree left right).extractLsb'
            (64*i.val) 64) ∧
      final.getMem 0x81048 = s.getMem 0x81048 + 16 ∧
      final.getMem 0x81000 = s.getMem 0x81000 + 1 ∧
      final.getMem 0x81050 = s.getMem 0x81050 + 1 ∧
      (∀ i : Fin 3,
        final.getMem (Signing.wordAddress 0x81008 i.val) =
          s.getMem (Signing.wordAddress 0x81008 i.val)) := by
  obtain ⟨node,first,nodePC,nodeWords,nodeFrame⟩ :=
    GroupedBalancedByteFastNodeCoreWords67.node_core_words hash s
      level tree left right pc hlevel hindex hchildren
  let final := GroupedBalancedByteFastEdgeUpdate67.updateState node
  have second := GroupedBalancedByteFastEdgeUpdate67.update_block node nodePC
  have finalPC := GroupedBalancedByteFastEdgeUpdate67.update_pc node nodePC
  have highFrame (a : Word) (high : 0x81000 ≤ a.toNat) :
      node.getMem a = s.getMem a := by
    exact nodeFrame a
      (high_disjoint a high 0x80020 (by decide))
      (high_disjoint a high 0x80000 (by decide))
      (high_disjoint a high 0x80300 (by decide))
      (fun i => high_disjoint a high 0x80500 (by decide)
        ⟨i.val,by omega⟩)
  refine ⟨final,?_,finalPC,?_,?_,?_,?_,?_⟩
  · have path := first.trans (OrdinarySteps.trace (hash := hash) second)
    simpa [GroupedBalancedByteFastNodeCoreWords67.image,
      GroupedBalancedByteFastEdgeUpdate67.image] using path
  · intro i
    rw [update_mem node (Signing.wordAddress 0x80500 i.val)
      (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)]
    exact nodeWords i
  · rw [update_pointer, highFrame 0x81048 (by decide)]
  · rw [update_edge_count, highFrame 0x81000 (by decide)]
  · rw [update_level_count, highFrame 0x81050 (by decide)]
  · intro i
    rw [update_mem node (Signing.wordAddress 0x81008 i.val)
      (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)]
    exact highFrame _ (by fin_cases i <;> decide)

#print axioms node_advance

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeAdvance67
