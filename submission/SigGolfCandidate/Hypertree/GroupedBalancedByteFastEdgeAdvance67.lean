import SigGolfCandidate.Hypertree.GroupedBalancedByteFastSideAdvance67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastIndexFields67

/-! Full functional edge step from index dispatch through the node update. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeAdvance67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastIndexFields67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private theorem low_ne_destination (a : Word)
    (low : a.toNat < 0x80020) (base i : Nat)
    (high : 0x80020 ≤ base) (small : base+8*i < 2^64) :
    a ≠ Signing.wordAddress base i := by
  intro eq
  have h := congrArg BitVec.toNat eq
  simp only [Signing.wordAddress,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small] at h
  omega

theorem left_edge_advance (hash : Hash) (s : MachineState)
    (level tree : Nat) (current sibling : Reference.Digest)
    (pc : s.pc = 0x1758)
    (side : s.getMem 0x81008 &&& 1 = (0 : Word))
    (ptr0 : accessValid (s.getMem 0x81048) 8 = true)
    (ptr8 : accessValid (s.getMem 0x81048 + 8) 8 = true)
    (low : ∀ half : Fin 2,
      (s.getMem 0x81048 + BitVec.ofNat 64 (8*half.val)).toNat < 0x80020)
    (hlevel : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (hindex : ∀ i : Fin 3,
      (GroupedBalancedByteFastEdgeIndex67.indexState s).getMem
        (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (root : ∀ half : Fin 2,
      s.getMem (Signing.wordAddress 0x80500 half.val) =
        current.extractLsb' (64*half.val) 64)
    (witness : ∀ half : Fin 2,
      s.getMem (s.getMem 0x81048 + BitVec.ofNat 64 (8*half.val)) =
        sibling.extractLsb' (64*half.val) 64) :
    ∃ final,
      Trace hash GroupedBalancedVerifyImage67Fast2Byte.image s
        164 171 1 1 final ∧
      (final.pc = if final.getReg .x6 ≠ final.getReg .x7
        then 0x1758 else 0x19c4) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80500 i.val) =
          (Reference.node hash level tree current sibling).extractLsb'
            (64*i.val) 64) ∧
      final.getMem 0x81048 = s.getMem 0x81048 + 16 ∧
      final.getMem 0x81000 = s.getMem 0x81000 + 1 ∧
      final.getMem 0x81050 = s.getMem 0x81050 + 1 ∧
      (∀ i : Fin 3,
        final.getMem (Signing.wordAddress 0x81008 i.val) =
          (GroupedBalancedByteFastEdgeIndex67.indexState s).getMem
            (Signing.wordAddress 0x81008 i.val)) := by
  let indexed := GroupedBalancedByteFastEdgeIndex67.indexState s
  have first := GroupedBalancedByteFastEdgeIndex67.index_block s pc
  have indexedPC : indexed.pc = 0x1830 := by
    rw [GroupedBalancedByteFastEdgeIndex67.index_pc s pc]
    rw [index_side]
    exact if_pos side
  have indexedPtr : indexed.getMem 0x81048 = s.getMem 0x81048 :=
    GroupedBalancedByteFastEdgeIndex67.index_pointer_frame s
  have indexedLevel : indexed.getMem 0x81000 = BitVec.ofNat 64 level := by
    rw [index_mem s 0x81000 (by decide) (by decide)
      (by decide) (by decide)]
    exact hlevel
  have indexedRoot : ∀ half : Fin 2,
      indexed.getMem (Signing.wordAddress 0x80500 half.val) =
        current.extractLsb' (64*half.val) 64 := by
    intro half
    rw [index_mem s _ (by fin_cases half <;> decide)
      (by fin_cases half <;> decide) (by fin_cases half <;> decide)
      (by fin_cases half <;> decide)]
    exact root half
  have indexedWitness : ∀ half : Fin 2,
      indexed.getMem
        (indexed.getMem 0x81048 + BitVec.ofNat 64 (8*half.val)) =
        sibling.extractLsb' (64*half.val) 64 := by
    intro half
    rw [indexedPtr,index_low_frame s _ (low half)]
    exact witness half
  have indexedSeparate : ∀ half : Fin 2, ∀ i, i < 2 →
      indexed.getMem 0x81048 + BitVec.ofNat 64 (8*half.val) ≠
        Signing.wordAddress 0x80520 i := by
    intro half i hi
    rw [indexedPtr]
    exact low_ne_destination _ (low half) 0x80520 i (by decide)
      (by omega)
  obtain ⟨final,rest,done,result,ptr,count,levelCount,index⟩ :=
    GroupedBalancedByteFastSideAdvance67.left_advance hash indexed
      level tree current sibling indexedPC
      (by rw [indexedPtr]; exact ptr0)
      (by rw [indexedPtr]; exact ptr8)
      indexedLevel hindex indexedRoot indexedWitness indexedSeparate
  refine ⟨final,?_,done,result,?_,?_,?_,index⟩
  · have path := (OrdinarySteps.trace (hash := hash) first).trans rest
    simpa [indexed,GroupedBalancedByteFastEdgeIndex67.image] using path
  · rw [ptr,indexedPtr]
  · rw [count,index_mem s 0x81000 (by decide) (by decide)
      (by decide) (by decide)]
  · rw [levelCount,index_mem s 0x81050 (by decide) (by decide)
      (by decide) (by decide)]

#print axioms left_edge_advance

theorem right_edge_advance (hash : Hash) (s : MachineState)
    (level tree : Nat) (current sibling : Reference.Digest)
    (pc : s.pc = 0x1758)
    (side : s.getMem 0x81008 &&& 1 ≠ (0 : Word))
    (ptr0 : accessValid (s.getMem 0x81048) 8 = true)
    (ptr8 : accessValid (s.getMem 0x81048 + 8) 8 = true)
    (low : ∀ half : Fin 2,
      (s.getMem 0x81048 + BitVec.ofNat 64 (8*half.val)).toNat < 0x80020)
    (hlevel : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (hindex : ∀ i : Fin 3,
      (GroupedBalancedByteFastEdgeIndex67.indexState s).getMem
        (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (root : ∀ half : Fin 2,
      s.getMem (Signing.wordAddress 0x80500 half.val) =
        current.extractLsb' (64*half.val) 64)
    (witness : ∀ half : Fin 2,
      s.getMem (s.getMem 0x81048 + BitVec.ofNat 64 (8*half.val)) =
        sibling.extractLsb' (64*half.val) 64) :
    ∃ final,
      Trace hash GroupedBalancedVerifyImage67Fast2Byte.image s
        165 172 1 1 final ∧
      (final.pc = if final.getReg .x6 ≠ final.getReg .x7
        then 0x1758 else 0x19c4) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80500 i.val) =
          (Reference.node hash level tree sibling current).extractLsb'
            (64*i.val) 64) ∧
      final.getMem 0x81048 = s.getMem 0x81048 + 16 ∧
      final.getMem 0x81000 = s.getMem 0x81000 + 1 ∧
      final.getMem 0x81050 = s.getMem 0x81050 + 1 ∧
      (∀ i : Fin 3,
        final.getMem (Signing.wordAddress 0x81008 i.val) =
          (GroupedBalancedByteFastEdgeIndex67.indexState s).getMem
            (Signing.wordAddress 0x81008 i.val)) := by
  let indexed := GroupedBalancedByteFastEdgeIndex67.indexState s
  have first := GroupedBalancedByteFastEdgeIndex67.index_block s pc
  have indexedPC : indexed.pc = 0x17dc := by
    rw [GroupedBalancedByteFastEdgeIndex67.index_pc s pc]
    rw [index_side]
    exact if_neg side
  have indexedPtr : indexed.getMem 0x81048 = s.getMem 0x81048 :=
    GroupedBalancedByteFastEdgeIndex67.index_pointer_frame s
  have indexedLevel : indexed.getMem 0x81000 = BitVec.ofNat 64 level := by
    rw [index_mem s 0x81000 (by decide) (by decide)
      (by decide) (by decide)]
    exact hlevel
  have indexedRoot : ∀ half : Fin 2,
      indexed.getMem (Signing.wordAddress 0x80500 half.val) =
        current.extractLsb' (64*half.val) 64 := by
    intro half
    rw [index_mem s _ (by fin_cases half <;> decide)
      (by fin_cases half <;> decide) (by fin_cases half <;> decide)
      (by fin_cases half <;> decide)]
    exact root half
  have indexedWitness : ∀ half : Fin 2,
      indexed.getMem
        (indexed.getMem 0x81048 + BitVec.ofNat 64 (8*half.val)) =
        sibling.extractLsb' (64*half.val) 64 := by
    intro half
    rw [indexedPtr,index_low_frame s _ (low half)]
    exact witness half
  have indexedSeparate : ∀ half : Fin 2, ∀ i, i < 2 →
      indexed.getMem 0x81048 + BitVec.ofNat 64 (8*half.val) ≠
        Signing.wordAddress 0x80530 i := by
    intro half i hi
    rw [indexedPtr]
    exact low_ne_destination _ (low half) 0x80530 i (by decide)
      (by omega)
  obtain ⟨final,rest,done,result,ptr,count,levelCount,index⟩ :=
    GroupedBalancedByteFastSideAdvance67.right_advance hash indexed
      level tree sibling current indexedPC
      (by rw [indexedPtr]; exact ptr0)
      (by rw [indexedPtr]; exact ptr8)
      indexedLevel hindex indexedRoot indexedWitness indexedSeparate
  refine ⟨final,?_,done,result,?_,?_,?_,index⟩
  · have path := (OrdinarySteps.trace (hash := hash) first).trans rest
    simpa [indexed,GroupedBalancedByteFastEdgeIndex67.image] using path
  · rw [ptr,indexedPtr]
  · rw [count,index_mem s 0x81000 (by decide) (by decide)
      (by decide) (by decide)]
  · rw [levelCount,index_mem s 0x81050 (by decide) (by decide)
      (by decide) (by decide)]

#print axioms right_edge_advance

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeAdvance67
