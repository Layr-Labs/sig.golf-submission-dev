import SigGolfCandidate.Hypertree.GroupedBalancedByteFastIndexFields67
import SigGolfCandidate.Hypertree.SignShift
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeAdvance67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeIndexRefine67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeNat67. -/
section
/-! The verifier's three-word index shift implements 192-bit division by two. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeIndexRefine67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastIndexFields67
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

def StoredIndex (s : MachineState) (index : BitVec 192) : Prop :=
  ∀ i : Fin 3,
    s.getMem (Signing.wordAddress 0x81008 i.val) =
      index.extractLsb' (64*i.val) 64

theorem index_refines (s : MachineState) (index : BitVec 192)
    (stored : StoredIndex s index) :
    StoredIndex (GroupedBalancedByteFastEdgeIndex67.indexState s)
      (index >>> 1) := by
  have w0 : s.getMem 0x81008 = index.extractLsb' 0 64 := stored 0
  have w1 : s.getMem 0x81010 = index.extractLsb' 64 64 := stored 1
  have w2 : s.getMem 0x81018 = index.extractLsb' 128 64 := stored 2
  intro i
  fin_cases i
  · change (GroupedBalancedByteFastEdgeIndex67.indexState s).getMem
      0x81008 = _
    rw [index_low_word,w0,w1]
    exact Signing.shifted_limb index 0
  · change (GroupedBalancedByteFastEdgeIndex67.indexState s).getMem
      0x81010 = _
    rw [index_mid_word,w1,w2]
    exact Signing.shifted_limb index 1
  · change (GroupedBalancedByteFastEdgeIndex67.indexState s).getMem
      0x81018 = _
    rw [index_high_word,w2]
    exact Signing.shifted_high_limb index

private theorem shifted_index_nat (index : Nat) (small : index < 2^192) :
    (BitVec.ofNat 192 index >>> 1) = BitVec.ofNat 192 (index/2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  norm_num
  omega

theorem index_nat (s : MachineState) (index : Nat)
    (small : index < 2^192)
    (stored : StoredIndex s (BitVec.ofNat 192 index)) :
    StoredIndex (GroupedBalancedByteFastEdgeIndex67.indexState s)
      (BitVec.ofNat 192 (index/2)) := by
  have next := index_refines s (BitVec.ofNat 192 index) stored
  rw [shifted_index_nat index small] at next
  exact next

theorem side_toNat (s : MachineState) (index : BitVec 192)
    (stored : StoredIndex s index) :
    (s.getMem 0x81008 &&& (1 : Word)).toNat = index.toNat % 2 := by
  have w0 : s.getMem 0x81008 = index.extractLsb' 0 64 := stored 0
  rw [w0]
  simp [BitVec.toNat_and,BitVec.extractLsb'_toNat]

theorem side_zero_iff (s : MachineState) (index : BitVec 192)
    (stored : StoredIndex s index) :
    s.getMem 0x81008 &&& (1 : Word) = 0 ↔ index.toNat % 2 = 0 := by
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    rw [side_toNat s index stored] at hn
    simpa using hn
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [side_toNat s index stored,h]
    rfl

#print axioms index_refines
#print axioms index_nat
#print axioms side_toNat
#print axioms side_zero_iff

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeIndexRefine67

end

/-! A complete upper Merkle edge indexed by the reference natural coordinate. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeNat67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeIndexRefine67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def nextRoot (hash : Hash) (level treeIndex : Nat)
    (current sibling : Reference.Digest) : Reference.Digest :=
  if treeIndex % 2 = 0 then
    Reference.node hash level (treeIndex/2) current sibling
  else Reference.node hash level (treeIndex/2) sibling current

theorem edge_nat (hash : Hash) (s : MachineState)
    (level treeIndex : Nat)
    (current sibling : Reference.Digest)
    (pc : s.pc = 0x1758)
    (small : treeIndex < 2^192)
    (stored : StoredIndex s (BitVec.ofNat 192 treeIndex))
    (ptr0 : accessValid (s.getMem 0x81048) 8 = true)
    (ptr8 : accessValid (s.getMem 0x81048 + 8) 8 = true)
    (low : ∀ half : Fin 2,
      (s.getMem 0x81048 + BitVec.ofNat 64 (8*half.val)).toNat < 0x80020)
    (hlevel : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (root : ∀ half : Fin 2,
      s.getMem (Signing.wordAddress 0x80500 half.val) =
        current.extractLsb' (64*half.val) 64)
    (witness : ∀ half : Fin 2,
      s.getMem (s.getMem 0x81048 + BitVec.ofNat 64 (8*half.val)) =
        sibling.extractLsb' (64*half.val) 64) :
    ∃ final,
      Trace hash GroupedBalancedVerifyImage67Fast2Byte.image s
        (164+treeIndex%2) (171+treeIndex%2) 1 1 final ∧
      (final.pc = if final.getReg .x6 ≠ final.getReg .x7
        then 0x1758 else 0x19c4) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80500 i.val) =
          (nextRoot hash level treeIndex current sibling).extractLsb'
            (64*i.val) 64) ∧
      final.getMem 0x81048 = s.getMem 0x81048 + 16 ∧
      final.getMem 0x81000 = s.getMem 0x81000 + 1 ∧
      final.getMem 0x81050 = s.getMem 0x81050 + 1 ∧
      StoredIndex final (BitVec.ofNat 192 (treeIndex/2)) := by
  have shifted := index_nat s treeIndex small stored
  by_cases parity : treeIndex % 2 = 0
  · have parityBV : (BitVec.ofNat 192 treeIndex).toNat % 2 = 0 := by
      simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] using parity
    have side := (side_zero_iff s (BitVec.ofNat 192 treeIndex) stored).2
      parityBV
    obtain ⟨final,trace,done,value,ptr,count,levelCount,index⟩ :=
      GroupedBalancedByteFastEdgeAdvance67.left_edge_advance hash s
        level (treeIndex/2) current sibling pc side ptr0 ptr8 low hlevel shifted
        root witness
    refine ⟨final,?_,done,?_,ptr,count,levelCount,?_⟩
    · simpa [parity] using trace
    · intro i
      simpa [nextRoot,parity] using value i
    · intro i
      rw [index i]
      exact shifted i
  · have side : s.getMem 0x81008 &&& (1 : Word) ≠ 0 := by
      intro eq
      have hv := (side_zero_iff s (BitVec.ofNat 192 treeIndex)
        stored).1 eq
      have hn : treeIndex % 2 = 0 := by
        simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] using hv
      exact parity hn
    have one : treeIndex % 2 = 1 := by omega
    obtain ⟨final,trace,done,value,ptr,count,levelCount,index⟩ :=
      GroupedBalancedByteFastEdgeAdvance67.right_edge_advance hash s
        level (treeIndex/2) current sibling pc side ptr0 ptr8 low hlevel shifted
        root witness
    refine ⟨final,?_,done,?_,ptr,count,levelCount,?_⟩
    · simpa [one] using trace
    · intro i
      simpa [nextRoot,parity] using value i
    · intro i
      rw [index i]
      exact shifted i

#print axioms edge_nat

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeNat67
