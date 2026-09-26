import SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdge67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastIndexFields67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeProgress67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastArrangedCarry67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeNat67
import SigGolfCandidate.TraceDeterminism


/-! One upper Merkle edge, with its exact side-dependent resource charge. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeStep67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

def rightBit (s : MachineState) : Nat :=
  if s.getMem 0x81008 &&& 1 = (0 : Word) then 0 else 1

theorem rightBit_le (s : MachineState) : rightBit s ≤ 1 := by
  unfold rightBit
  split_ifs <;> omega

theorem edge_step (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1758)
    (ptr0 : accessValid (s.getMem 0x81048) 8 = true)
    (ptr8 : accessValid (s.getMem 0x81048 + 8) 8 = true) :
    ∃ final,
      Trace hash GroupedBalancedVerifyImage67Fast2Byte.image s
        (164 + rightBit s) (171 + rightBit s) 1 1 final ∧
      final.pc = if final.getReg .x6 ≠ final.getReg .x7
        then 0x1758 else 0x19c4 := by
  by_cases side : s.getMem 0x81008 &&& 1 = (0 : Word)
  · have mapped :
        (GroupedBalancedByteFastEdgeIndex67.indexState s).getReg .x6 = 0 := by
      rw [GroupedBalancedByteFastIndexFields67.index_side, side]
    obtain ⟨final,trace,done⟩ := GroupedBalancedByteFastEdge67.left_edge
      hash s pc mapped ptr0 ptr8
    have bit : rightBit s = 0 := by
      unfold rightBit
      exact if_pos side
    refine ⟨final,?_,done⟩
    rw [bit]
    simpa [GroupedBalancedByteFastEdge67.image] using trace
  · have mapped :
        (GroupedBalancedByteFastEdgeIndex67.indexState s).getReg .x6 ≠ 0 := by
      rw [GroupedBalancedByteFastIndexFields67.index_side]
      exact side
    obtain ⟨final,trace,done⟩ := GroupedBalancedByteFastEdge67.right_edge
      hash s pc mapped ptr0 ptr8
    have bit : rightBit s = 1 := by
      unfold rightBit
      exact if_neg side
    refine ⟨final,?_,done⟩
    rw [bit]
    simpa [GroupedBalancedByteFastEdge67.image] using trace

#print axioms edge_step

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeStep67


/-! Counter and immutable witness carry over a full upper Merkle edge. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeCarry67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeIndexRefine67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private theorem low_ne_destination (a : Word)
    (low : a.toNat < 0x80000) (base i : Nat)
    (high : 0x80000 ≤ base) (small : base+8*i < 2^64) :
    a ≠ Signing.wordAddress base i := by
  intro eq
  have h := congrArg BitVec.toNat eq
  simp only [Signing.wordAddress,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small] at h
  omega

theorem edge_control (hash : Hash) (s : MachineState)
    (level tree : Nat) (current sibling : Reference.Digest)
    (pc : s.pc = 0x1758)
    (ptr0 : accessValid (s.getMem 0x81048) 8 = true)
    (ptr8 : accessValid (s.getMem 0x81048 + 8) 8 = true)
    (low : ∀ half : Fin 2,
      (s.getMem 0x81048 + BitVec.ofNat 64 (8*half.val)).toNat < 0x80000)
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
        (164 + GroupedBalancedByteFastEdgeStep67.rightBit s)
        (171 + GroupedBalancedByteFastEdgeStep67.rightBit s) 1 1 final ∧
      (final.pc = if s.getMem 0x81050 + 1 ≠ s.getMem 0x81060
        then 0x1758 else 0x19c4) ∧
      final.getMem 0x81060 = s.getMem 0x81060 ∧
      final.getMem 0x81058 = s.getMem 0x81058 ∧
      (∀ a : Word, a.toNat < 0x80000 → final.getMem a = s.getMem a) ∧
      (∀ a : Word, 0xfff700 ≤ a.toNat → final.getMem a = s.getMem a) := by
  let indexed := GroupedBalancedByteFastEdgeIndex67.indexState s
  have first := GroupedBalancedByteFastEdgeIndex67.index_block s pc
  have indexedPtr : indexed.getMem 0x81048 = s.getMem 0x81048 :=
    GroupedBalancedByteFastEdgeIndex67.index_pointer_frame s
  have indexedLevel : indexed.getMem 0x81000 = BitVec.ofNat 64 level := by
    rw [GroupedBalancedByteFastIndexFields67.index_mem s 0x81000
      (by decide) (by decide) (by decide) (by decide)]
    exact hlevel
  have indexedRoot : ∀ half : Fin 2,
      indexed.getMem (Signing.wordAddress 0x80500 half.val) =
        current.extractLsb' (64*half.val) 64 := by
    intro half
    rw [GroupedBalancedByteFastIndexFields67.index_mem s _
      (by fin_cases half <;> decide) (by fin_cases half <;> decide)
      (by fin_cases half <;> decide) (by fin_cases half <;> decide)]
    exact root half
  have indexedWitness : ∀ half : Fin 2,
      indexed.getMem
        (indexed.getMem 0x81048 + BitVec.ofNat 64 (8*half.val)) =
        sibling.extractLsb' (64*half.val) 64 := by
    intro half
    rw [indexedPtr,GroupedBalancedByteFastIndexFields67.index_low_frame s _
      (by have := low half; omega)]
    exact witness half
  have carryHigh (a : Word) (ne0 : a ≠ 0x81008)
      (ne1 : a ≠ 0x81010) (ne2 : a ≠ 0x81018)
      (ne3 : a ≠ 0x81020) : indexed.getMem a = s.getMem a :=
    GroupedBalancedByteFastIndexFields67.index_mem s a ne0 ne1 ne2 ne3
  have carryLow (a : Word) (aLow : a.toNat < 0x80000) :
      indexed.getMem a = s.getMem a :=
    GroupedBalancedByteFastIndexFields67.index_low_frame s a (by omega)
  by_cases side : s.getMem 0x81008 &&& 1 = (0 : Word)
  · have indexedPC : indexed.pc = 0x1830 := by
      rw [GroupedBalancedByteFastEdgeIndex67.index_pc s pc]
      rw [GroupedBalancedByteFastIndexFields67.index_side]
      exact if_pos side
    have separate : ∀ half : Fin 2, ∀ i, i < 2 →
        indexed.getMem 0x81048 + BitVec.ofNat 64 (8*half.val) ≠
          Signing.wordAddress 0x80520 i := by
      intro half i hi
      rw [indexedPtr]
      exact low_ne_destination _ (low half) 0x80520 i (by decide)
        (by omega)
    obtain ⟨final,rest,done,limit,group,lowFrame,highFrame⟩ :=
      GroupedBalancedByteFastArrangedCarry67.left_side_carry hash indexed
        level tree current sibling indexedPC
        (by rw [indexedPtr]; exact ptr0)
        (by rw [indexedPtr]; exact ptr8)
        indexedLevel hindex indexedRoot indexedWitness separate
    refine ⟨final,?_,?_,?_,?_,?_,?_⟩
    · have path := (OrdinarySteps.trace (hash := hash) first).trans rest
      have bit : GroupedBalancedByteFastEdgeStep67.rightBit s = 0 := by
        unfold GroupedBalancedByteFastEdgeStep67.rightBit
        exact if_pos side
      simpa [indexed,GroupedBalancedByteFastEdgeIndex67.image,bit] using path
    · rw [done,carryHigh 0x81050 (by decide) (by decide) (by decide)
        (by decide),carryHigh 0x81060 (by decide) (by decide) (by decide)
        (by decide)]
    · rw [limit,carryHigh 0x81060 (by decide) (by decide) (by decide)
        (by decide)]
    · rw [group,carryHigh 0x81058 (by decide) (by decide) (by decide)
        (by decide)]
    · intro a aLow
      rw [lowFrame a aLow,carryLow a aLow]
    · intro a aHigh
      rw [highFrame a aHigh]
      have disjoint (b : Word) (small : b.toNat < 0xfff700) : a ≠ b := by
        intro eq
        have h := congrArg BitVec.toNat eq
        omega
      exact carryHigh a
        (disjoint 0x81008 (by decide))
        (disjoint 0x81010 (by decide))
        (disjoint 0x81018 (by decide))
        (disjoint 0x81020 (by decide))
  · have indexedPC : indexed.pc = 0x17dc := by
      rw [GroupedBalancedByteFastEdgeIndex67.index_pc s pc]
      rw [GroupedBalancedByteFastIndexFields67.index_side]
      exact if_neg side
    have separate : ∀ half : Fin 2, ∀ i, i < 2 →
        indexed.getMem 0x81048 + BitVec.ofNat 64 (8*half.val) ≠
          Signing.wordAddress 0x80530 i := by
      intro half i hi
      rw [indexedPtr]
      exact low_ne_destination _ (low half) 0x80530 i (by decide)
        (by omega)
    obtain ⟨final,rest,done,limit,group,lowFrame,highFrame⟩ :=
      GroupedBalancedByteFastArrangedCarry67.right_side_carry hash indexed
        level tree sibling current indexedPC
        (by rw [indexedPtr]; exact ptr0)
        (by rw [indexedPtr]; exact ptr8)
        indexedLevel hindex indexedRoot indexedWitness separate
    refine ⟨final,?_,?_,?_,?_,?_,?_⟩
    · have path := (OrdinarySteps.trace (hash := hash) first).trans rest
      have bit : GroupedBalancedByteFastEdgeStep67.rightBit s = 1 := by
        unfold GroupedBalancedByteFastEdgeStep67.rightBit
        exact if_neg side
      simpa [indexed,GroupedBalancedByteFastEdgeIndex67.image,bit] using path
    · rw [done,carryHigh 0x81050 (by decide) (by decide) (by decide)
        (by decide),carryHigh 0x81060 (by decide) (by decide) (by decide)
        (by decide)]
    · rw [limit,carryHigh 0x81060 (by decide) (by decide) (by decide)
        (by decide)]
    · rw [group,carryHigh 0x81058 (by decide) (by decide) (by decide)
        (by decide)]
    · intro a aLow
      rw [lowFrame a aLow,carryLow a aLow]
    · intro a aHigh
      rw [highFrame a aHigh]
      have disjoint (b : Word) (small : b.toNat < 0xfff700) : a ≠ b := by
        intro eq
        have h := congrArg BitVec.toNat eq
        omega
      exact carryHigh a
        (disjoint 0x81008 (by decide))
        (disjoint 0x81010 (by decide))
        (disjoint 0x81018 (by decide))
        (disjoint 0x81020 (by decide))

theorem rightBit_nat (s : MachineState) (treeIndex : Nat)
    (small : treeIndex < 2^192)
    (stored : StoredIndex s (BitVec.ofNat 192 treeIndex)) :
    GroupedBalancedByteFastEdgeStep67.rightBit s = treeIndex % 2 := by
  by_cases parity : treeIndex % 2 = 0
  · have side : s.getMem 0x81008 &&& (1 : Word) = 0 :=
      (side_zero_iff s (BitVec.ofNat 192 treeIndex) stored).2
        (by simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] using parity)
    rw [parity]
    unfold GroupedBalancedByteFastEdgeStep67.rightBit
    exact if_pos side
  · have side : s.getMem 0x81008 &&& (1 : Word) ≠ 0 := by
      intro eq
      have hv := (side_zero_iff s (BitVec.ofNat 192 treeIndex)
        stored).1 eq
      have hn : treeIndex % 2 = 0 := by
        simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] using hv
      exact parity hn
    have one : treeIndex % 2 = 1 := by omega
    rw [one]
    unfold GroupedBalancedByteFastEdgeStep67.rightBit
    exact if_neg side

theorem edge_nat_carry (hash : Hash) (s : MachineState)
    (level treeIndex : Nat)
    (current sibling : Reference.Digest)
    (pc : s.pc = 0x1758)
    (small : treeIndex < 2^192)
    (stored : StoredIndex s (BitVec.ofNat 192 treeIndex))
    (ptr0 : accessValid (s.getMem 0x81048) 8 = true)
    (ptr8 : accessValid (s.getMem 0x81048 + 8) 8 = true)
    (low : ∀ half : Fin 2,
      (s.getMem 0x81048 + BitVec.ofNat 64 (8*half.val)).toNat < 0x80000)
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
      (final.pc = if s.getMem 0x81050 + 1 ≠ s.getMem 0x81060
        then 0x1758 else 0x19c4) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80500 i.val) =
          (GroupedBalancedByteFastEdgeNat67.nextRoot hash level treeIndex
            current sibling).extractLsb' (64*i.val) 64) ∧
      final.getMem 0x81048 = s.getMem 0x81048 + 16 ∧
      final.getMem 0x81000 = s.getMem 0x81000 + 1 ∧
      final.getMem 0x81050 = s.getMem 0x81050 + 1 ∧
      StoredIndex final (BitVec.ofNat 192 (treeIndex/2)) ∧
      final.getMem 0x81060 = s.getMem 0x81060 ∧
      final.getMem 0x81058 = s.getMem 0x81058 ∧
      (∀ a : Word, a.toNat < 0x80000 → final.getMem a = s.getMem a) ∧
      (∀ a : Word, 0xfff700 ≤ a.toNat → final.getMem a = s.getMem a) := by
  have shifted := index_nat s treeIndex small stored
  obtain ⟨final,trace,_,value,ptr,levelCount,edgeCount,index⟩ :=
    GroupedBalancedByteFastEdgeNat67.edge_nat hash s level treeIndex
      current sibling pc small stored ptr0 ptr8
      (by intro half; have := low half; omega) hlevel root witness
  obtain ⟨control,controlTrace,controlPC,limit,group,lowFrame,highFrame⟩ :=
    edge_control hash s level (treeIndex/2) current sibling
      pc ptr0 ptr8 low hlevel shifted root witness
  have controlTrace' : Trace hash
      GroupedBalancedVerifyImage67Fast2Byte.image s
      (164+treeIndex%2) (171+treeIndex%2) 1 1 control := by
    simpa [rightBit_nat s treeIndex small stored] using controlTrace
  have eq := Trace.deterministic trace controlTrace'
  subst control
  exact ⟨final,trace,controlPC,value,ptr,levelCount,edgeCount,index,
    limit,group,lowFrame,highFrame⟩

#print axioms edge_control
#print axioms rightBit_nat
#print axioms edge_nat_carry

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeCarry67
