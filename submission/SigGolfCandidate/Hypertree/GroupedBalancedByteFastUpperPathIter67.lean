import SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeCarry67

/-! Induction across every edge in one height-three or height-four upper path. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastUpperPathIter67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeIndexRefine67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeNat67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

def ptrAt (base n : Nat) : Word := BitVec.ofNat 64 (base + 16*n)
def countAt (n : Nat) : Word := BitVec.ofNat 64 n
def indexAt (index n : Nat) : Nat := index / 2^n

def rootAt (hash : Hash) (level index : Nat)
    (initial : Reference.Digest) (siblings : Nat → Reference.Digest) :
    Nat → Reference.Digest
  | 0 => initial
  | n+1 => nextRoot hash (level+n) (indexAt index n)
      (rootAt hash level index initial siblings n) (siblings n)

theorem ptr_next (base n : Nat) :
    ptrAt base n + 16 = ptrAt base (n+1) := by
  simp [ptrAt,Nat.mul_add,BitVec.ofNat_add]
  ac_rfl

theorem count_next (n : Nat) : countAt n + 1 = countAt (n+1) := by
  simp [countAt,BitVec.ofNat_add]

theorem level_next (level n : Nat) :
    BitVec.ofNat 64 (level+n) + 1 = BitVec.ofNat 64 (level+(n+1)) := by
  simp [BitVec.ofNat_add]
  ac_rfl

theorem index_next (index n : Nat) :
    indexAt index n / 2 = indexAt index (n+1) := by
  simp [indexAt,pow_succ,Nat.div_div_eq_div_mul]

theorem index_small (index n : Nat) (small : index < 2^192) :
    indexAt index n < 2^192 := by
  unfold indexAt
  exact lt_of_le_of_lt (Nat.div_le_self _ _) small

private theorem ptr_nat (base n half : Nat)
  (bound : base + 16*(n+1) ≤ 0x38da0) (hhalf : half < 2) :
    (ptrAt base n + BitVec.ofNat 64 (8*half)).toNat =
      base + 16*n + 8*half := by
  rw [ptrAt,← BitVec.ofNat_add]
  have small : base + 16*n + 8*half < 2^64 := by omega
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]

theorem ptr_valid0 (base n : Nat)
    (aligned : base % 8 = 0)
    (bound : base + 16*(n+1) ≤ 0x38da0) :
    accessValid (ptrAt base n) 8 = true := by
  have small : base+16*n < 2^64 := by omega
  have nat : (ptrAt base n).toNat = base+16*n := by
    change (base+16*n) % 2^64 = base+16*n
    exact Nat.mod_eq_of_lt small
  unfold accessValid rangeValid
  rw [nat]
  have align : (base+16*n)%8 = 0 := by omega
  simp [align,MEMORY_BYTES]
  omega

theorem ptr_valid8 (base n : Nat)
    (aligned : base % 8 = 0)
    (bound : base + 16*(n+1) ≤ 0x38da0) :
    accessValid (ptrAt base n + 8) 8 = true := by
  have nat : (ptrAt base n + 8).toNat = base+16*n+8 := by
    simpa using ptr_nat base n 1 bound (by decide)
  unfold accessValid rangeValid
  rw [nat]
  have align : (base+16*n+8)%8 = 0 := by omega
  simp [align,MEMORY_BYTES]
  omega

theorem ptr_low (base n : Nat)
    (bound : base + 16*(n+1) ≤ 0x38da0) :
    ∀ half : Fin 2,
      (ptrAt base n + BitVec.ofNat 64 (8*half.val)).toNat < 0x80000 := by
  intro half
  rw [ptr_nat base n half.val bound half.isLt]
  omega

theorem ptr_word (base n : Nat) (half : Fin 2) :
    ptrAt base n + BitVec.ofNat 64 (8*half.val) =
      BitVec.ofNat 64 (base+16*n+8*half.val) := by
  simp [ptrAt,←BitVec.ofNat_add]

theorem count_branch (n h : Nat) (hn : n < h) (hh : h ≤ 4) :
    (if countAt n + 1 ≠ countAt h then (0x1758 : Word) else 0x19c4) =
      (if n+1 = h then 0x19c4 else 0x1758) := by
  interval_cases h <;> interval_cases n <;> decide

theorem run_path (hash : Hash) (s : MachineState)
    (base level index h n : Nat)
    (initial : Reference.Digest)
    (siblings : Nat → Reference.Digest)
    (hn : n ≤ h) (hh : h = 3 ∨ h = 4)
    (aligned : base % 8 = 0)
    (baseBound : base + 16*h ≤ 0x38da0)
    (levelBound : level+h < 2^64)
    (indexBound : index < 2^192)
    (pc : s.pc = 0x1758)
    (ptr : s.getMem 0x81048 = ptrAt base 0)
    (count : s.getMem 0x81050 = countAt 0)
    (limit : s.getMem 0x81060 = countAt h)
    (levelMem : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (stored : StoredIndex s (BitVec.ofNat 192 index))
    (root : ∀ half : Fin 2,
      s.getMem (Signing.wordAddress 0x80500 half.val) =
        initial.extractLsb' (64*half.val) 64)
    (witness : ∀ j, j < h → ∀ half : Fin 2,
      s.getMem (BitVec.ofNat 64 (base+16*j+8*half.val)) =
        (siblings j).extractLsb' (64*half.val) 64) :
    ∃ final steps cycles,
      Trace hash image s steps cycles n n final ∧
      final.pc = (if n = h then 0x19c4 else 0x1758) ∧
      final.getMem 0x81048 = ptrAt base n ∧
      final.getMem 0x81050 = countAt n ∧
      final.getMem 0x81060 = countAt h ∧
      final.getMem 0x81000 = BitVec.ofNat 64 (level+n) ∧
      StoredIndex final (BitVec.ofNat 192 (indexAt index n)) ∧
      (∀ half : Fin 2,
        final.getMem (Signing.wordAddress 0x80500 half.val) =
          (rootAt hash level index initial siblings n).extractLsb'
              (64*half.val) 64) ∧
      final.getMem 0x81058 = s.getMem 0x81058 ∧
      (∀ a : Word, a.toNat < 0x80000 → final.getMem a = s.getMem a) ∧
      (∀ a : Word, 0xfff700 ≤ a.toNat → final.getMem a = s.getMem a) ∧
      steps ≤ 165*n ∧ cycles ≤ 172*n := by
  induction n with
  | zero =>
    refine ⟨s,0,0,Trace.refl s,?_,ptr,count,limit,?_,?_,?_,rfl,?_,?_,by omega,by omega⟩
    · rcases hh with rfl | rfl <;> simpa using pc
    · simpa using levelMem
    · simpa [indexAt] using stored
    · simpa [rootAt] using root
    · intro a _; rfl
    · intro a _; rfl
  | succ n ih =>
    have less : n < h := by omega
    have h4 : h ≤ 4 := by rcases hh with rfl | rfl <;> omega
    obtain ⟨mid,steps,cycles,path,midPc,midPtr,midCount,midLimit,
      midLevel,midIndex,midRoot,midGroup,midFrame,midHigh,stepsBound,cyclesBound⟩ :=
      ih (by omega)
    have edgePC : mid.pc = 0x1758 := by
      simpa [show n ≠ h by omega] using midPc
    have currentBound : base+16*(n+1) ≤ 0x38da0 := by omega
    have v0 : accessValid (mid.getMem 0x81048) 8 = true := by
      rw [midPtr]
      exact ptr_valid0 base n aligned currentBound
    have v8 : accessValid (mid.getMem 0x81048 + 8) 8 = true := by
      rw [midPtr]
      exact ptr_valid8 base n aligned currentBound
    have low : ∀ half : Fin 2,
        (mid.getMem 0x81048 + BitVec.ofNat 64 (8*half.val)).toNat <
          0x80000 := by
      rw [midPtr]
      exact ptr_low base n currentBound
    have siblingWords : ∀ half : Fin 2,
        mid.getMem (mid.getMem 0x81048 +
          BitVec.ofNat 64 (8*half.val)) =
          (siblings n).extractLsb' (64*half.val) 64 := by
      intro half
      have addrLow :
          (BitVec.ofNat 64 (base+16*n+8*half.val)).toNat < 0x80000 := by
        rw [←ptr_word]
        exact ptr_low base n currentBound half
      rw [midPtr,ptr_word,midFrame _ addrLow]
      exact witness n less half
    obtain ⟨final,edge,finalPc,finalRoot,finalPtr,finalLevel,
      finalCount,finalIndex,finalLimit,finalGroup,finalFrame,finalHigh⟩ :=
      GroupedBalancedByteFastEdgeCarry67.edge_nat_carry hash mid
        (level+n) (indexAt index n)
        (rootAt hash level index initial siblings n) (siblings n)
        edgePC (index_small index n indexBound) midIndex v0 v8 low
        midLevel midRoot siblingWords
    refine ⟨final,steps+(164+indexAt index n%2),
      cycles+(171+indexAt index n%2),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [Nat.succ_eq_add_one,Nat.add_zero] using path.trans edge
    · rw [finalPc,midCount,midLimit,count_branch n h less h4]
    · rw [finalPtr,midPtr,ptr_next]
    · rw [finalCount,midCount,count_next]
    · exact finalLimit.trans midLimit
    · rw [finalLevel,midLevel,level_next]
    · simpa [index_next] using finalIndex
    · simpa [rootAt] using finalRoot
    · rw [finalGroup,midGroup]
    · intro a aLow
      rw [finalFrame a aLow,midFrame a aLow]
    · intro a aHigh
      rw [finalHigh a aHigh,midHigh a aHigh]
    · omega
    · omega

#print axioms run_path

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastUpperPathIter67
