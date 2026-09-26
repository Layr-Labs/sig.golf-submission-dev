import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootOneNode67
import SigGolfCandidate.Hypertree.GroupedBalancedUpperTree67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootNodes67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootFold67. -/
section
/-! Functional induction over the parent hashes of one keygen Merkle level. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootNodes67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 16384
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedKeygenImage67.image
private abbrev root := GroupedBalancedUpperTree67.root

theorem table_word_nat (b j : Nat) (i : Fin 2)
    (bCase : b = 0x82000 ∨ b = 0x82100) (jBound : j < 16) :
    (Signing.wordAddress (b+16*j) i.val).toNat = b+16*j+8*i.val := by
  simp [Signing.wordAddress,BitVec.toNat_ofNat]
  rcases bCase with rfl | rfl <;> omega

theorem table_word_high (b j : Nat) (i : Fin 2)
    (bCase : b = 0x82000 ∨ b = 0x82100) (jBound : j < 16) :
    0x82000 ≤ (Signing.wordAddress (b+16*j) i.val).toNat := by
  rw [table_word_nat b j i bCase jBound]
  rcases bCase with rfl | rfl <;> omega

theorem children_of_table (hash : Hash) (secretKey : SecretKey)
    (s : MachineState) (base ell k n src : Nat)
    (nBound : n < k) (kBound : k ≤ 8)
    (table : ∀ j : Nat, j < 2*k → ∀ i : Fin 2,
      s.getMem (Signing.wordAddress (src+16*j) i.val) =
        (root hash secretKey base ell j).extractLsb' (64*i.val) 64) :
    ∀ i : Fin 4,
      s.getMem (Signing.wordAddress (src+32*n) i.val) =
        if i.val < 2 then
          (root hash secretKey base ell (2*n)).extractLsb' (64*i.val) 64
        else
          (root hash secretKey base ell (2*n+1)).extractLsb' (64*(i.val-2)) 64 := by
  intro i
  fin_cases i
  · simpa [Signing.wordAddress,
      show src+16*(2*n)=src+32*n by omega] using table (2*n) (by omega) 0
  · simpa [Signing.wordAddress,
      show src+16*(2*n)=src+32*n by omega] using table (2*n) (by omega) 1
  · simpa [Signing.wordAddress,
      show src+16*(2*n+1)=src+32*n+16 by omega] using
      table (2*n+1) (by omega) 0
  · simpa [Signing.wordAddress,
      show src+16*(2*n+1)=src+32*n+16 by omega] using
      table (2*n+1) (by omega) 1

theorem table_disjoint (src dst j k : Nat) (i : Fin 2)
    (srcCase : src = 0x82000 ∨ src = 0x82100)
    (dstCase : dst = 0x82000 ∨ dst = 0x82100)
    (different : src ≠ dst) (jBound : j < 16) (kBound : k ≤ 8) :
    (Signing.wordAddress (src+16*j) i.val).toNat < dst ∨
      dst+16*k ≤ (Signing.wordAddress (src+16*j) i.val).toNat := by
  rw [table_word_nat src j i srcCase jBound]
  rcases srcCase with rfl | rfl <;> rcases dstCase with rfl | rfl <;> omega

theorem output_node (hash : Hash) (secretKey : SecretKey) (base ell n : Nat) :
    Reference.node hash (base+ell) n
      (root hash secretKey base ell (2*n))
      (root hash secretKey base ell (2*n+1)) =
    root hash secretKey base (ell+1) n := by
  rfl

theorem tree_index_words (n : Nat) (nBound : n < 8) :
    (BitVec.ofNat 192 n).extractLsb' 0 64 = BitVec.ofNat 64 n ∧
    (BitVec.ofNat 192 n).extractLsb' 64 64 = 0#64 ∧
    (BitVec.ofNat 192 n).extractLsb' 128 64 = 0#64 := by
  have nRange : n < 6277101735386680763835789423207666416102355444464034512896 := by omega
  constructor
  · simp only [BitVec.extractLsb',BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt nRange]
    simp
  constructor
  · have shift : n >>> 64 = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      omega
    simp only [BitVec.extractLsb',BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt nRange,shift]
  · have shift : n >>> 128 = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      omega
    simp only [BitVec.extractLsb',BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt nRange,shift]

theorem interval_frame (s t : MachineState) (dst n : Nat)
    (dstCase : dst = 0x82000 ∨ dst = 0x82100) (nBound : n < 8)
    (frame : ∀ a : Word, 0x82000 ≤ a.toNat →
      a ≠ Signing.wordAddress (dst+16*n) 0 →
      a ≠ Signing.wordAddress (dst+16*n) 1 → t.getMem a = s.getMem a)
    (a : Word) (high : 0x82000 ≤ a.toNat)
    (outside : a.toNat < dst+16*n ∨ dst+16*(n+1) ≤ a.toNat) :
    t.getMem a = s.getMem a := by
  apply frame a high
  · intro eq
    have hn := congrArg BitVec.toNat eq
    have wordNat : (Signing.wordAddress (dst+16*n) 0).toNat = dst+16*n := by
      simpa using table_word_nat dst n (0 : Fin 2) dstCase (by omega)
    rw [wordNat] at hn
    omega
  · intro eq
    have hn := congrArg BitVec.toNat eq
    have wordNat : (Signing.wordAddress (dst+16*n) 1).toNat = dst+16*n+8 := by
      simpa using table_word_nat dst n (1 : Fin 2) dstCase (by omega)
    rw [wordNat] at hn
    omega

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootNodes67

end

/-! The direct67 H4 keygen node loop computes an entire reference tree level. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenRootNodes67
set_option maxRecDepth 16384
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedKeygenImage67.image
private abbrev root := GroupedBalancedUpperTree67.root

theorem nodes_values (hash : Hash) (secretKey : SecretKey)
    (s : MachineState) (base ell n rem src dst : Nat)
    (pc : s.pc = 0x1480) (positive : 0 < rem) (bound : n+rem ≤ 8)
    (srcCase : src = 0x82000 ∨ src = 0x82100)
    (dstCase : dst = 0x82000 ∨ dst = 0x82100)
    (different : src ≠ dst)
    (index : s.getMem 0x81040#64 = BitVec.ofNat 64 n)
    (count : s.getMem 0x81070#64 = BitVec.ofNat 64 (n+rem))
    (source : s.getMem 0x81078#64 = BitVec.ofNat 64 src)
    (destination : s.getMem 0x81080#64 = BitVec.ofNat 64 dst)
    (levelWord : s.getMem 0x81000 = BitVec.ofNat 64 (base+ell))
    (index1 : s.getMem 0x81010 = 0#64)
    (index2 : s.getMem 0x81018 = 0#64)
    (table : ∀ j : Nat, j < 2*(n+rem) → ∀ i : Fin 2,
      s.getMem (Signing.wordAddress (src+16*j) i.val) =
        (root hash secretKey base ell j).extractLsb' (64*i.val) 64) :
    ∃ final,
      Trace hash image s (79*rem) (86*rem) rem rem final ∧
      final.pc = 0x15bc ∧
      final.getMem 0x81040#64 = BitVec.ofNat 64 (n+rem) ∧
      (∀ a : Word, 0x81000 ≤ a.toNat → a.toNat < 0x82000 →
        a ≠ 0x81008#64 → a ≠ 0x81040#64 → final.getMem a = s.getMem a) ∧
      (∀ j : Nat, n ≤ j → j < n+rem → ∀ i : Fin 2,
        final.getMem (Signing.wordAddress (dst+16*j) i.val) =
          (root hash secretKey base (ell+1) j).extractLsb' (64*i.val) 64) ∧
      (∀ a : Word, 0x82000 ≤ a.toNat →
        (a.toNat < dst+16*n ∨ dst+16*(n+rem) ≤ a.toNat) →
        final.getMem a = s.getMem a) := by
  induction rem generalizing s n with
  | zero => omega
  | succ t ih =>
      have nBound : n < 8 := by omega
      have words := tree_index_words n nBound
      have index0 : s.getMem 0x81040 =
          (BitVec.ofNat 192 n).extractLsb' 0 64 := by
        have lit : (0x81040#64 : Word) = (0x81040 : Word) := by decide
        rw [←lit,index,words.1]
      have children := children_of_table hash secretKey s base ell (n+t+1)
        n src (by omega) (by omega) (by
          intro j jBound i
          exact table j (by omega) i)
      obtain ⟨mid,first,midPC,midIndex,midLow,midOutput,midHigh⟩ :=
        GroupedBalancedKeygenRootOneNode67.one_node_values hash s
          n (n+t+1) src dst (base+ell) n
          (root hash secretKey base ell (2*n))
          (root hash secretKey base ell (2*n+1))
          pc (by omega) (by omega) srcCase dstCase index
          (by simpa only [Nat.add_assoc] using count) source destination
          levelWord index0 (by simpa [words.2.1] using index1)
          (by simpa [words.2.2] using index2) children
      have firstFrame (a : Word) (high : 0x82000 ≤ a.toNat)
          (outside : a.toNat < dst+16*n ∨ dst+16*(n+1) ≤ a.toNat) :
          mid.getMem a = s.getMem a :=
        interval_frame s mid dst n dstCase nBound midHigh a high outside
      have midTable : ∀ j : Nat, j < 2*(n+1+t) → ∀ i : Fin 2,
          mid.getMem (Signing.wordAddress (src+16*j) i.val) =
            (root hash secretKey base ell j).extractLsb' (64*i.val) 64 := by
        intro j jBound i
        have disj := table_disjoint src dst j (n+t+1) i srcCase dstCase
          different (by omega) (by omega)
        have frame := firstFrame (Signing.wordAddress (src+16*j) i.val)
          (table_word_high src j i srcCase (by omega)) (by omega)
        rw [frame]
        exact table j (by omega) i
      by_cases last : t = 0
      · subst t
        refine ⟨mid,?_,?_,?_,midLow,?_,?_⟩
        · simpa only [Nat.reduceMul,Nat.mul_one,Nat.reduceAdd] using first
        · simpa [midPC]
        · simpa [Nat.add_assoc] using midIndex
        · intro j jLow jHigh i
          have jEq : j=n := by omega
          subst j
          rw [midOutput i,output_node]
        · intro a high outside
          exact firstFrame a high (by omega)
      · have midPC' : mid.pc = 0x1480 := by simpa [last] using midPC
        have midCount : mid.getMem 0x81070#64 = BitVec.ofNat 64 ((n+1)+t) := by
          rw [midLow 0x81070#64 (by decide) (by decide) (by decide) (by decide)]
          simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using count
        have midSrc : mid.getMem 0x81078#64 = BitVec.ofNat 64 src := by
          rw [midLow 0x81078#64 (by decide) (by decide) (by decide) (by decide)]
          exact source
        have midDst : mid.getMem 0x81080#64 = BitVec.ofNat 64 dst := by
          rw [midLow 0x81080#64 (by decide) (by decide) (by decide) (by decide)]
          exact destination
        have midLevel : mid.getMem 0x81000 = BitVec.ofNat 64 (base+ell) := by
          rw [midLow 0x81000 (by decide) (by decide) (by decide) (by decide)]
          exact levelWord
        have midIndex1 : mid.getMem 0x81010 = 0#64 := by
          rw [midLow 0x81010 (by decide) (by decide) (by decide) (by decide)]
          exact index1
        have midIndex2 : mid.getMem 0x81018 = 0#64 := by
          rw [midLow 0x81018 (by decide) (by decide) (by decide) (by decide)]
          exact index2
        obtain ⟨final,second,finalPC,finalIndex,finalLow,finalOutput,finalHigh⟩ :=
          ih mid (n+1) midPC' (by omega) (by omega) midIndex
            midCount midSrc midDst midLevel midIndex1 midIndex2 midTable
        refine ⟨final,?_,finalPC,?_,?_,?_,?_⟩
        · simpa only [Nat.mul_succ,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
            using first.trans second
        · have arith : n+1+t = n+(t+1) := by omega
          rw [arith] at finalIndex
          exact finalIndex
        · intro a high low ne08 ne40
          rw [finalLow a high low ne08 ne40,midLow a high low ne08 ne40]
        · intro j jLow jHigh i
          by_cases firstJ : j=n
          · subst j
            have high := table_word_high dst n i dstCase (by omega)
            have wordNat := table_word_nat dst n i dstCase (by omega)
            rw [finalHigh (Signing.wordAddress (dst+16*n) i.val) high
              (by rw [wordNat]; left; omega),midOutput i,output_node]
          · have h := finalOutput j (by omega) (by omega) i
            simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
        · intro a high outside
          rw [finalHigh a high (by omega),firstFrame a high (by omega)]

#print axioms nodes_values
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootFold67
