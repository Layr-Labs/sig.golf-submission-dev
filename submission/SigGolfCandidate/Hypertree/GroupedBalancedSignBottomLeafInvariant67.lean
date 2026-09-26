import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomAddressStep67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomStackSlots67

/-! An inductive invariant for the signer's 1024 bottom leaves. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafInvariant67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomStackSlots67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image

def Inv (hash : Hash) (secretKey : SecretKey) (base : Nat)
    (selected : Word) (i : Nat) (s : MachineState) : Prop :=
  s.pc = (if i < 1024 then 0x12cc else 0x14ec) ∧
  s.getMem 0x810e0 = BitVec.ofNat 64 i ∧
  s.getMem 0x810e8 = selected ∧
  s.getMem 0x81000 = 0 ∧
  (∀ (hi : i < 1024) (w : Fin 3),
    s.getMem (Signing.wordAddress 0x81008 w.val) =
      (BitVec.ofNat 192 (base+i)).extractLsb' (64*w.val) 64) ∧
  (∀ w : Fin 4,
    s.getMem (Signing.wordAddress 0x20 w.val) =
      secretKey.extractLsb' (64*w.val) 64) ∧
  (∀ j : Nat, j < i →
    s.getMem (slot j 0) =
      (GroupedBottomTree.leafRoot hash secretKey (base+j)).extractLsb' 0 64 ∧
    s.getMem (slot j 1) =
      (GroupedBottomTree.leafRoot hash secretKey (base+j)).extractLsb' 64 64)

theorem word_succ (i : Nat) (hi : i < 1024) :
    (BitVec.ofNat 64 i) + 1 = BitVec.ofNat 64 (i+1) := by
  apply BitVec.toNat_inj.mp
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
  have h0 : i < 2^64 := by omega
  have h1 : i+1 < 2^64 := by omega
  rw [Nat.mod_eq_of_lt h0,Nat.mod_eq_of_lt h1]
  have hone : (1 : BitVec 64).toNat = 1 := rfl
  rw [hone]
  rw [Nat.mod_eq_of_lt h1]

theorem word_is_1024 (i : Nat) (hi : i < 1024) :
    ((BitVec.ofNat 64 i) + 1 = (1024 : Word)) ↔ i+1=1024 := by
  rw [word_succ i hi]
  constructor
  · intro eq
    have heq := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat] at heq
    have hs : i+1 < 2^64 := by omega
    rw [Nat.mod_eq_of_lt hs] at heq
    norm_num at heq
    exact heq
  · intro eq
    rw [eq]
    rfl

theorem next_leaf_arithmetic (base i : Nat)
    (hbase : base + 1024 ≤ 2^160)
    (halign : base % 1024 = 0)
    (hi : i + 1 < 1024) :
    base+i < 2^160 ∧ (base+i) % 1024 < 1023 := by
  have hmod : (base+i) % 1024 = i := by omega
  constructor <;> omega

theorem inv_step (hash : Hash) (secretKey : SecretKey)
    (base : Nat) (selected : Word) (i : Nat) (s : MachineState)
    (hbase : base + 1024 ≤ 2^160)
    (halign : base % 1024 = 0)
    (hi : i < 1024) (inv : Inv hash secretKey base selected i s) :
    ∃ next : MachineState,
      Trace hash image s
        (if s.getMem 0x810e0 = s.getMem 0x810e8 then 166 else 149)
        (if s.getMem 0x810e0 = s.getMem 0x810e8 then 180 else 163)
        2 2 next ∧
      Inv hash secretKey base selected (i+1) next ∧
      (∀ a : Word,
        GroupedBalancedSignBottomLeafTickData67.StableAddress a →
          next.getMem a = s.getMem a) ∧
      (s.getMem 0x810e0 = s.getMem 0x810e8 →
        ∀ w : Fin 2,
          next.getMem (Signing.wordAddress 0x20080 w.val) =
            (GroupedBottomTree.secret hash secretKey (base+i)).extractLsb'
              (64*w.val) 64) ∧
      (s.getMem 0x810e0 ≠ s.getMem 0x810e8 →
        ∀ w : Fin 2,
          next.getMem (Signing.wordAddress 0x20080 w.val) =
            s.getMem (Signing.wordAddress 0x20080 w.val)) := by
  obtain ⟨pc,count,chosen,level,address,keyWords,prior⟩ := inv
  have entryPc : s.pc = 0x12cc := by simpa [hi] using pc
  have countBound : (s.getMem 0x810e0).toNat < 1024 := by
    rw [count]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hi
  obtain ⟨next,trace,nextCount,nextLow,nextChosen,nextLevel,nextUpper,
    nextKey,stored0,stored8,previous,stable,nextPc,selectedWords,
    skippedWords⟩ :=
    GroupedBalancedSignBottomLeafTickData67.leaf_tick_data hash s
      secretKey (base+i) entryPc countBound level (address hi) keyWords
  refine ⟨next,trace,?_,stable,selectedWords,skippedWords⟩
  refine ⟨?_,?_,?_,nextLevel,?_,nextKey,?_⟩
  · rw [nextPc,count]
    by_cases hnext : i+1 < 1024
    · have hne : i+1 ≠ 1024 := by omega
      have hcond : ¬ ((BitVec.ofNat 64 i) + 1 = (1024 : Word)) := by
        intro eq
        exact hne ((word_is_1024 i hi).mp eq)
      simp only [if_pos hnext]
      split
      · rename_i eq
        exact False.elim (hcond eq)
      · rfl
    · have heq : i+1=1024 := by omega
      have hcond : (BitVec.ofNat 64 i) + 1 = (1024 : Word) :=
        (word_is_1024 i hi).mpr heq
      simp only [if_neg hnext]
      split
      · rfl
      · rename_i ne
        exact False.elim (ne hcond)
  · rw [nextCount,count,word_succ i hi]
  · exact nextChosen.trans chosen
  · intro hnext w
    have ⟨hLeaf,hm⟩ := next_leaf_arithmetic base i hbase halign hnext
    fin_cases w
    · have old : s.getMem 0x81008 =
          (BitVec.ofNat 192 (base+i)).extractLsb' 0 64 := by
        have h := address hi (0 : Fin 3)
        norm_num [Signing.wordAddress] at h
        exact h
      have step := GroupedBalancedSignBottomAddressStep67.low_step
        (base+i) hLeaf hm
      have new : next.getMem 0x81008 =
          (BitVec.ofNat 192 (base+i+1)).extractLsb' 0 64 :=
        (nextLow.trans (congrArg (fun x : Word => x + 1) old)).trans step.symm
      norm_num [Signing.wordAddress]
      change next.getMem (0x81008 : Word) =
        (BitVec.ofNat 192 (base+(i+1))).extractLsb' 0 64
      simpa only [Nat.add_assoc] using new
    · have old : s.getMem 0x81010 =
          (BitVec.ofNat 192 (base+i)).extractLsb' 64 64 := by
        have h := address hi (1 : Fin 3)
        norm_num [Signing.wordAddress] at h
        exact h
      have step := GroupedBalancedSignBottomAddressStep67.middle_step
        (base+i) hLeaf hm
      have keep : next.getMem 0x81010 = s.getMem 0x81010 := by
        have h := nextUpper (0 : Fin 2)
        norm_num [Signing.wordAddress] at h
        exact h
      have new : next.getMem 0x81010 =
          (BitVec.ofNat 192 (base+i+1)).extractLsb' 64 64 :=
        (keep.trans old).trans step.symm
      norm_num [Signing.wordAddress]
      change next.getMem (0x81010 : Word) =
        (BitVec.ofNat 192 (base+(i+1))).extractLsb' 64 64
      simpa only [Nat.add_assoc] using new
    · have old : s.getMem 0x81018 =
          (BitVec.ofNat 192 (base+i)).extractLsb' 128 64 := by
        have h := address hi (2 : Fin 3)
        norm_num [Signing.wordAddress] at h
        exact h
      have step := GroupedBalancedSignBottomAddressStep67.high_step
        (base+i) hLeaf hm
      have keep : next.getMem 0x81018 = s.getMem 0x81018 := by
        have h := nextUpper (1 : Fin 2)
        norm_num [Signing.wordAddress] at h
        exact h
      have new : next.getMem 0x81018 =
          (BitVec.ofNat 192 (base+i+1)).extractLsb' 128 64 :=
        (keep.trans old).trans step.symm
      norm_num [Signing.wordAddress]
      change next.getMem (0x81018 : Word) =
        (BitVec.ofNat 192 (base+(i+1))).extractLsb' 128 64
      simpa only [Nat.add_assoc] using new
  · intro j hj
    by_cases eq : j = i
    · subst j
      have current0 : next.getMem (slot i 0) =
          (GroupedBottomTree.leafRoot hash secretKey (base+i)).extractLsb' 0 64 := by
        rw [slot0_dynamic i hi,← count]
        exact stored0
      have current8 : next.getMem (slot i 1) =
          (GroupedBottomTree.leafRoot hash secretKey (base+i)).extractLsb' 64 64 := by
        rw [slot1_dynamic i hi,← count]
        exact stored8
      exact ⟨current0,current8⟩
    · have hjOld : j < i := by omega
      have old := prior j hjOld
      have countNat : (s.getMem 0x810e0).toNat = i := by
        rw [count]
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega)]
      have hjCount : j < (s.getMem 0x810e0).toNat := by
        rw [countNat]
        exact hjOld
      exact ⟨(previous j 0 hjCount (by decide)).trans old.1,
        (previous j 1 hjCount (by decide)).trans old.2⟩

theorem run_prefix_stable (hash : Hash) (secretKey : SecretKey)
    (base : Nat) (selected : Word) (start : MachineState)
    (hbase : base + 1024 ≤ 2^160)
    (halign : base % 1024 = 0)
    (initial : Inv hash secretKey base selected 0 start) :
    ∀ i : Nat, i ≤ 1024 →
      ∃ (n c : Nat) (finish : MachineState),
        Trace hash image start n c (2*i) (2*i) finish ∧
        Inv hash secretKey base selected i finish ∧
        (∀ a : Word,
          GroupedBalancedSignBottomLeafTickData67.StableAddress a →
            finish.getMem a = start.getMem a) := by
  intro i hi
  induction i with
  | zero =>
    exact ⟨0,0,start,by simpa using
      (Trace.refl (hash := hash) (image := image) start),initial,
      by intro a _; rfl⟩
  | succ i ih =>
    have hi0 : i < 1024 := by omega
    obtain ⟨n,c,mid,trace,midInv,midStable⟩ := ih (by omega)
    obtain ⟨finish,step,finishInv,stepStable,_,_⟩ :=
      inv_step hash secretKey base selected i mid hbase halign hi0 midInv
    refine ⟨n + (if mid.getMem 0x810e0 = mid.getMem 0x810e8 then 166 else 149),
      c + (if mid.getMem 0x810e0 = mid.getMem 0x810e8 then 180 else 163),
      finish,?_,finishInv,?_⟩
    · simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        trace.trans step
    · intro a ha
      exact (stepStable a ha).trans (midStable a ha)

theorem run_prefix (hash : Hash) (secretKey : SecretKey)
    (base : Nat) (selected : Word) (start : MachineState)
    (hbase : base + 1024 ≤ 2^160)
    (halign : base % 1024 = 0)
    (initial : Inv hash secretKey base selected 0 start) :
    ∀ i : Nat, i ≤ 1024 →
      ∃ (n c : Nat) (finish : MachineState),
        Trace hash image start n c (2*i) (2*i) finish ∧
        Inv hash secretKey base selected i finish := by
  intro i hi
  obtain ⟨n,c,finish,trace,inv,_⟩ :=
    run_prefix_stable hash secretKey base selected start hbase halign initial i hi
  exact ⟨n,c,finish,trace,inv⟩

theorem run_all_stable (hash : Hash) (secretKey : SecretKey)
    (base : Nat) (selected : Word) (start : MachineState)
    (hbase : base + 1024 ≤ 2^160)
    (halign : base % 1024 = 0)
    (initial : Inv hash secretKey base selected 0 start) :
    ∃ (n c : Nat) (finish : MachineState),
      Trace hash image start n c 2048 2048 finish ∧
      finish.pc = 0x14ec ∧
      (∀ j : Nat, j < 1024 →
        finish.getMem (slot j 0) =
          (GroupedBottomTree.leafRoot hash secretKey (base+j)).extractLsb' 0 64 ∧
        finish.getMem (slot j 1) =
          (GroupedBottomTree.leafRoot hash secretKey (base+j)).extractLsb' 64 64) ∧
      (∀ a : Word,
        GroupedBalancedSignBottomLeafTickData67.StableAddress a →
          finish.getMem a = start.getMem a) := by
  obtain ⟨n,c,finish,trace,inv,stable⟩ :=
    run_prefix_stable hash secretKey base selected start hbase halign initial
      1024 (by decide)
  refine ⟨n,c,finish,by simpa using trace,?_,?_,stable⟩
  · exact inv.1.trans (by decide)
  · exact inv.2.2.2.2.2.2

theorem run_all (hash : Hash) (secretKey : SecretKey)
    (base : Nat) (selected : Word) (start : MachineState)
    (hbase : base + 1024 ≤ 2^160)
    (halign : base % 1024 = 0)
    (initial : Inv hash secretKey base selected 0 start) :
    ∃ (n c : Nat) (finish : MachineState),
      Trace hash image start n c 2048 2048 finish ∧
      finish.pc = 0x14ec ∧
      (∀ j : Nat, j < 1024 →
        finish.getMem (slot j 0) =
          (GroupedBottomTree.leafRoot hash secretKey (base+j)).extractLsb' 0 64 ∧
        finish.getMem (slot j 1) =
          (GroupedBottomTree.leafRoot hash secretKey (base+j)).extractLsb' 64 64) := by
  obtain ⟨n,c,finish,trace,inv⟩ :=
    run_prefix hash secretKey base selected start hbase halign initial 1024 (by decide)
  refine ⟨n,c,finish,by simpa using trace,?_,?_⟩
  · exact inv.1.trans (by decide)
  · exact inv.2.2.2.2.2.2

#print axioms word_succ
#print axioms word_is_1024
#print axioms next_leaf_arithmetic
#print axioms inv_step
#print axioms run_prefix_stable
#print axioms run_prefix
#print axioms run_all_stable
#print axioms run_all
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafInvariant67
