import SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalFold67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsLeavesFold67

/-! Fold the concrete leaf-root values through all sixteen keygen leaves. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalLeavesFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenLeafFunctionalFold67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

def RootsPrefix (hash : Hash) (secretKey : SecretKey)
    (n : Nat) (s : MachineState) : Prop :=
  ∀ j : Fin 16, j.val < n → ∀ i : Fin 2,
    s.getMem (Signing.wordAddress 0x82000 (2*j.val+i.val)) =
      (GroupedBalancedUpperTree67.leafRoot hash secretKey 156 j.val).extractLsb'
        (64*i.val) 64

def SafeFrame (n : Nat) (s t : MachineState) : Prop :=
  (∀ a : Word, a.toNat < 0x100 → t.getMem a = s.getMem a) ∧
  (∀ j : Fin 16, j.val < n → ∀ i : Fin 2,
    t.getMem (Signing.wordAddress 0x82000 (2*j.val+i.val)) =
      s.getMem (Signing.wordAddress 0x82000 (2*j.val+i.val)))

structure LeafState (hash : Hash) (secretKey : SecretKey)
    (n : Nat) (s : MachineState) : Prop where
  even : EvenState hash secretKey n 0 s
  roots : RootsPrefix hash secretKey n s

theorem roots_zero (hash : Hash) (secretKey : SecretKey) (s : MachineState) :
    RootsPrefix hash secretKey 0 s := by
  intro j small
  omega

private theorem low_address (s : MachineState) (n : Nat) (bound : n < 16)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 n).extractLsb' (64*i.val) 64) :
    s.getMem 0x81008#64 = BitVec.ofNat 64 n :=
  leaf_counter_word s n bound address

private theorem next_address (s t : MachineState) (n : Nat)
    (bound : n < 15)
    (prior : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 n).extractLsb' (64*i.val) 64)
    (low : t.getMem 0x81008#64 = BitVec.ofNat 64 (n+1))
    (high : GroupedBalancedKeygenRootControlsTick67.ControlFrame s t) :
    ∀ i : Fin 3,
      t.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 (n+1)).extractLsb' (64*i.val) 64 := by
  intro i
  fin_cases i
  · change t.getMem 0x81008#64 = BitVec.ofNat 64 ((n+1) % 2^192)
    rw [Nat.mod_eq_of_lt (by omega : n+1 < 2^192)]
    exact low
  · have before := prior ⟨1,by decide⟩
    have same := high.1
    have zeroOld : (n % 2^192) >>> 64 = 0 := by
      rw [Nat.mod_eq_of_lt (by omega : n < 2^192),Nat.shiftRight_eq_div_pow]
      omega
    have zeroNew : ((n+1) % 2^192) >>> 64 = 0 := by
      rw [Nat.mod_eq_of_lt (by omega : n+1 < 2^192),Nat.shiftRight_eq_div_pow]
      omega
    have oldWord : t.getMem 0x81010#64 =
        BitVec.ofNat 64 ((n % 2^192) >>> 64) := by
      simpa [Signing.wordAddress,BitVec.extractLsb'] using same.trans before
    change t.getMem 0x81010#64 =
      BitVec.ofNat 64 (((n+1) % 2^192) >>> 64)
    rw [zeroNew,zeroOld] at *
    exact oldWord
  · have before := prior ⟨2,by decide⟩
    have same := high.2
    have zeroOld : (n % 2^192) >>> 128 = 0 := by
      rw [Nat.mod_eq_of_lt (by omega : n < 2^192),Nat.shiftRight_eq_div_pow]
      omega
    have zeroNew : ((n+1) % 2^192) >>> 128 = 0 := by
      rw [Nat.mod_eq_of_lt (by omega : n+1 < 2^192),Nat.shiftRight_eq_div_pow]
      omega
    have oldWord : t.getMem 0x81018#64 =
        BitVec.ofNat 64 ((n % 2^192) >>> 128) := by
      simpa [Signing.wordAddress,BitVec.extractLsb'] using same.trans before
    change t.getMem 0x81018#64 =
      BitVec.ofNat 64 (((n+1) % 2^192) >>> 128)
    rw [zeroNew,zeroOld] at *
    exact oldWord

private theorem root_slot_other (j : Fin 16) (n : Nat)
    (small : j.val < n) (bound : n < 16) (i k : Fin 2) :
    Signing.wordAddress 0x82000 (2*j.val+i.val) ≠
      Signing.wordAddress 0x82000 (2*n+k.val) := by
  intro same
  have h := congrArg BitVec.toNat same
  simp only [Signing.wordAddress,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := j.isLt; have := i.isLt; omega),
    Nat.mod_eq_of_lt (by have := k.isLt; omega)] at h
  have := i.isLt
  have := k.isLt
  omega

theorem roots_step (hash : Hash) (secretKey : SecretKey)
    (n : Nat) (bound : n < 16) (s t : MachineState)
    (prior : RootsPrefix hash secretKey n s)
    (frame : SafeFrame n s t)
    (fresh : ∀ i : Fin 2,
      t.getMem (Signing.wordAddress 0x82000 (2*n+i.val)) =
        (GroupedBalancedUpperTree67.leafRoot hash secretKey 156 n).extractLsb'
          (64*i.val) 64) :
    RootsPrefix hash secretKey (n+1) t := by
  intro j small i
  by_cases old : j.val < n
  · rw [frame.2 j old i]
    exact prior j old i
  · have eqj : j.val = n := by omega
    have same : j = ⟨n,bound⟩ := Fin.eq_of_val_eq eqj
    subst j
    exact fresh i

theorem regular_leaf_step (hash : Hash) (secretKey : SecretKey)
    (n : Nat) (bound : n < 15) (s : MachineState)
    (inv : LeafState hash secretKey n s)
    (safe : ∀ final, Trace hash image s 11854 13726 248 265 final →
      SafeFrame n s final) :
    ∃ final,
      Trace hash image s 11854 13726 248 265 final ∧
      LeafState hash secretKey (n+1) final := by
  have below : n < 16 := by omega
  obtain ⟨stored,first,storedPC,rootWords⟩ :=
    leaf_from_entry hash secretKey n below s inv.even
  have restartPC : stored.pc = 0x1040 := by
    simpa [show n ≠ 15 by omega] using storedPC
  let final := GroupedBalancedKeygenLeafRestart67.restartState stored
  have second : Trace hash image stored 4 4 0 0 final :=
    (GroupedBalancedKeygenLeafRestart67.restart_steps stored restartPC).trace
  have total : Trace hash image s 11854 13726 248 265 final := by
    simpa only [Nat.reduceAdd] using first.trans second
  obtain ⟨made,other,madePC,madeCounter,madeLeaf,madeLevel⟩ :=
    GroupedBalancedKeygenLeavesFold67.regular_leaf hash s n
      inv.even.pc bound inv.even.counter
      (low_address s n below inv.even.address) inv.even.level
  have same : final = made := Trace.deterministic total other
  have control :=
    GroupedBalancedKeygenRootControlsLeavesFold67.regular_leaf_control
      hash s final n inv.even.pc bound inv.even.counter
      (low_address s n below inv.even.address) inv.even.level total
  have frame := safe final total
  have fresh : ∀ i : Fin 2,
      final.getMem (Signing.wordAddress 0x82000 (2*n+i.val)) =
        (GroupedBalancedUpperTree67.leafRoot hash secretKey 156 n).extractLsb'
          (64*i.val) 64 := by
    intro i
    have neq : Signing.wordAddress 0x82000 (2*n+i.val) ≠ 0x81030#64 := by
      intro eq
      have h := congrArg BitVec.toNat eq
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := i.isLt; omega)] at h
      omega
    rw [GroupedBalancedKeygenLeafRestart67.restart_other stored _ neq]
    exact rootWords i
  refine ⟨final,total,⟨?_,roots_step hash secretKey n below s final
    inv.roots frame fresh⟩⟩
  refine ⟨?_,?_,?_,?_,?_,Prefix.zero hash secretKey (n+1) final⟩
  · rw [same]
    exact madePC
  · rw [same]
    exact madeCounter
  · rw [same]
    exact madeLevel
  · apply next_address s final n bound inv.even.address
    · rw [same]
      exact madeLeaf
    · exact control
  · intro i
    rw [frame.1 _ (by fin_cases i <;> decide)]
    exact inv.even.secret i

def LeafSafety (hash : Hash) (secretKey : SecretKey) : Prop :=
  (∀ n : Nat, n < 15 → ∀ s : MachineState,
    EvenState hash secretKey n 0 s → ∀ final : MachineState,
      Trace hash image s 11854 13726 248 265 final →
      SafeFrame n s final) ∧
  (∀ s : MachineState,
    EvenState hash secretKey 15 0 s → ∀ final : MachineState,
      Trace hash image s 11850 13722 248 265 final →
      SafeFrame 15 s final)

theorem regular_leaves (hash : Hash) (secretKey : SecretKey)
    (safety : LeafSafety hash secretKey)
    (k : Nat) (bound : k ≤ 15) (s : MachineState)
    (inv : LeafState hash secretKey 0 s) :
    ∃ final,
      Trace hash image s (11854*k) (13726*k) (248*k) (265*k) final ∧
      LeafState hash secretKey k final := by
  induction k with
  | zero =>
      exact ⟨s,by simpa using (Trace.refl s : Trace hash image s 0 0 0 0 s),inv⟩
  | succ k ih =>
      obtain ⟨mid,first,midInv⟩ := ih (by omega)
      obtain ⟨final,second,finalInv⟩ :=
        regular_leaf_step hash secretKey k (by omega) mid midInv
          (safety.1 k (by omega) mid midInv.even)
      refine ⟨final,?_,finalInv⟩
      simpa only [Nat.mul_succ,Nat.add_comm] using first.trans second

theorem last_leaf (hash : Hash) (secretKey : SecretKey)
    (safety : LeafSafety hash secretKey)
    (s : MachineState) (inv : LeafState hash secretKey 15 s) :
    ∃ final,
      Trace hash image s 11850 13722 248 265 final ∧
      RootsPrefix hash secretKey 16 final := by
  obtain ⟨final,trace,_,fresh⟩ :=
    leaf_from_entry hash secretKey 15 (by decide) s inv.even
  have frame := safety.2 s inv.even final trace
  exact ⟨final,trace,
    roots_step hash secretKey 15 (by decide) s final inv.roots frame fresh⟩

theorem sixteen_leaves (hash : Hash) (secretKey : SecretKey)
    (safety : LeafSafety hash secretKey)
    (s : MachineState) (inv : LeafState hash secretKey 0 s) :
    ∃ final,
      Trace hash image s 189660 219612 3968 4240 final ∧
      RootsPrefix hash secretKey 16 final := by
  obtain ⟨mid,first,midInv⟩ :=
    regular_leaves hash secretKey safety 15 (by decide) s inv
  obtain ⟨final,second,roots⟩ := last_leaf hash secretKey safety mid midInv
  refine ⟨final,?_,roots⟩
  simpa only [Nat.reduceMul,Nat.reduceAdd] using first.trans second

theorem entry_sixteen_leaves (hash : Hash) (secretKey : SecretKey)
    (safety : LeafSafety hash secretKey)
    (s : MachineState) (pc : s.pc = 0x1000)
    (source : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    ∃ final,
      Trace hash image s 189680 219632 3968 4240 final ∧
      (∀ j : Fin 16, ∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x82000 (2*j.val+i.val)) =
          (GroupedBalancedUpperTree67.leafRoot hash secretKey 156 j.val).extractLsb'
            (64*i.val) 64) := by
  let entry := GroupedBalancedKeygenPrefix67.entryState s
  have first : Trace hash image s 20 20 0 0 entry :=
    GroupedBalancedKeygenPrefix67.entry_trace hash s pc
  have initial : LeafState hash secretKey 0 entry :=
    ⟨entry_even hash secretKey s source pc,roots_zero hash secretKey entry⟩
  obtain ⟨final,second,roots⟩ :=
    sixteen_leaves hash secretKey safety entry initial
  refine ⟨final,?_,?_⟩
  · simpa only [Nat.reduceAdd] using first.trans second
  · intro j i
    exact roots j j.isLt i

#print axioms roots_step
#print axioms regular_leaf_step
#print axioms regular_leaves
#print axioms last_leaf
#print axioms sixteen_leaves
#print axioms entry_sixteen_leaves

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalLeavesFold67
