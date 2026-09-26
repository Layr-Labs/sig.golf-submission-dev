import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSchedule67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperIndexedInitial67
import SigGolfCandidate.Hypertree.GroupedBalancedScheme67

/-! State carried across all upper signing groups. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperOuterInvariant67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperSchedule67
open GroupedBalancedSignUpperIndexedInitial67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def indexAt (initial : BitVec 192) (k : Nat) : BitVec 192 :=
  initial >>> prefixHeight k

def groupRoot (hash : Hash) (secretKey : SecretKey)
    (initialIndex : BitVec 192) (k : Nat) : BitVec 128 :=
  GroupedBalancedUpperTree67.root hash secretKey (treeBase k) (height k)
    ((indexAt initialIndex k).toNat/2^height k)

structure Boundary (hash : Hash) (secretKey : SecretKey)
    (initialIndex : BitVec 192)
    (k : Nat) (message : BitVec 128) (s : MachineState) : Prop where
  pc : s.pc=0x15e0
  layer : s.getMem 0x81058=BitVec.ofNat 64 k
  heightWord : s.getMem 0x81060=BitVec.ofNat 64 (height k)
  treeWord : s.getMem 0x81000=BitVec.ofNat 64 (treeBase k)
  witnessWord : s.getMem 0x810f0=BitVec.ofNat 64 (currentWitness k)
  selectedWords : ∀ w : Fin 3,
    s.getMem (Signing.wordAddress 0x81090 w.val)=
      (indexAt initialIndex k).extractLsb' (64*w.val) 64
  currentWords : CurrentWords s message
  stack : s.getReg .x2=0xfff700
  keyWords : ∀ j : Fin 4,
    s.getMem (Signing.wordAddress 0x20 j.val)=
      secretKey.extractLsb' (64*j.val) 64
  tables : GroupedBalancedVerifyByteContract67.Tables s

theorem index_next (initial : BitVec 192) (k : Nat) :
    indexAt initial (k+1)=indexAt initial k >>> height k := by
  unfold indexAt
  rw [prefix_next,BitVec.shiftRight_add]

theorem index_bound (initial : BitVec 192)
    (initialBound : initial.toNat<2^150) (k : Nat) :
    (indexAt initial k).toNat<2^160 := by
  simp only [indexAt,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  have h : initial.toNat / 2^prefixHeight k ≤ initial.toNat :=
    Nat.div_le_self _ _
  omega

theorem final_index_small (initial : BitVec 192)
    (initialBound : initial.toNat<2^150) :
    (indexAt initial 44).toNat<16 := by
  simp only [indexAt,prefix_forty_four,BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  have hp : (2:Nat)^150=(2:Nat)^146*16 := by decide
  omega

theorem final_root_address_zero (initial : BitVec 192)
    (initialBound : initial.toNat<2^150) :
    (indexAt initial 44).toNat/16=0 := by
  have h := final_index_small initial initialBound
  omega

theorem layer_thirty_iff (k : Nat) (hk : k<45) :
    (BitVec.ofNat 64 k+1=(30 : Word)) ↔ k=29 := by
  constructor
  · intro h
    have word : BitVec.ofNat 64 (k+1)=30#64 := by
      simpa [BitVec.ofNat_add] using h
    have hn := congrArg BitVec.toNat word
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : k+1<2^64)] at hn
    norm_num at hn
    omega
  · intro h
    subst k
    decide

theorem layer_forty_five_iff (k : Nat) (hk : k<45) :
    (BitVec.ofNat 64 k+1=(45 : Word)) ↔ k=44 := by
  constructor
  · intro h
    have word : BitVec.ofNat 64 (k+1)=45#64 := by
      simpa [BitVec.ofNat_add] using h
    have hn := congrArg BitVec.toNat word
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : k+1<2^64)] at hn
    norm_num at hn
    omega
  · intro h
    subst k
    decide

theorem current_of_root (s : MachineState) (root : BitVec 128)
    (words : ∀ w : Fin 2,
      s.getMem (BitVec.ofNat 64 (0x80500+8*w.val))=
        root.extractLsb' (64*w.val) 64) : CurrentWords s root := by
  intro w
  simpa [CurrentWords,Signing.wordAddress] using words w

theorem witness_after_group (k : Nat) (final : MachineState)
    (word : final.getMem 0x810f0=
      BitVec.ofNat 64 (witnessBase k) +
        (BitVec.ofNat 64 (height k) <<< 4)) :
    final.getMem 0x810f0=
      BitVec.ofNat 64 (currentWitness (k+1)) := by
  rw [witness_next]
  rcases height_cases k with h|h
  · rw [h] at word ⊢
    have shift : (BitVec.ofNat 64 3 <<< 4)=48#64 := by decide
    rw [shift] at word
    simpa [BitVec.ofNat_add] using word
  · rw [h] at word ⊢
    have shift : (BitVec.ofNat 64 4 <<< 4)=64#64 := by decide
    rw [shift] at word
    simpa [BitVec.ofNat_add] using word

theorem boundary_next (hash : Hash) (secretKey : SecretKey)
    (initialIndex : BitVec 192) (k : Nat) (hk : k<44)
    (message : BitVec 128) (s final : MachineState)
    (before : Boundary hash secretKey initialIndex k message s)
    (pc : final.pc=
      (if s.getMem 0x81058+1=(45 : Word) then 0x1d60 else 0x15e0))
    (rootWords : ∀ w : Fin 2,
      final.getMem (BitVec.ofNat 64 (0x80500+8*w.val))=
        (groupRoot hash secretKey initialIndex k).extractLsb'
          (64*w.val) 64)
    (layer : final.getMem 0x81058=s.getMem 0x81058+1)
    (heightWord : final.getMem 0x81060=
      (if s.getMem 0x81058+1=(30 : Word) then 4 else
        BitVec.ofNat 64 (height k)))
    (witnessWord : final.getMem 0x810f0=
      BitVec.ofNat 64 (witnessBase k)+
        (BitVec.ofNat 64 (height k) <<< 4))
    (selectedWords : ∀ w : Fin 3,
      final.getMem (Signing.wordAddress 0x81090 w.val)=
        (indexAt initialIndex k >>> height k).extractLsb'
          (64*w.val) 64)
    (stack : final.getReg .x2=s.getReg .x2)
    (lowFrame : ∀ a : Word, a.toNat<0x100 →
      final.getMem a=s.getMem a)
    (treeWord : final.getMem 0x81000=
      BitVec.ofNat 64 (treeBase k+height k))
    (tableFrame : ∀ a : Word, 0xfff700≤a.toNat →
      final.getMem a=s.getMem a) :
    Boundary hash secretKey initialIndex (k+1)
      (groupRoot hash secretKey initialIndex k) final := by
  have hk45 : k<45 := by omega
  have notLast : s.getMem 0x81058+1≠(45 : Word) := by
    rw [before.layer]
    intro eq
    have keq := (layer_forty_five_iff k hk45).mp eq
    omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [if_neg notLast] using pc
  · calc
      final.getMem 0x81058=s.getMem 0x81058+1 := layer
      _ = BitVec.ofNat 64 k+1 := by rw [before.layer]
      _ = BitVec.ofNat 64 (k+1) := by simp [BitVec.ofNat_add]
  · rw [heightWord]
    change (if s.getMem (528472#64)+1#64=30#64 then 4#64 else
      BitVec.ofNat 64 (height k)) = BitVec.ofNat 64 (height (k+1))
    by_cases h29 : k=29
    · have hs : s.getMem 0x81058+1=(30 : Word) := by
        rw [before.layer]
        exact (layer_thirty_iff k hk45).mpr h29
      change s.getMem (528472#64)+1#64=30#64 at hs
      rw [if_pos hs,height_switch]
      simp [h29]
    · have hs : s.getMem 0x81058+1≠(30 : Word) := by
        rw [before.layer]
        exact fun eq => h29 ((layer_thirty_iff k hk45).mp eq)
      change s.getMem (528472#64)+1#64≠30#64 at hs
      rw [if_neg hs,height_switch]
      simp [h29]
  · rw [treeWord,treeBase_next]
  · exact witness_after_group k final witnessWord
  · intro w
    rw [index_next]
    exact selectedWords w
  · exact current_of_root final _ rootWords
  · rw [stack]
    exact before.stack
  · intro j
    rw [lowFrame _ (by fin_cases j <;> decide)]
    exact before.keyWords j
  · exact GroupedBalancedSignUpperBaseToInitial67.tables_of_high_frame
      s final before.tables tableFrame

#print axioms index_next
#print axioms index_bound
#print axioms final_root_address_zero
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperOuterInvariant67
