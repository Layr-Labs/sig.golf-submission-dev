import SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodeStore67

/-! Safe tree buffer addresses for the 15 direct67 H4 parent nodes. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodeAddress67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private theorem src_addr (s : MachineState) (n b : Nat)
    (index : s.getMem 0x81040#64 = BitVec.ofNat 64 n)
    (base : s.getMem 0x81078#64 = BitVec.ofNat 64 b) :
    (s.getMem 0x81040#64 <<< 5) + s.getMem 0x81078#64 =
      BitVec.ofNat 64 (b+32*n) := by
  rw [index,base,KeygenDomain.shift_ofNat]
  simp [BitVec.ofNat_add,Nat.mul_comm,BitVec.add_comm]

private theorem dst_addr (s : MachineState) (n b : Nat)
    (index : s.getMem 0x81040#64 = BitVec.ofNat 64 n)
    (base : s.getMem 0x81080#64 = BitVec.ofNat 64 b) :
    (s.getMem 0x81040#64 <<< 4) + s.getMem 0x81080#64 =
      BitVec.ofNat 64 (b+16*n) := by
  rw [index,base,KeygenDomain.shift_ofNat]
  simp [BitVec.ofNat_add,Nat.mul_comm,BitVec.add_comm]

theorem source_accesses (s : MachineState) (n b : Nat)
    (nBound : n < 8) (bCase : b = 0x82000 ∨ b = 0x82100)
    (index : s.getMem 0x81040#64 = BitVec.ofNat 64 n)
    (base : s.getMem 0x81078#64 = BitVec.ofNat 64 b) :
    ∀ k : Fin 4, accessValid ((s.getMem 0x81040#64 <<< 5) +
      s.getMem 0x81078#64 + BitVec.ofNat 64 (8*k.val)) 8 = true := by
  intro k
  have addr := src_addr s n b index base
  rw [addr]
  have bRange : 0x82000 ≤ b ∧ b ≤ 0x82100 := by rcases bCase with rfl | rfl <;> omega
  simp [BitVec.ofNat_add,accessValid,rangeValid,MEMORY_BYTES,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : b + 32*n + 8*k.val < 2^64)]
  omega

theorem destination_low (s : MachineState) (n b : Nat)
    (nBound : n < 8) (bCase : b = 0x82000 ∨ b = 0x82100)
    (index : s.getMem 0x81040#64 = BitVec.ofNat 64 n)
    (base : s.getMem 0x81080#64 = BitVec.ofNat 64 b) :
    0x82000 ≤ ((s.getMem 0x81040#64 <<< 4) + s.getMem 0x81080#64).toNat ∧
    0x82000 ≤ ((s.getMem 0x81040#64 <<< 4) + s.getMem 0x81080#64 + 8#64).toNat := by
  have addr := dst_addr s n b index base
  rw [addr]
  have bRange : 0x82000 ≤ b ∧ b ≤ 0x82100 := by rcases bCase with rfl | rfl <;> omega
  simp [BitVec.ofNat_add,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : b + 16*n + 8 < 2^64)]
  omega

theorem destination_accesses (s : MachineState) (n b : Nat)
    (nBound : n < 8) (bCase : b = 0x82000 ∨ b = 0x82100)
    (index : s.getMem 0x81040#64 = BitVec.ofNat 64 n)
    (base : s.getMem 0x81080#64 = BitVec.ofNat 64 b) :
    accessValid ((s.getMem 0x81040#64 <<< 4) + s.getMem 0x81080#64) 8 = true ∧
    accessValid ((s.getMem 0x81040#64 <<< 4) + s.getMem 0x81080#64 + 8#64) 8 = true := by
  have addr := dst_addr s n b index base
  rw [addr]
  have bRange : 0x82000 ≤ b ∧ b ≤ 0x82100 := by rcases bCase with rfl | rfl <;> omega
  simp [BitVec.ofNat_add,accessValid,rangeValid,MEMORY_BYTES,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : b + 16*n + 8 < 2^64)]
  omega

#print axioms source_accesses
#print axioms destination_low
#print axioms destination_accesses
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodeAddress67

/-! One direct67 keygen H4 parent node, with loop controls. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenOneNode67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedKeygenImage67.image

theorem one_node (hash : Hash) (s : MachineState) (n k src dst : Nat)
    (pc : s.pc = 0x1480) (nBound : n < k) (kBound : k ≤ 8)
    (srcCase : src = 0x82000 ∨ src = 0x82100)
    (dstCase : dst = 0x82000 ∨ dst = 0x82100)
    (index : s.getMem 0x81040#64 = BitVec.ofNat 64 n)
    (count : s.getMem 0x81070#64 = BitVec.ofNat 64 k)
    (source : s.getMem 0x81078#64 = BitVec.ofNat 64 src)
    (destination : s.getMem 0x81080#64 = BitVec.ofNat 64 dst) :
    ∃ final,
      Trace hash image s 79 86 1 1 final ∧
      final.pc = (if n+1 = k then 0x15bc else 0x1480) ∧
      final.getMem 0x81040#64 = BitVec.ofNat 64 (n+1) ∧
      (∀ a : Word, 0x81000 ≤ a.toNat → a.toNat < 0x82000 →
        a ≠ 0x81008#64 → a ≠ 0x81040#64 → final.getMem a = s.getMem a) := by
  have srcSafe := GroupedBalancedKeygenNodeAddress67.source_accesses s n src
    (by omega) srcCase index source
  obtain ⟨hashed,first,hashedPC,hashedFrame⟩ :=
    GroupedBalancedKeygenNodeHash67.prelude_header_hash hash s pc
      (by simpa using srcSafe ⟨0,by decide⟩)
      (by simpa using srcSafe ⟨1,by decide⟩)
      (by simpa using srcSafe ⟨2,by decide⟩)
      (by simpa using srcSafe ⟨3,by decide⟩)
  have hi (a : Word) (high : 0x81000 ≤ a.toNat) (ne08 : a ≠ 0x81008#64) :
      hashed.getMem a = s.getMem a := hashedFrame a high ne08
  have hashedIndex : hashed.getMem 0x81040#64 = BitVec.ofNat 64 n := by
    rw [hi 0x81040#64 (by decide) (by decide),index]
  have hashedDestination : hashed.getMem 0x81080#64 = BitVec.ofNat 64 dst := by
    rw [hi 0x81080#64 (by decide) (by decide),destination]
  have hashedCount : hashed.getMem 0x81070#64 = BitVec.ofNat 64 k := by
    rw [hi 0x81070#64 (by decide) (by decide),count]
  obtain ⟨destLow,destNextLow⟩ :=
    GroupedBalancedKeygenNodeAddress67.destination_low hashed n dst
      (by omega) dstCase hashedIndex hashedDestination
  obtain ⟨destSafe,destNextSafe⟩ :=
    GroupedBalancedKeygenNodeAddress67.destination_accesses hashed n dst
      (by omega) dstCase hashedIndex hashedDestination
  let final := GroupedBalancedKeygenNodeStore67.storeState hashed
  have second : Trace hash image hashed 24 24 0 0 final :=
    (GroupedBalancedKeygenNodeStore67.store_steps hashed hashedPC destSafe destNextSafe).trace
  have far0 : 0x81070#64 ≠ (hashed.getMem 0x81040#64 <<< 4) + hashed.getMem 0x81080#64 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    have left : (0x81070#64 : Word).toNat = 0x81070 := by decide
    rw [left] at hn
    omega
  have far1 : 0x81070#64 ≠ (hashed.getMem 0x81040#64 <<< 4) + hashed.getMem 0x81080#64 + 8#64 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    have left : (0x81070#64 : Word).toNat = 0x81070 := by decide
    rw [left] at hn
    omega
  have bitEq : (BitVec.ofNat 64 n + 1 = BitVec.ofNat 64 k) ↔ n+1 = k := by
    constructor
    · intro eq
      have hn := congrArg BitVec.toNat eq
      simp [BitVec.toNat_ofNat] at hn
      omega
    · intro eq
      simpa [BitVec.ofNat_add] using congrArg (BitVec.ofNat 64) eq
  refine ⟨final,by simpa only [Nat.reduceAdd] using first.trans second,?_,?_,?_⟩
  · rw [GroupedBalancedKeygenNodeStore67.store_pc hashed hashedPC far0 far1,
      hashedIndex,hashedCount]
    simp only [bitEq]
  · rw [GroupedBalancedKeygenNodeStore67.store_counter,hashedIndex]
    simp [BitVec.ofNat_add]
  · intro a high low ne08 ne40
    rw [GroupedBalancedKeygenNodeStore67.store_below_frame hashed a low ne40 destLow destNextLow]
    exact hi a high ne08

#print axioms one_node
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenOneNode67
