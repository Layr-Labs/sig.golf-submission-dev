import SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafStore67

/-! A complete direct67 leaf transition following its 67 endpoint chains. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenOneLeaf67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

private theorem last_leaf_iff (n : Nat) (bound : n < 16) :
    ((BitVec.ofNat 64 n : Word) + 1 = 16) ↔ n = 15 := by
  interval_cases n <;> decide

theorem one_leaf (hash : Hash) (s : MachineState) (n : Nat)
    (pc : s.pc = 0x131c) (bound : n < 16)
    (leaf : s.getMem 0x81008#64 = BitVec.ofNat 64 n)
    (level : s.getMem 0x81000 = 156) :
    ∃ final,
      Trace hash image s 865 1008 1 18 final ∧
      final.pc = (if n = 15 then 0x1428 else 0x1040) ∧
      final.getMem 0x81008#64 = BitVec.ofNat 64 (n+1) ∧
      final.getMem 0x81000 = 156 := by
  obtain ⟨hashed,first,hashedPC,highFrame⟩ :=
    GroupedBalancedKeygenLeafHash67.copy_header_hash hash s pc
  have hashedLeaf : hashed.getMem 0x81008#64 = BitVec.ofNat 64 n := by
    rw [highFrame 0x81008#64 (by decide)]
    exact leaf
  have hashedLevel : hashed.getMem 0x81000 = 156 := by
    rw [highFrame 0x81000 (by decide)]
    exact level
  obtain ⟨safe,safeNext⟩ :=
    GroupedBalancedKeygenLeafStore67.store_accesses hashed n bound hashedLeaf
  let final := GroupedBalancedKeygenLeafStore67.storeState hashed
  have second : Trace hash image hashed 21 21 0 0 final :=
    (GroupedBalancedKeygenLeafStore67.store_steps hashed hashedPC safe safeNext).trace
  have finalPC : final.pc = if n = 15 then 0x1428 else 0x1040 := by
    rw [GroupedBalancedKeygenLeafStore67.store_pc hashed hashedPC,hashedLeaf]
    have succ : (BitVec.ofNat 64 n : Word) + 1 = BitVec.ofNat 64 (n+1) := by
      simp [BitVec.ofNat_add]
    rw [succ]
    have eq : ((BitVec.ofNat 64 (n+1) : Word) = 16) ↔ n = 15 := by
      simpa only [succ] using last_leaf_iff n bound
    simp only [eq]
  have finalLeaf : final.getMem 0x81008#64 = BitVec.ofNat 64 (n+1) :=
    GroupedBalancedKeygenLeafStore67.store_counter hashed n bound hashedLeaf
  have finalLevel : final.getMem 0x81000 = 156 := by
    rw [GroupedBalancedKeygenLeafStore67.store_below_frame hashed n bound
      hashedLeaf 0x81000 (by decide) (by decide)]
    exact hashedLevel
  exact ⟨final,by simpa only [Nat.reduceAdd] using first.trans second,
    finalPC,finalLeaf,finalLevel⟩

#print axioms one_leaf

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenOneLeaf67
