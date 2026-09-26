import SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafRestart67

/-! All 16 keygen H3 leaves, with exact machine resources. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeavesFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem regular_leaf (hash : Hash) (s : MachineState) (n : Nat)
    (pc : s.pc = 0x1050) (bound : n < 15)
    (counter : s.getMem 0x81030 = 0)
    (leaf : s.getMem 0x81008#64 = BitVec.ofNat 64 n)
    (level : s.getMem 0x81000 = 156) :
    ∃ final,
      Trace hash image s 11854 13726 248 265 final ∧
      final.pc = 0x1050 ∧
      final.getMem 0x81030 = 0 ∧
      final.getMem 0x81008#64 = BitVec.ofNat 64 (n+1) ∧
      final.getMem 0x81000 = 156 := by
  obtain ⟨chains,first,chainsPC,_,chainsLevel,chainsLeaf⟩ :=
    GroupedBalancedKeygenChainsFold67.all_chains hash s pc counter level
  obtain ⟨stored,second,storedPC,storedLeaf,storedLevel⟩ :=
    GroupedBalancedKeygenOneLeaf67.one_leaf hash chains n chainsPC
      (by omega) (chainsLeaf.trans leaf) chainsLevel
  have nextPC : stored.pc = 0x1040 := by
    simpa [show n ≠ 15 by omega] using storedPC
  let final := GroupedBalancedKeygenLeafRestart67.restartState stored
  have third : Trace hash image stored 4 4 0 0 final :=
    (GroupedBalancedKeygenLeafRestart67.restart_steps stored nextPC).trace
  have finalLeaf : final.getMem 0x81008#64 = BitVec.ofNat 64 (n+1) := by
    rw [GroupedBalancedKeygenLeafRestart67.restart_other stored 0x81008#64
      (by decide)]
    exact storedLeaf
  have finalLevel : final.getMem 0x81000 = 156 := by
    rw [GroupedBalancedKeygenLeafRestart67.restart_other stored 0x81000
      (by decide)]
    exact storedLevel
  exact ⟨final,by simpa only [Nat.reduceAdd] using
    (first.trans second).trans third,
    GroupedBalancedKeygenLeafRestart67.restart_pc stored nextPC,
    GroupedBalancedKeygenLeafRestart67.restart_counter stored,
    finalLeaf,finalLevel⟩

theorem last_leaf (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 0)
    (leaf : s.getMem 0x81008#64 = 15#64)
    (level : s.getMem 0x81000 = 156) :
    ∃ final,
      Trace hash image s 11850 13722 248 265 final ∧
      final.pc = 0x1428 ∧
      final.getMem 0x81008#64 = 16#64 ∧
      final.getMem 0x81000 = 156 := by
  obtain ⟨chains,first,chainsPC,_,chainsLevel,chainsLeaf⟩ :=
    GroupedBalancedKeygenChainsFold67.all_chains hash s pc counter level
  obtain ⟨final,second,finalPC,finalLeaf,finalLevel⟩ :=
    GroupedBalancedKeygenOneLeaf67.one_leaf hash chains 15 chainsPC
      (by decide) (by simpa using chainsLeaf.trans leaf) chainsLevel
  exact ⟨final,by simpa only [Nat.reduceAdd] using first.trans second,
    by simpa using finalPC,by simpa using finalLeaf,finalLevel⟩

theorem regular_leaves (hash : Hash) (s : MachineState) (k : Nat)
    (bound : k ≤ 15) (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 0)
    (leaf : s.getMem 0x81008#64 = 0)
    (level : s.getMem 0x81000 = 156) :
    ∃ final,
      Trace hash image s (11854*k) (13726*k) (248*k) (265*k) final ∧
      final.pc = 0x1050 ∧
      final.getMem 0x81030 = 0 ∧
      final.getMem 0x81008#64 = BitVec.ofNat 64 k ∧
      final.getMem 0x81000 = 156 := by
  induction k with
  | zero =>
      exact ⟨s,by simpa using (Trace.refl s : Trace hash image s 0 0 0 0 s),
        pc,counter,by simpa using leaf,level⟩
  | succ k ih =>
      obtain ⟨mid,first,midPC,midCounter,midLeaf,midLevel⟩ :=
        ih (by omega)
      obtain ⟨final,second,finalPC,finalCounter,finalLeaf,finalLevel⟩ :=
        regular_leaf hash mid k midPC (by omega) midCounter midLeaf midLevel
      exact ⟨final,by simpa only [Nat.mul_succ,Nat.add_comm] using first.trans second,
        finalPC,finalCounter,by simpa using finalLeaf,finalLevel⟩

theorem sixteen_leaves (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 0)
    (leaf : s.getMem 0x81008#64 = 0)
    (level : s.getMem 0x81000 = 156) :
    ∃ final,
      Trace hash image s 189660 219612 3968 4240 final ∧
      final.pc = 0x1428 ∧
      final.getMem 0x81008#64 = 16#64 ∧
      final.getMem 0x81000 = 156 := by
  obtain ⟨mid,first,midPC,midCounter,midLeaf,midLevel⟩ :=
    regular_leaves hash s 15 (by decide) pc counter leaf level
  obtain ⟨final,second,finalPC,finalLeaf,finalLevel⟩ :=
    last_leaf hash mid midPC midCounter (by simpa using midLeaf) midLevel
  exact ⟨final,by simpa only [Nat.reduceMul,Nat.reduceAdd] using first.trans second,
    finalPC,finalLeaf,finalLevel⟩

theorem entry_sixteen_leaves (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1000) :
    ∃ final,
      Trace hash image s 189680 219632 3968 4240 final ∧
      final.pc = 0x1428 ∧
      final.getMem 0x81008#64 = 16#64 ∧
      final.getMem 0x81000 = 156 := by
  let entry := GroupedBalancedKeygenPrefix67.entryState s
  have first : Trace hash image s 20 20 0 0 entry :=
    GroupedBalancedKeygenPrefix67.entry_trace hash s pc
  obtain ⟨level,leaf,_,_,counter⟩ := GroupedBalancedKeygenPrefix67.entry_words s
  obtain ⟨final,second,finalPC,finalLeaf,finalLevel⟩ :=
    sixteen_leaves hash entry (GroupedBalancedKeygenPrefix67.entry_pc s pc)
      counter leaf level
  exact ⟨final,by simpa only [Nat.reduceAdd] using first.trans second,
    finalPC,finalLeaf,finalLevel⟩

#print axioms regular_leaf
#print axioms regular_leaves
#print axioms sixteen_leaves
#print axioms entry_sixteen_leaves

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeavesFold67
