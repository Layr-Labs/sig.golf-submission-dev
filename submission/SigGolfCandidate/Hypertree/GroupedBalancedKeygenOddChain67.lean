import SigGolfCandidate.Hypertree.GroupedBalancedKeygenOddSeed67

/-! An odd direct67 keygen chain needs no new H1 query. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenOddChain67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem regular_odd_chain (hash : Hash) (s : MachineState) (n : Nat)
    (pc : s.pc = 0x1050) (small : n < 65)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n)
    (odd : s.getMem 0x81030 &&& 1 ≠ 0) :
    ∃ final,
      Trace hash image s 112 133 3 3 final ∧
      final.pc = 0x1050 ∧
      final.getMem 0x81030 = BitVec.ofNat 64 (n+1) ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      final.getMem 0x81008 = s.getMem 0x81008 := by
  obtain ⟨ready,first,readyPC,readyX19,readyCounter,readyLevel,readyLeaf⟩ :=
    GroupedBalancedKeygenOddSeed67.odd_seed_from_entry hash s pc odd
  obtain ⟨final,second,done,finalCounter,_,finalLevel,finalLeaf⟩ :=
    GroupedBalancedKeygenChainStep67.regular_step hash ready n readyPC small
      (readyCounter.trans counter) (readyX19.trans counter)
  exact ⟨final,by simpa only [Nat.reduceAdd] using first.trans second,
    done,finalCounter,finalLevel.trans readyLevel,finalLeaf.trans readyLeaf⟩

theorem special65_odd_chain (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 65#64)
    (odd : s.getMem 0x81030 &&& 1 ≠ 0) :
    ∃ final,
      Trace hash image s 131 187 8 8 final ∧
      final.pc = 0x1050 ∧
      final.getMem 0x81030 = 66#64 ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      final.getMem 0x81008 = s.getMem 0x81008 := by
  obtain ⟨ready,first,readyPC,readyX19,readyCounter,readyLevel,readyLeaf⟩ :=
    GroupedBalancedKeygenOddSeed67.odd_seed_from_entry hash s pc odd
  obtain ⟨final,second,done,finalCounter,_,finalLevel,finalLeaf⟩ :=
    GroupedBalancedKeygenChainStep67.special65_step hash ready readyPC
      (readyCounter.trans counter) (readyX19.trans counter)
  exact ⟨final,by simpa only [Nat.reduceAdd] using first.trans second,
    done,finalCounter,finalLevel.trans readyLevel,finalLeaf.trans readyLeaf⟩

#print axioms regular_odd_chain
#print axioms special65_odd_chain

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenOddChain67
