import SigGolfCandidate.Hypertree.GroupedBalancedKeygenEvenSeedRun67

/-! The complete even direct67 keygen chain, including its paired H1 query. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenEvenChain67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem regular_even_chain (hash : Hash) (s : MachineState) (n : Nat)
    (pc : s.pc = 0x1050) (small : n < 65)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n)
    (even : s.getMem 0x81030 &&& 1 = 0)
    (level : s.getMem 0x81000 = 156) :
    ∃ final,
      Trace hash image s 213 241 4 4 final ∧
      final.pc = 0x1050 ∧
      final.getMem 0x81030 = BitVec.ofNat 64 (n+1) ∧
      final.getMem 0x81000 = 156 ∧
      final.getMem 0x81008 = s.getMem 0x81008 := by
  obtain ⟨ready,first,readyPC,readyX19,readyCounter,readyLevel,readyLeaf⟩ :=
    GroupedBalancedKeygenEvenSeedRun67.even_seed_from_entry
      hash s n pc counter even level
  obtain ⟨final,second,done,finalCounter,_,finalLevel,finalLeaf⟩ :=
    GroupedBalancedKeygenChainStep67.regular_step hash ready n readyPC small
      readyCounter readyX19
  exact ⟨final,by simpa only [Nat.reduceAdd] using first.trans second,
    done,finalCounter,finalLevel.trans readyLevel,finalLeaf.trans readyLeaf⟩

theorem special66_even_chain (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 66#64)
    (even : s.getMem 0x81030 &&& 1 = 0)
    (level : s.getMem 0x81000 = 156) :
    ∃ final,
      Trace hash image s 241 318 11 11 final ∧
      final.pc = 0x131c ∧
      final.getMem 0x81030 = 67#64 ∧
      final.getMem 0x81000 = 156 ∧
      final.getMem 0x81008 = s.getMem 0x81008 := by
  obtain ⟨ready,first,readyPC,readyX19,readyCounter,readyLevel,readyLeaf⟩ :=
    GroupedBalancedKeygenEvenSeedRun67.even_seed_from_entry
      hash s 66 pc counter even level
  obtain ⟨final,second,done,finalCounter,_,finalLevel,finalLeaf⟩ :=
    GroupedBalancedKeygenChainStep67.special66_step hash ready readyPC
      readyCounter readyX19
  exact ⟨final,by simpa only [Nat.reduceAdd] using first.trans second,
    done,finalCounter,finalLevel.trans readyLevel,finalLeaf.trans readyLeaf⟩

#print axioms regular_even_chain
#print axioms special66_even_chain

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenEvenChain67
