import SigGolfCandidate.Hypertree.GroupedBalancedKeygenEvenChain67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenOddChain67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenPrefix67

/-! Exact resource trace for all 67 direct keygen WOTS endpoints. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenChainsFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

private theorem even_word (k : Nat) (bound : k ≤ 32) :
    ((BitVec.ofNat 64 (2*k) : Word) &&& 1) = 0 := by
  interval_cases k <;> decide

private theorem odd_word (k : Nat) (bound : k < 32) :
    ((BitVec.ofNat 64 (2*k+1) : Word) &&& 1) ≠ 0 := by
  interval_cases k <;> decide

theorem regular_pair (hash : Hash) (s : MachineState) (k : Nat)
    (pc : s.pc = 0x1050) (bound : k < 32)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 (2*k))
    (level : s.getMem 0x81000 = 156) :
    ∃ final,
      Trace hash image s 325 374 7 7 final ∧
      final.pc = 0x1050 ∧
      final.getMem 0x81030 = BitVec.ofNat 64 (2*(k+1)) ∧
      final.getMem 0x81000 = 156 ∧
      final.getMem 0x81008 = s.getMem 0x81008 := by
  have even : s.getMem 0x81030 &&& 1 = 0 := by
    rw [counter]
    exact even_word k (by omega)
  obtain ⟨mid,first,midPC,midCounter,midLevel,midLeaf⟩ :=
    GroupedBalancedKeygenEvenChain67.regular_even_chain hash s (2*k)
      pc (by omega) counter even level
  have midOdd : mid.getMem 0x81030 &&& 1 ≠ 0 := by
    rw [midCounter]
    exact odd_word k bound
  obtain ⟨final,second,finalPC,finalCounter,finalLevel,finalLeaf⟩ :=
    GroupedBalancedKeygenOddChain67.regular_odd_chain hash mid (2*k+1)
      midPC (by omega) midCounter midOdd
  exact ⟨final,by simpa only [Nat.reduceAdd] using first.trans second,
    finalPC,by simpa [show 2*(k+1) = 2*k+2 by omega] using finalCounter,
    finalLevel.trans midLevel,finalLeaf.trans midLeaf⟩

theorem regular_pairs (hash : Hash) (s : MachineState) (k : Nat)
    (bound : k ≤ 32) (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 0)
    (level : s.getMem 0x81000 = 156) :
    ∃ final,
      Trace hash image s (325*k) (374*k) (7*k) (7*k) final ∧
      final.pc = 0x1050 ∧
      final.getMem 0x81030 = BitVec.ofNat 64 (2*k) ∧
      final.getMem 0x81000 = 156 ∧
      final.getMem 0x81008 = s.getMem 0x81008 := by
  induction k with
  | zero =>
      exact ⟨s,by simpa using (Trace.refl s : Trace hash image s 0 0 0 0 s),
        pc,by simpa using counter,level,rfl⟩
  | succ k ih =>
      obtain ⟨mid,first,midPC,midCounter,midLevel,midLeaf⟩ :=
        ih (by omega)
      obtain ⟨final,second,finalPC,finalCounter,finalLevel,finalLeaf⟩ :=
        regular_pair hash mid k midPC (by omega) midCounter midLevel
      refine ⟨final,?_,finalPC,?_,finalLevel,finalLeaf.trans midLeaf⟩
      · simpa only [Nat.mul_succ, Nat.add_comm] using first.trans second
      · simpa using finalCounter

theorem all_chains (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 0)
    (level : s.getMem 0x81000 = 156) :
    ∃ final,
      Trace hash image s 10985 12714 247 247 final ∧
      final.pc = 0x131c ∧
      final.getMem 0x81030 = 67#64 ∧
      final.getMem 0x81000 = 156 ∧
      final.getMem 0x81008 = s.getMem 0x81008 := by
  obtain ⟨after64,first,pc64,counter64,level64,leaf64⟩ :=
    regular_pairs hash s 32 (by decide) pc counter level
  have even64 : after64.getMem 0x81030 &&& 1 = 0 := by
    rw [counter64]
    decide
  obtain ⟨after65,second,pc65,counter65,level65,leaf65⟩ :=
    GroupedBalancedKeygenEvenChain67.regular_even_chain hash after64 64
      pc64 (by decide) (by simpa using counter64) even64 level64
  have odd65 : after65.getMem 0x81030 &&& 1 ≠ 0 := by
    rw [counter65]
    decide
  obtain ⟨after66,third,pc66,counter66,level66,leaf66⟩ :=
    GroupedBalancedKeygenOddChain67.special65_odd_chain hash after65
      pc65 (by simpa using counter65) odd65
  have even66 : after66.getMem 0x81030 &&& 1 = 0 := by
    rw [counter66]
    decide
  obtain ⟨final,fourth,finalPC,finalCounter,finalLevel,finalLeaf⟩ :=
    GroupedBalancedKeygenEvenChain67.special66_even_chain hash after66
      pc66 counter66 even66 (level66.trans level65)
  refine ⟨final,?_,finalPC,finalCounter,finalLevel,
    finalLeaf.trans (leaf66.trans (leaf65.trans leaf64))⟩
  simpa only [Nat.reduceMul,Nat.reduceAdd] using
    ((first.trans second).trans third).trans fourth

theorem entry_all_chains (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1000) :
    ∃ final,
      Trace hash image s 11005 12734 247 247 final ∧
      final.pc = 0x131c ∧
      final.getMem 0x81030 = 67#64 ∧
      final.getMem 0x81000 = 156 ∧
      final.getMem 0x81008 = 0 := by
  let entry := GroupedBalancedKeygenPrefix67.entryState s
  have first : Trace hash image s 20 20 0 0 entry :=
    GroupedBalancedKeygenPrefix67.entry_trace hash s pc
  obtain ⟨level,leaf,_,_,counter⟩ := GroupedBalancedKeygenPrefix67.entry_words s
  obtain ⟨final,second,finalPC,finalCounter,finalLevel,finalLeaf⟩ :=
    all_chains hash entry (GroupedBalancedKeygenPrefix67.entry_pc s pc)
      counter level
  exact ⟨final,by simpa only [Nat.reduceAdd] using first.trans second,
    finalPC,finalCounter,finalLevel,finalLeaf.trans leaf⟩

#print axioms regular_pair
#print axioms regular_pairs
#print axioms all_chains
#print axioms entry_all_chains

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenChainsFold67
