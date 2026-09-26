import SigGolfCandidate.Hypertree.GroupedBalancedKeygenEndpointCopy67


/-! The 67 endpoint copies leave the keygen tree-level register untouched. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenEndpointLevel67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenEndpointCopy67
set_option maxRecDepth 8192

theorem copy_level (s : MachineState) (n : Nat) (bound : n < 67)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n) :
    (copyState s).getMem 0x81000 = s.getMem 0x81000 := by
  rw [copy_mem, address_eq s n counter]
  have next : BitVec.ofNat 64 (0x80800+16*n) + 8 =
      BitVec.ofNat 64 (0x80800+16*n+8) := by
    simp [BitVec.ofNat_add]
  rw [next]
  have differentCounter : (0x81000 : Word) ≠ 0x81030 := by decide
  have differentStart : (0x81000 : Word) ≠
      BitVec.ofNat 64 (0x80800+16*n) := by
    intro same
    have value := congrArg BitVec.toNat same
    have small : 0x80800+16*n < 2^64 := by omega
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at value
    omega
  have differentNext : (0x81000 : Word) ≠
      BitVec.ofNat 64 (0x80800+16*n+8) := by
    intro same
    have value := congrArg BitVec.toNat same
    have small : 0x80800+16*n+8 < 2^64 := by omega
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at value
    omega
  simp only [differentCounter, differentStart, differentNext,
    ↓reduceIte]

#print axioms copy_level

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenEndpointLevel67



/-! The 67 endpoint copies leave the keygen leaf-index register untouched. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenEndpointLeaf67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenEndpointCopy67
set_option maxRecDepth 8192

theorem copy_leaf (s : MachineState) (n : Nat) (bound : n < 67)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n) :
    (copyState s).getMem 0x81008 = s.getMem 0x81008 := by
  rw [copy_mem, address_eq s n counter]
  have next : BitVec.ofNat 64 (0x80800+16*n) + 8 =
      BitVec.ofNat 64 (0x80800+16*n+8) := by
    simp [BitVec.ofNat_add]
  rw [next]
  have differentCounter : (0x81008 : Word) ≠ 0x81030 := by decide
  have differentStart : (0x81008 : Word) ≠
      BitVec.ofNat 64 (0x80800+16*n) := by
    intro same
    have value := congrArg BitVec.toNat same
    have small : 0x80800+16*n < 2^64 := by omega
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at value
    omega
  have differentNext : (0x81008 : Word) ≠
      BitVec.ofNat 64 (0x80800+16*n+8) := by
    intro same
    have value := congrArg BitVec.toNat same
    have small : 0x80800+16*n+8 < 2^64 := by omega
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at value
    omega
  simp only [differentCounter, differentStart, differentNext,
    ↓reduceIte]

#print axioms copy_leaf

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenEndpointLeaf67


/-! A direct67 keygen WOTS chain and endpoint copy, with exact H2 cost. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenChainStep67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsChainRun67
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenEndpointCopy67
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenEndpointLevel67
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenEndpointLeaf67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

private theorem word_succ (n : Nat) :
    (BitVec.ofNat 64 n : Word) + 1 = BitVec.ofNat 64 (n+1) := by
  simp [BitVec.ofNat_add]

private theorem word_ne_of_lt (n limit : Nat)
    (small : n < limit) (limitBound : limit < 2^64) :
    (BitVec.ofNat 64 n : Word) ≠ BitVec.ofNat 64 limit := by
  intro eq
  have same := congrArg BitVec.toNat eq
  simp [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2^64),
    Nat.mod_eq_of_lt limitBound] at same
  omega

theorem regular_step (hash : Hash) (s : MachineState) (n : Nat)
    (pc : s.pc = 0x11d8) (small : n < 65)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n)
    (index : s.getReg .x19 = BitVec.ofNat 64 n) :
    ∃ final,
      Trace hash image s 86 107 3 3 final ∧
      final.pc = 0x1050 ∧
      final.getMem 0x81030 = BitVec.ofNat 64 (n+1) ∧
      final.getReg .x19 = BitVec.ofNat 64 n ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      final.getMem 0x81008 = s.getMem 0x81008 := by
  have not65 : s.getReg .x19 ≠ 65#64 := by
    rw [index]
    exact word_ne_of_lt n 65 small (by decide)
  have not66 : s.getReg .x19 ≠ 66#64 := by
    rw [index]
    exact word_ne_of_lt n 66 (by omega) (by decide)
  obtain ⟨ready,first,readyPC,readyX19,readyCounter,readyLevel,readyLeaf⟩ :=
    regular_from_entry hash s pc not65 not66
  have readyWord : ready.getMem 0x81030 = BitVec.ofNat 64 n :=
    readyCounter.trans counter
  obtain ⟨safe,safeNext⟩ := address_safe ready n (by omega) readyWord
  let final := copyState ready
  have second : Trace hash image ready 19 19 0 0 final :=
    (copy_steps ready readyPC safe safeNext).trace (hash := hash)
  have finalCounter : final.getMem 0x81030 = BitVec.ofNat 64 (n+1) := by
    rw [copy_counter,readyWord,word_succ]
  have finalPC : final.pc = 0x1050 := by
    rw [copy_pc ready readyPC,readyWord,word_succ]
    have ne : (BitVec.ofNat 64 (n+1) : Word) ≠ 67 := by
      exact word_ne_of_lt (n+1) 67 (by omega) (by decide)
    exact if_neg ne
  exact ⟨final,by simpa only [Nat.reduceAdd] using first.trans second,
    finalPC,finalCounter,by rw [copy_x19,readyX19,index],
    (copy_level ready n (by omega) readyWord).trans readyLevel,
    (copy_leaf ready n (by omega) readyWord).trans readyLeaf⟩

theorem special65_step (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x11d8)
    (counter : s.getMem 0x81030 = 65#64)
    (index : s.getReg .x19 = 65#64) :
    ∃ final,
      Trace hash image s 105 161 8 8 final ∧
      final.pc = 0x1050 ∧
      final.getMem 0x81030 = 66#64 ∧
      final.getReg .x19 = 65#64 ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      final.getMem 0x81008 = s.getMem 0x81008 := by
  obtain ⟨ready,first,readyPC,readyX19,readyCounter,readyLevel,readyLeaf⟩ :=
    special65_from_entry hash s pc index
  have readyWord : ready.getMem 0x81030 = 65#64 := readyCounter.trans counter
  obtain ⟨safe,safeNext⟩ := address_safe ready 65 (by decide) readyWord
  let final := copyState ready
  have second : Trace hash image ready 19 19 0 0 final :=
    (copy_steps ready readyPC safe safeNext).trace (hash := hash)
  have finalCounter : final.getMem 0x81030 = 66#64 := by
    rw [copy_counter,readyWord]
    decide
  have finalPC : final.pc = 0x1050 := by
    rw [copy_pc ready readyPC,readyWord]
    decide
  exact ⟨final,by simpa only [Nat.reduceAdd] using first.trans second,
    finalPC,finalCounter,by rw [copy_x19,readyX19,index],
    (copy_level ready 65 (by decide) readyWord).trans readyLevel,
    (copy_leaf ready 65 (by decide) readyWord).trans readyLeaf⟩

theorem special66_step (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x11d8)
    (counter : s.getMem 0x81030 = 66#64)
    (index : s.getReg .x19 = 66#64) :
    ∃ final,
      Trace hash image s 114 184 10 10 final ∧
      final.pc = 0x131c ∧
      final.getMem 0x81030 = 67#64 ∧
      final.getReg .x19 = 66#64 ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      final.getMem 0x81008 = s.getMem 0x81008 := by
  obtain ⟨ready,first,readyPC,readyX19,readyCounter,readyLevel,readyLeaf⟩ :=
    special66_from_entry hash s pc index
  have readyWord : ready.getMem 0x81030 = 66#64 := readyCounter.trans counter
  obtain ⟨safe,safeNext⟩ := address_safe ready 66 (by decide) readyWord
  let final := copyState ready
  have second : Trace hash image ready 19 19 0 0 final :=
    (copy_steps ready readyPC safe safeNext).trace (hash := hash)
  have finalCounter : final.getMem 0x81030 = 67#64 := by
    rw [copy_counter,readyWord]
    decide
  have finalPC : final.pc = 0x131c := by
    rw [copy_pc ready readyPC,readyWord]
    decide
  exact ⟨final,by simpa only [Nat.reduceAdd] using first.trans second,
    finalPC,finalCounter,by rw [copy_x19,readyX19,index],
    (copy_level ready 66 (by decide) readyWord).trans readyLevel,
    (copy_leaf ready 66 (by decide) readyWord).trans readyLeaf⟩

#print axioms regular_step
#print axioms special65_step
#print axioms special66_step

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenChainStep67
