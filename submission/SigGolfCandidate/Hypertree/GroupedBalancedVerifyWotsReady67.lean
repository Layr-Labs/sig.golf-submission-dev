import SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsHeaderData67

/-! The decoder return flows into the existing concrete 67-chain loop. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsReady67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyWotsHeaderBlock67
open GroupedBalancedVerifyWotsHeaderFields67
open GroupedBalancedVerifyWotsHeaderData67
open GroupedBalancedByteFastChainReady67
open GroupedBalancedByteFastChainCarry67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

def readyState (s : MachineState) : MachineState :=
  GroupedBalancedByteFastLimit67.initialChainState (headerState s)

theorem ready_steps (s : MachineState) (pc : s.pc = 0x1518) :
    OrdinarySteps image s 60 (readyState s) := by
  have header := header_steps s pc
  have pointer := GroupedBalancedByteFastLimit67.initial_chain_block
    (headerState s) (header_pc s pc)
  simpa only [readyState] using
    Keygen.ordinary_trans image s (headerState s) (readyState s)
      48 12 header pointer

theorem ready_pc (s : MachineState) (pc : s.pc = 0x1518) :
    (readyState s).pc = 0x1608 :=
  GroupedBalancedByteFastLimit67.initial_chain_pc (headerState s)
    (header_pc s pc)

theorem ready_mem (s : MachineState) (a : Word) :
    (readyState s).getMem a = (headerState s).getMem a := by
  simp [readyState,GroupedBalancedByteFastLimit67.initialChainState,
    GroupedBalancedByteFastLimit67.initialState,
    GroupedBalancedByteFastLimit67.pointerState,execInstrBr]

theorem ready_header (s : MachineState) (base : Nat)
    (baseWord : s.getMem 0x81000 = BitVec.ofNat 64 base) :
    (readyState s).getMem 0x90000 =
      KeygenDomain.header 2 base 0 0 0 := by
  rw [ready_mem,header_word,baseWord]
  simp [KeygenDomain.header,KeygenDomain.shift_ofNat,
    BitVec.ofNat_add]

theorem ready_index (s : MachineState) (leaf : Nat)
    (index : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64) :
    ∀ i : Fin 3,
      (readyState s).getMem (Signing.wordAddress 0x90008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64 := by
  intro i
  fin_cases i
  · simpa [Signing.wordAddress] using
      (ready_mem s 0x90008).trans
        ((header_index_low s).trans (index 0))
  · simpa [Signing.wordAddress] using
      (ready_mem s 0x90010).trans
        ((header_index_mid s).trans (index 1))
  · simpa [Signing.wordAddress] using
      (ready_mem s 0x90018).trans
        ((header_index_high s).trans (index 2))

#print axioms ready_steps
#print axioms ready_header
#print axioms ready_index
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsReady67
