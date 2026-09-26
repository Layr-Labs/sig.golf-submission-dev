import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Round67

/-! Inductive data invariant for the direct67 upper WOTS H2 chain. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Invariant67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedUpperTree67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
noncomputable section H2Invariant
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev round := GroupedBalancedSignUpperH2Round67.roundResult

structure Data (hash : Hash) (s : MachineState)
    (base leaf witnessBase : Nat) (chain : ChainMixed)
    (step : Nat) (seed : Reference.Digest) : Prop where
  service : s.getReg .x5 = 1
  source : s.getReg .x10 = 0x80000
  bits : s.getReg .x11 = 384
  destination : s.getReg .x12 = 0x80020
  chainReg : s.getReg .x19 = BitVec.ofNat 64 chain.val
  maxReg : s.getReg .x20 = BitVec.ofNat 64 (maxDigit chain)
  stepReg : s.getReg .x21 = BitVec.ofNat 64 step
  headerCarry : ∃ old, old < 11 ∧
    s.getMem 0x80000 = KeygenDomain.header 2 base 0 chain.val old
  index : ∀ i : Fin 3,
    s.getMem (Signing.wordAddress 0x80008 i.val) =
      (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64
  value : ∀ i : Fin 2,
    s.getMem (Signing.wordAddress 0x80020 i.val) =
      (walk (chainHash hash base leaf chain) 0 step seed).extractLsb'
        (64*i.val) 64
  counter : s.getMem 0x81030 = BitVec.ofNat 64 chain.val
  witness : s.getMem 0x810f0 = BitVec.ofNat 64 witnessBase

theorem max_bounds (chain : ChainMixed) :
    3 ≤ maxDigit chain ∧ maxDigit chain ≤ 10 := by
  simp only [maxDigit,GroupedBalancedChecksum67.maxDigit]
  split_ifs <;> omega

theorem walk_one_more (hash : Hash) (base leaf : Nat)
    (chain : ChainMixed) (step : Nat) (seed : Reference.Digest) :
    walk (chainHash hash base leaf chain) 0 (step+1) seed =
      chainHash hash base leaf chain step
        (walk (chainHash hash base leaf chain) 0 step seed) := by
  rw [walk_append (chainHash hash base leaf chain) 0 step 1 seed]
  simp [walk]

theorem round_data (hash : Hash) (s : MachineState)
    (base leaf witnessBase : Nat) (chain : ChainMixed)
    (step : Nat) (seed : Reference.Digest)
    (data : Data hash s base leaf witnessBase chain step seed)
    (pc : s.pc = 0x1a38)
    (baseBound : base < 256)
    (stepBound : step < maxDigit chain)
    (witnessBound : witnessBase + 16*chain.val + 16 ≤ 0x80000)
    (aligned : witnessBase % 8 = 0) :
    ∃ n, n ≤ 30 ∧
      Trace hash image s n (n+7) 1 1 (round hash s) ∧
      (round hash s).pc =
        (if BitVec.ofNat 64 (step+1) ≠ BitVec.ofNat 64 (maxDigit chain)
          then 0x1a38 else 0x1ab0) ∧
      Data hash (round hash s) base leaf witnessBase chain (step+1) seed := by
  obtain ⟨old,oldBound,header⟩ := data.headerCarry
  have chainBound : chain.val < 67 := chain.isLt
  have safe := GroupedBalancedSignUpperH2Round67.safe_after_hash hash s
    data.source data.destination witnessBase chain.val
    data.witness data.counter chainBound witnessBound aligned
  obtain ⟨safeDigit,safeWitness,safeWitnessNext,low0,low1⟩ := safe
  obtain ⟨n,nBound,path,nextPc,nextStep,nextMax,nextChain,nextService,
    nextSource,nextBits,nextDestination,highFrame⟩ :=
      GroupedBalancedSignUpperH2Round67.round_trace hash s pc
        data.service data.source data.bits data.destination
        safeDigit safeWitness safeWitnessNext low0 low1
  have stepSmall : step < 11 := by
    have b := (max_bounds chain).2
    omega
  have nextSmall : step+1 < 11 := by
    have b := (max_bounds chain).2
    omega
  have headerAfter := GroupedBalancedSignUpperH2Round67.round_header
    hash s base chain.val old step data.source data.destination
    data.stepReg header baseBound (by omega : chain.val < 256)
    (by omega : old < 256)
    (by omega : step < 256) low0 low1
  have treeAfter := GroupedBalancedSignUpperH2Round67.round_index hash s
    data.source data.destination low0 low1
  have headerReplacement : replaceByte (s.getMem 0x80000) 4
      ((s.getReg .x21).truncate 8) =
        KeygenDomain.header 2 base 0 chain.val step := by
    rw [header,data.stepReg]
    have low : (BitVec.ofNat 64 step).truncate 8 =
        BitVec.ofNat 8 step := by simp
    rw [low]
    exact GroupedBalancedByteFastSuffixData67.header_step_replace
      base chain.val old step baseBound (by omega : chain.val < 256)
      (by omega : old < 256)
      (by omega : step < 256)
  have valueAfter := GroupedBalancedSignUpperH2Round67.round_chain_words
    hash s base leaf step chain data.source data.bits data.destination
    headerReplacement data.index
    (walk (chainHash hash base leaf chain) 0 step seed)
    data.value low0 low1
  have stepWord : s.getReg .x21 + 1 = BitVec.ofNat 64 (step+1) := by
    rw [data.stepReg,BitVec.ofNat_add]
    rfl
  refine ⟨n,nBound,path,?_,?_⟩
  · rw [nextPc,stepWord,data.maxReg]
  · refine {
      service := nextService.trans data.service,
      source := nextSource.trans data.source,
      bits := nextBits.trans data.bits,
      destination := nextDestination.trans data.destination,
      chainReg := nextChain.trans data.chainReg,
      maxReg := nextMax.trans data.maxReg,
      stepReg := nextStep.trans stepWord,
      headerCarry := ⟨step,stepSmall,headerAfter⟩,
      index := ?_, value := ?_, counter := ?_, witness := ?_ }
    · intro i
      rw [treeAfter i]
      exact data.index i
    · intro i
      rw [walk_one_more hash base leaf chain step seed]
      exact valueAfter i
    · rw [highFrame 0x81030 (by decide)]
      exact data.counter
    · rw [highFrame 0x810f0 (by decide)]
      exact data.witness

end H2Invariant
#print axioms round_data
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Invariant67
