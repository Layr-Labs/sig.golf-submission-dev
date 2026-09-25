import SigGolfCandidate.Hypertree.VerifyChainLoop
import SigGolfCandidate.Hypertree.VerifyHoistBridge
import SigGolfCandidate.Hypertree.VerifyHoistWitness
import SigGolfCandidate.Hypertree.KeygenEndpoint

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

def chainSourceFast (s : MachineState) : Word := s.getMem 0x80448 + (s.getMem 0x80430 <<< 4)

theorem chainSource_eq (s : MachineState) (base : Nat) (chain : Reference.Chain)
    (pointer : s.getMem 0x80448 = BitVec.ofNat 64 base)
    (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val) :
    chainSourceFast s = BitVec.ofNat 64 (base + 16 * chain.val) := by
  unfold chainSourceFast
  rw [pointer, counter, KeygenDomain.shift_ofNat]
  change BitVec.ofNat 64 base + BitVec.ofNat 64 (chain.val * 16) = _
  rw [← BitVec.ofNat_add]
  congr 1
  omega

theorem chainSource_safe (s : MachineState) (base : Nat) (chain : Reference.Chain)
    (pointer : s.getMem 0x80448 = BitVec.ofNat 64 base)
    (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (aligned : base % 8 = 0) (bound : base + 16 * chain.val + 16 ≤ MEMORY_BYTES) :
    accessValid (chainSourceFast s) 8 = true ∧ accessValid (chainSourceFast s + 8) 8 = true := by
  rw [chainSource_eq s base chain pointer counter]
  have sum : BitVec.ofNat 64 (base + 16 * chain.val) + 8 =
      BitVec.ofNat 64 (base + 16 * chain.val + 8) := (BitVec.ofNat_add _ _).symm
  rw [sum]
  have small : base + 16 * chain.val < 2^64 := by simp only [MEMORY_BYTES] at bound; omega
  have smallNext : base + 16 * chain.val + 8 < 2^64 := by simp only [MEMORY_BYTES] at bound; omega
  simp [accessValid, rangeValid, BitVec.toNat_ofNat, Nat.add_mod, Nat.mul_mod, aligned]
  omega

private theorem witness_carry (s ready : MachineState) (level tree leaf : Nat)
    (carry : Hoist.HeaderWordCarry s level tree leaf)
    (service : ready.getReg .x5 = s.getReg .x5)
    (destination : ready.getReg .x12 = s.getReg .x12)
    (seven : ready.getReg .x31 = s.getReg .x31)
    (frame : ∀ a, a ≠ 0x80020 → a ≠ 0x80028 →
      ready.getMem a = s.getMem a) :
    Hoist.HeaderWordCarry ready level tree leaf := by
  rcases carry with ⟨oldChain,oldStep,hc,hs,header,index,r5,r12,r31⟩
  refine ⟨oldChain,oldStep,hc,hs,?_,?_,service.trans r5,
    destination.trans r12,seven.trans r31⟩
  · exact (frame _ (by decide) (by decide)).trans header
  · intro i
    exact (frame _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)).trans (index i)

/-- Witness loading, header selection, and the complete in-place HASH chain. -/
theorem recover_chain_fragment_fast (hash : Hash) (s : MachineState)
    (level tree : Nat) (side : Bool) (chain : Reference.Chain)
    (digit : Fin 8) (value : Reference.Digest)
    (levelBound : level < 256)
    (pc : s.pc = 0x1490)
    (valid0 : accessValid (chainSourceFast s) 8 = true)
    (valid8 : accessValid (chainSourceFast s + 8) 8 = true)
    (levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (leafEq : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side))
    (chainEq : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (value0 : s.getMem (chainSourceFast s) = value.extractLsb' 0 64)
    (value8 : s.getMem (chainSourceFast s + 8) = value.extractLsb' 64 64)
    (digitEq : s.getByte (BitVec.ofNat 64 (0x80600 + chain.val)) =
      BitVec.ofNat 8 digit.val)
    (ready : Hoist.HeaderReadyWord s level tree (Reference.sideNumber side) chain.val) :
    ∃ final steps cycles calls,
      Trace hash verify s steps cycles calls calls final ∧
      steps ≤ cycles ∧
      cycles ≤ 11*calls+24+(if chain.val=0 then 47 else 0) ∧
      calls = 7-digit.val ∧
      final.pc = 0x163c ∧
      final.getMem 0x80430 = BitVec.ofNat 64 chain.val ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80020 i.val) =
        (walk (Reference.chainHash hash level tree side chain)
          digit.val (7-digit.val) value).extractLsb' (64*i.val) 64) ∧
      Hoist.HeaderWordCarry final level tree (Reference.sideNumber side) ∧
      final.getReg .x1 = s.getReg .x1 ∧
      final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  obtain ⟨witness, witnessRun, witnessPC, witnessDigit, witnessChain,
    witnessPtr, witnessLevel, witnessLeaf, witnessCounter, witnessIndex,
    witnessValue, witnessService, witnessDestination, witnessSeven,
    witnessRA, witnessSP, witnessFrame⟩ :=
    Hoist.witness_prepare s level tree side chain digit value pc
      (by simpa only [Hoist.chainSource,chainSourceFast] using valid0)
      (by simpa only [Hoist.chainSource,chainSourceFast] using valid8)
      levelEq leafEq chainEq indexEq
      (by simpa only [Hoist.chainSource,chainSourceFast] using value0)
      (by simpa only [Hoist.chainSource,chainSourceFast] using value8)
      digitEq
  have witnessReady : Hoist.HeaderReadyWord witness level tree
      (Reference.sideNumber side) chain.val := by
    rcases ready with zero | carry
    · exact Or.inl zero
    · exact Or.inr (witness_carry s witness level tree
        (Reference.sideNumber side) carry witnessService witnessDestination
        witnessSeven witnessFrame)
  obtain ⟨prepared, headerSteps, headerRun, headerStepsEq, preparedPC,
    preparedData, preparedRA, preparedSP, headerFrame⟩ :=
    Hoist.prepare_header witness level tree side chain digit value witnessPC
      witnessChain witnessDigit witnessPtr witnessLevel witnessLeaf
      witnessCounter witnessIndex witnessValue witnessReady levelBound
  obtain ⟨final, loopSteps, loopCycles, loopRun, loopStepBound,
    loopCycleBound, loopStepCycle, finalPC, finalData, finalCarry,
    loopRA, loopSP, loopFrame⟩ :=
    chain_from_digit_fast hash prepared level tree side chain digit value
      preparedPC levelBound preparedData
  have frame (a : Word) (outside : OutsideChainWork a) :
      final.getMem a = s.getMem a := by
    rw [loopFrame a outside]
    have outHeader : Hoist.OutsideHeader a := by
      refine ⟨?_,?_,?_,?_,outside.2.2.2⟩
      · simpa [wordAddress] using outside.1 (0 : Fin 8)
      · simpa [wordAddress] using outside.1 (1 : Fin 8)
      · simpa [wordAddress] using outside.1 (2 : Fin 8)
      · simpa [wordAddress] using outside.1 (3 : Fin 8)
    rw [headerFrame a outHeader]
    apply witnessFrame
    · simpa [wordAddress] using outside.1 (4 : Fin 8)
    · simpa [wordAddress] using outside.1 (5 : Fin 8)
  refine ⟨final,14+headerSteps+loopSteps,14+headerSteps+loopCycles,
    7-digit.val,?_,by omega,?_,rfl,finalPC,?_,finalData.valueEq,
    finalCarry,loopRA.trans (preparedRA.trans witnessRA),
    loopSP.trans (preparedSP.trans witnessSP),frame⟩
  · convert witnessRun.trace.trans (headerRun.trace.trans loopRun) using 1 <;> omega
  · rw [headerStepsEq]
    by_cases zero : chain.val = 0
    · simp only [if_pos zero]
      omega
    · simp only [if_neg zero]
      omega
  · rw [frame _ (by unfold OutsideChainWork; decide)]
    exact chainEq

/-- The verifier's endpoint store is the shared checked store-and-advance block. -/
theorem verify_endpoint_code : KeygenEndpoint.CodeAt verify 0x163c (-508) 32 40 := by decide


end SigGolfCandidate.Hypertree.Verifying
