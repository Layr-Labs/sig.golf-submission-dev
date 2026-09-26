import SigGolfCandidate.Hypertree.VerifyChainLoop
import SigGolfCandidate.Hypertree.VerifyHoistBridge
import SigGolfCandidate.Hypertree.VerifyHoistWitness
import SigGolfCandidate.Hypertree.VerifyHoistWitnessResume
import SigGolfCandidate.Hypertree.KeygenEndpoint
import SigGolfCandidate.Hypertree.EndpointStore
import SigGolfCandidate.Hypertree.VerifyHoistHeader
import SigGolfCandidate.Hypertree.VerifyHoistWord

/-! Inlined from SigGolfCandidate.Hypertree.VerifyChainRecovery; its only importer was SigGolfCandidate.Hypertree.VerifyEndpoint. -/
section
namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

def chainSourceFast (s : MachineState) : Word := s.getMem 0x80448 + (s.getMem 0x80430 <<< 4)

/-- The first chain starts at the full witness loader. Every resumed chain enters
after the endpoint store has left the base and chain registers ready. -/
def ChainEntry (s : MachineState) (next : Nat) : Prop :=
  s.pc = (if next = 46 then 0x1690 else if next = 0 then 0x1490 else 0x1498) ∧
  (next = 0 ∨ next = 46 ∨
    (s.getReg .x28 = 0x80000 ∧ s.getReg .x6 = BitVec.ofNat 64 next))

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
    (entry : ChainEntry s chain.val)
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
      cycles ≤ 11*calls+19+(if chain.val=0 then 49 else 0) ∧
      calls = 7-digit.val ∧
      final.pc = 0x1640 ∧
      final.getMem 0x80430 = BitVec.ofNat 64 chain.val ∧
      final.getReg .x6 = BitVec.ofNat 64 chain.val ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80020 i.val) =
        (walk (Reference.chainHash hash level tree side chain)
          digit.val (7-digit.val) value).extractLsb' (64*i.val) 64) ∧
      Hoist.HeaderWordCarry final level tree (Reference.sideNumber side) ∧
      final.getReg .x1 = s.getReg .x1 ∧
      final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  have witnessPrep :
      ∃ witness, OrdinarySteps verify s (if chain.val = 0 then 13 else 11) witness ∧
        witness.pc = 0x190c ∧
        witness.getReg .x30 = BitVec.ofNat 64 digit.val ∧
        witness.getReg .x6 = BitVec.ofNat 64 chain.val ∧
        witness.getReg .x28 = 0x80000 ∧
        witness.getMem 0x80400 = BitVec.ofNat 64 level ∧
        witness.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side) ∧
        witness.getMem 0x80430 = BitVec.ofNat 64 chain.val ∧
        (∀ i : Fin 3, witness.getMem (wordAddress 0x80408 i.val) =
          (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64) ∧
        (∀ i : Fin 2, witness.getMem (wordAddress 0x80020 i.val) =
          value.extractLsb' (64*i.val) 64) ∧
        witness.getReg .x5 = s.getReg .x5 ∧
        witness.getReg .x12 = s.getReg .x12 ∧
        witness.getReg .x31 = s.getReg .x31 ∧
        witness.getReg .x1 = s.getReg .x1 ∧
        witness.getReg .x2 = s.getReg .x2 ∧
        (∀ a, a ≠ 0x80020 → a ≠ 0x80028 → witness.getMem a = s.getMem a) := by
    have notTerminal : chain.val ≠ 46 := by have h := chain.isLt; omega
    by_cases first : chain.val = 0
    · have atFirst : s.pc = 0x1490 := by
        simpa [ChainEntry, notTerminal, first] using entry.1
      simpa [first] using
        (Hoist.witness_prepare s level tree side chain digit value atFirst
          (by simpa only [Hoist.chainSource,chainSourceFast] using valid0)
          (by simpa only [Hoist.chainSource,chainSourceFast] using valid8)
          levelEq leafEq chainEq indexEq
          (by simpa only [Hoist.chainSource,chainSourceFast] using value0)
          (by simpa only [Hoist.chainSource,chainSourceFast] using value8)
          digitEq)
    · have atResume : s.pc = 0x1498 := by
        simpa [ChainEntry, notTerminal, first] using entry.1
      have regs : s.getReg .x28 = 0x80000 ∧
          s.getReg .x6 = BitVec.ofNat 64 chain.val := by
        rcases entry.2 with zero | terminal | regs
        · exact False.elim (first zero)
        · exact False.elim (notTerminal terminal)
        · exact regs
      simpa [first] using
        (Hoist.witness_prepare_after_endpoint s level tree side chain digit value
          atResume regs.1 regs.2
          (by simpa only [Hoist.chainSource,chainSourceFast] using valid0)
          (by simpa only [Hoist.chainSource,chainSourceFast] using valid8)
          levelEq leafEq chainEq indexEq
          (by simpa only [Hoist.chainSource,chainSourceFast] using value0)
          (by simpa only [Hoist.chainSource,chainSourceFast] using value8)
          digitEq)
  obtain ⟨witness, witnessRun, witnessPC, witnessDigit, witnessChain,
    witnessPtr, witnessLevel, witnessLeaf, witnessCounter, witnessIndex,
    witnessValue, witnessService, witnessDestination, witnessSeven,
    witnessRA, witnessSP, witnessFrame⟩ := witnessPrep
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
  refine ⟨final,(if chain.val=0 then 13 else 11)+headerSteps+loopSteps,
    (if chain.val=0 then 13 else 11)+headerSteps+loopCycles,
    7-digit.val,?_,by omega,?_,rfl,finalPC,?_,finalData.chainReg,finalData.valueEq,
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

end SigGolfCandidate.Hypertree.Verifying

end

namespace SigGolfCandidate.Hypertree.Verifying.EndpointShort
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false

def CodeAt (image : Image) : Prop :=
  instructionAt image 0x1640 = some (.base (.LUI .x28 128)) ∧
  instructionAt image 0x1644 = some (.base (.SLLI .x7 .x6 4)) ∧
  instructionAt image 0x1648 = some (.base (.ADD .x7 .x7 .x12)) ∧
  instructionAt image 0x164c = some (.base (.LD .x10 .x28 32)) ∧
  instructionAt image 0x1650 = some (.base (.LD .x11 .x28 40)) ∧
  instructionAt image 0x1654 = some (.base (.SD .x7 .x10 2016)) ∧
  instructionAt image 0x1658 = some (.base (.SD .x7 .x11 2024)) ∧
  instructionAt image 0x165c = some (.base (.ADDI .x6 .x6 1)) ∧
  instructionAt image 0x1660 = some (.base (.SD .x28 .x6 1072)) ∧
  instructionAt image 0x1664 = some (.base (.ADDI .x7 .x0 46)) ∧
  instructionAt image 0x1668 = some (.base (.BNE .x6 .x7 8)) ∧
  instructionAt image 0x166c = some (.base (.JAL .x0 36)) ∧
  instructionAt image 0x1670 = some (.base (.JAL .x0 (-472)))

theorem verify_code : CodeAt verify := by
  unfold CodeAt
  decide

def core (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.SLLI .x7 .x6 4)
  let s := execInstrBr s (.ADD .x7 .x7 .x12)
  let s := execInstrBr s (.LD .x10 .x28 32)
  let s := execInstrBr s (.LD .x11 .x28 40)
  let s := execInstrBr s (.SD .x7 .x10 2016)
  let s := execInstrBr s (.SD .x7 .x11 2024)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.SD .x28 .x6 1072)
  execInstrBr s (.ADDI .x7 .x0 46)

def stateAt (s : MachineState) : MachineState :=
  let branched := execInstrBr (core s) (.BNE .x6 .x7 8)
  if s.getMem 0x80430 + 1 = 46 then
    execInstrBr branched (.JAL .x0 36)
  else execInstrBr branched (.JAL .x0 (-472))

theorem state_pc (s : MachineState) (pc : s.pc = 0x1640)
    (counterReg : s.getReg .x6 = s.getMem 0x80430) :
    (stateAt s).pc = if s.getMem 0x80430 + 1 = 46 then 0x1690 else 0x1498 := by
  simp [stateAt, core, execInstrBr, pc, counterReg, signExtend12, signExtend13, signExtend21,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  split_ifs <;> decide

theorem state_regs (s : MachineState) :
    (stateAt s).getReg .x28 = 0x80000 ∧
    (stateAt s).getReg .x6 = s.getReg .x6 + 1 ∧
    (stateAt s).getReg .x7 = 46 ∧
    (stateAt s).getReg .x10 = s.getMem 0x80020 ∧
    (stateAt s).getReg .x11 = s.getMem 0x80028 := by
  simp [stateAt, core, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem address_relative (s : MachineState)
    (destination : s.getReg .x12 = 0x80020) :
    (s.getMem 0x80430 <<< 4) + s.getReg .x12 + 2016 =
      KeygenEndpoint.address s := by
  rw [destination]
  unfold KeygenEndpoint.address
  simp only [BitVec.add_assoc]
  congr 1

theorem address_relative_next (s : MachineState)
    (destination : s.getReg .x12 = 0x80020) :
    (s.getMem 0x80430 <<< 4) + s.getReg .x12 + 2024 =
      KeygenEndpoint.address s + 8 := by
  rw [destination]
  unfold KeygenEndpoint.address
  simp only [BitVec.add_assoc]
  congr 1

theorem state_mem (s : MachineState)
    (destination : s.getReg .x12 = 0x80020)
    (counterReg : s.getReg .x6 = s.getMem 0x80430) (a : Word) :
    (stateAt s).getMem a = (KeygenEndpoint.stateAt s (-508) 32 40).getMem a := by
  simp [stateAt, core, KeygenEndpoint.stateAt, execInstrBr, signExtend12,
    destination, counterReg, BitVec.add_assoc,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem state_stack (s : MachineState) :
    (stateAt s).getReg .x1 = s.getReg .x1 ∧ (stateAt s).getReg .x2 = s.getReg .x2 := by
  simp [stateAt, core, execInstrBr, MachineState.getReg_setReg_ne]

theorem state_sticky (s : MachineState) :
    (stateAt s).getReg .x5 = s.getReg .x5 ∧
    (stateAt s).getReg .x12 = s.getReg .x12 ∧
    (stateAt s).getReg .x31 = s.getReg .x31 := by
  simp [stateAt, core, execInstrBr, MachineState.getReg_setReg_ne]


theorem state_post (s : MachineState) (chain : Reference.Chain)
    (value : Reference.Digest)
    (pc : s.pc = 0x1640)
    (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (chainReg : s.getReg .x6 = BitVec.ofNat 64 chain.val)
    (destination : s.getReg .x12 = 0x80020)
    (valueWords : ∀ i : Fin 2,
      s.getMem (wordAddress 0x80020 i.val) = value.extractLsb' (64*i.val) 64) :
    (stateAt s).pc = (if chain.val+1=46 then 0x1690 else 0x1498) ∧
    (stateAt s).getMem 0x80430 = BitVec.ofNat 64 (chain.val+1) ∧
    (∀ i : Fin 2, (stateAt s).getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
      value.extractLsb' (64*i.val) 64) ∧
    (stateAt s).getReg .x1 = s.getReg .x1 ∧
    (stateAt s).getReg .x2 = s.getReg .x2 ∧
    (∀ a, a ≠ 0x80430 →
      (∀ i : Fin 2, a ≠ KeygenEndpoint.endpointAddress chain.val i.val) →
      (stateAt s).getMem a = s.getMem a) := by
  have counterReg : s.getReg .x6 = s.getMem 0x80430 :=
    chainReg.trans counter.symm
  have addr : KeygenEndpoint.address s = KeygenEndpoint.endpointAddress chain.val 0 := by
    simpa only [KeygenEndpoint.endpointAddress, Nat.mul_zero, Nat.add_zero] using
      KeygenEndpoint.address_eq s chain.val counter
  have addr8 : KeygenEndpoint.address s + 8 =
      KeygenEndpoint.endpointAddress chain.val 1 := by
    rw [addr]
    change BitVec.ofNat 64 (0x80800+16*chain.val+8*0) + BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_add]
    rfl
  have inc : s.getMem 0x80430 + 1 = BitVec.ofNat 64 (chain.val+1) := by
    rw [counter, BitVec.ofNat_add]; rfl
  have eq : s.getMem 0x80430 + 1 = 46 ↔ chain.val+1 = 46 := by
    rw [inc]
    constructor
    · intro same
      have h := congrArg BitVec.toNat same
      change (chain.val+1) % 2^64 = 46 at h
      have := chain.isLt
      omega
    · intro same; rw [same]; rfl
  have neCounter (i : Fin 2) : KeygenEndpoint.endpointAddress chain.val i.val ≠ 0x80430 := by
    intro same
    have h := congrArg BitVec.toNat same
    simp only [KeygenEndpoint.endpointAddress, BitVec.toNat_ofNat] at h
    have hc := chain.isLt
    have hi := i.isLt
    have small : 0x80800 + 16*chain.val + 8*i.val < 2^64 := by omega
    change (0x80800 + 16*chain.val + 8*i.val) % 2^64 = 0x80430 at h
    rw [Nat.mod_eq_of_lt small] at h
    omega
  have separate : KeygenEndpoint.endpointAddress chain.val 0 ≠
      KeygenEndpoint.endpointAddress chain.val 1 := by
    intro same
    have h := congrArg BitVec.toNat same
    simp only [KeygenEndpoint.endpointAddress, BitVec.toNat_ofNat] at h
    have := chain.isLt
    omega
  have src0 : ((0x80000 : Word) + signExtend12 (32 : BitVec 12)) =
      wordAddress 0x80020 0 := by decide
  have src8 : ((0x80000 : Word) + signExtend12 (40 : BitVec 12)) =
      wordAddress 0x80020 1 := by decide
  refine ⟨?_, ?_, ?_, (state_stack s).1, (state_stack s).2, ?_⟩
  · rw [state_pc s pc counterReg]
    simp only [eq]
  · rw [state_mem s destination counterReg, KeygenEndpoint.memAt, if_pos rfl, inc]
  · intro i
    rw [state_mem s destination counterReg, KeygenEndpoint.memAt, if_neg (neCounter i), addr8, addr]
    fin_cases i
    · rw [if_neg separate, if_pos rfl]
      rw [src0]
      exact valueWords 0
    · rw [if_pos rfl]
      rw [src8]
      exact valueWords 1
  · intro a hc outside
    have h0 : a ≠ KeygenEndpoint.endpointAddress chain.val 0 := outside 0
    have h1 : a ≠ KeygenEndpoint.endpointAddress chain.val 1 := outside 1
    rw [state_mem s destination counterReg, KeygenEndpoint.memAt, if_neg hc, addr8, if_neg h1, addr, if_neg h0]


/-- The x12-relative endpoint reuses the live chain register in twelve instructions. -/
theorem block (image : Image) (code : CodeAt image) (s : MachineState)
    (chain : Reference.Chain)
    (pc : s.pc = 0x1640)
    (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (chainReg : s.getReg .x6 = BitVec.ofNat 64 chain.val)
    (destination : s.getReg .x12 = 0x80020) :
    OrdinarySteps image s 12 (stateAt s) := by
  obtain ⟨c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13⟩ := code
  have counterReg : s.getReg .x6 = s.getMem 0x80430 :=
    chainReg.trans counter.symm
  have safe := KeygenEndpoint.address_safe s chain.val chain.isLt counter
  let s1 := execInstrBr s (.LUI .x28 128)
  let s2 := s1
  let s3 := execInstrBr s2 (.SLLI .x7 .x6 4)
  let s4 := execInstrBr s3 (.ADD .x7 .x7 .x12)
  let s5 := execInstrBr s4 (.LD .x10 .x28 32)
  let s6 := execInstrBr s5 (.LD .x11 .x28 40)
  let s7 := execInstrBr s6 (.SD .x7 .x10 2016)
  let s8 := execInstrBr s7 (.SD .x7 .x11 2024)
  let s9 := execInstrBr s8 (.ADDI .x6 .x6 1)
  let s10 := execInstrBr s9 (.SD .x28 .x6 1072)
  let s11 := execInstrBr s10 (.ADDI .x7 .x0 46)
  let s12 := execInstrBr s11 (.BNE .x6 .x7 8)
  have branchPC : s12.pc =
      if s.getMem 0x80430 + 1 = 46 then 0x166c else 0x1670 := by
    simp [s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,
      execInstrBr,pc,counterReg,signExtend12,signExtend13,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  have coreEq : s11 = core s := rfl
  apply OrdinarySteps.step s s2 _ (.base (.LUI .x28 128)) 11
  · simpa only [fetch_at,pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.SLLI .x7 .x6 4)) 10
  · have hp : s2.pc = 0x1644 := by simp [s1,s2,execInstrBr,pc]
    simpa only [fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADD .x7 .x7 .x12)) 9
  · have hp : s3.pc = 0x1648 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LD .x10 .x28 32)) 8
  · have hp : s4.pc = 0x164c := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [fetch_at,hp] using c4
  · simp [s1,s2,s3,s4,s5,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      accessValid,rangeValid,MEMORY_BYTES]
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x11 .x28 40)) 7
  · have hp : s5.pc = 0x1650 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [fetch_at,hp] using c5
  · simp [s1,s2,s3,s4,s5,s6,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      accessValid,rangeValid,MEMORY_BYTES]
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x7 .x10 2016)) 6
  · have hp : s6.pc = 0x1654 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [fetch_at,hp] using c6
  · have valid : memoryArgumentsValid s6 (.SD .x7 .x10 (2016#12)) = true := by
      have safe0 := safe.1
      rw [← address_relative s destination] at safe0
      simpa [s6,s5,s4,s3,s2,s1,memoryArgumentsValid,execInstrBr,counterReg,
        signExtend12,MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne] using safe0
    simp [ordinaryStep, valid, s7]
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x7 .x11 2024)) 5
  · have hp : s7.pc = 0x1658 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [fetch_at,hp] using c7
  · have valid : memoryArgumentsValid s7 (.SD .x7 .x11 (2024#12)) = true := by
      have safe8 := safe.2
      rw [← address_relative_next s destination] at safe8
      simpa [s7,s6,s5,s4,s3,s2,s1,memoryArgumentsValid,execInstrBr,counterReg,
        signExtend12,MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne] using safe8
    simp [ordinaryStep, valid, s8]
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x6 .x6 1)) 4
  · have hp : s8.pc = 0x165c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.SD .x28 .x6 1072)) 3
  · have hp : s9.pc = 0x1660 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [fetch_at,hp] using c9
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,ordinaryStep,memoryArgumentsValid,
      execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,accessValid,rangeValid,MEMORY_BYTES]
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x7 .x0 46)) 2
  · have hp : s10.pc = 0x1664 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.BNE .x6 .x7 8)) 1
  · have hp : s11.pc = 0x1668 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [fetch_at,hp] using c11
  · rfl
  by_cases h : s.getMem (0x80430 : Word) + (1 : Word) = (46 : Word)
  · have hb : s.getMem 525360#64 + 1#64 = 46#64 := h
    apply OrdinarySteps.step s12 (stateAt s) _ (.base (.JAL .x0 36)) 0
    · have hp : s12.pc = 0x166c := by rw [branchPC]; simp [hb]
      simpa only [fetch_at,hp] using c12
    · unfold stateAt
      rw [if_pos h]
      change ordinaryStep s12 (.base (.JAL .x0 36)) =
        some (execInstrBr s12 (.JAL .x0 36))
      rfl
    exact OrdinarySteps.refl _
  · have hb : ¬ s.getMem 525360#64 + 1#64 = 46#64 := h
    apply OrdinarySteps.step s12 (stateAt s) _ (.base (.JAL .x0 (-472))) 0
    · have hp : s12.pc = 0x1670 := by rw [branchPC]; simp [hb]
      simpa only [fetch_at,hp] using c13
    · unfold stateAt
      rw [if_neg h]
      change ordinaryStep s12 (.base (.JAL .x0 (-472))) =
        some (execInstrBr s12 (.JAL .x0 (-472)))
      rfl
    exact OrdinarySteps.refl _

end SigGolfCandidate.Hypertree.Verifying.EndpointShort

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

private theorem endpoint_header_word_frame (s : MachineState) (chain : Reference.Chain)
    (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (j : Nat) (hj : j < 4) :
    (KeygenEndpoint.stateAt s (-508) 32 40).getMem (wordAddress 0x80000 j) =
      s.getMem (wordAddress 0x80000 j) := by
  rw [KeygenEndpoint.memAt]
  have counterNe : wordAddress 0x80000 j ≠ 0x80430 := by
    intro same
    have h := congrArg BitVec.toNat same
    change (0x80000+8*j) % 2^64 = 0x80430 at h
    omega
  have endpointNe (i : Fin 2) :
      wordAddress 0x80000 j ≠ KeygenEndpoint.endpointAddress chain.val i.val := by
    intro same
    have h := congrArg BitVec.toNat same
    change (0x80000+8*j) % 2^64 =
      (0x80800+16*chain.val+8*i.val) % 2^64 at h
    have hc := chain.isLt
    have hi := i.isLt
    omega
  have addr := KeygenEndpoint.address_eq s chain.val counter
  rw [if_neg counterNe, addr]
  have h0 : wordAddress 0x80000 j ≠ BitVec.ofNat 64 (0x80800+16*chain.val) := by
    simpa [KeygenEndpoint.endpointAddress] using endpointNe (0 : Fin 2)
  have h1 : wordAddress 0x80000 j ≠ BitVec.ofNat 64 (0x80800+16*chain.val)+8 := by
    have addr8 : BitVec.ofNat 64 (0x80800+16*chain.val)+8 =
        KeygenEndpoint.endpointAddress chain.val 1 := by
      simp [KeygenEndpoint.endpointAddress, BitVec.ofNat_add, Nat.add_comm]
      ac_rfl
    rw [addr8]
    exact endpointNe 1
  rw [if_neg h1, if_neg h0]

/-- The stronger word-level hoisted header invariant survives endpoint storage. -/
theorem endpoint_header_word_carry (s : MachineState) (level tree leaf : Nat)
    (chain : Reference.Chain) (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (carry : Hoist.HeaderWordCarry s level tree leaf) :
    Hoist.HeaderWordCarry (KeygenEndpoint.stateAt s (-508) 32 40) level tree leaf := by
  rcases carry with ⟨oldChain, oldStep, hc, hs, header, index, service, destination, seven⟩
  obtain ⟨r5, r12, r31⟩ := KeygenEndpoint.stickyRegsAt s (-508) 32 40
  refine ⟨oldChain, oldStep, hc, hs, ?_, ?_, r5.trans service,
    r12.trans destination, r31.trans seven⟩
  · simpa [wordAddress] using
      (endpoint_header_word_frame s chain counter 0 (by decide)).trans header
  · intro i
    have addr : wordAddress 0x80008 i.val = wordAddress 0x80000 (i.val+1) := by
      unfold wordAddress
      apply congrArg (BitVec.ofNat 64)
      omega
    rw [addr, endpoint_header_word_frame s chain counter (i.val+1)
      (by have := i.isLt; omega)]
    simpa only [← addr] using index i


/-- The old pure header carry theorem transfers because the two blocks have identical memory and sticky registers. -/
theorem endpoint_short_header_word_carry (s : MachineState) (level tree leaf : Nat)
    (chain : Reference.Chain)
    (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (chainReg : s.getReg .x6 = BitVec.ofNat 64 chain.val)
    (carry : Hoist.HeaderWordCarry s level tree leaf) :
    Hoist.HeaderWordCarry (EndpointShort.stateAt s) level tree leaf := by
  have counterReg : s.getReg .x6 = s.getMem 0x80430 :=
    chainReg.trans counter.symm
  have old := endpoint_header_word_carry s level tree leaf chain counter carry
  rcases old with ⟨oldChain, oldStep, hc, hs, header, index, service, destination, seven⟩
  rcases carry with ⟨_, _, _, _, _, _, sourceService, sourceDestination, sourceSeven⟩
  obtain ⟨r5, r12, r31⟩ := EndpointShort.state_sticky s
  refine ⟨oldChain, oldStep, hc, hs, ?_, ?_, r5.trans sourceService,
    r12.trans sourceDestination, r31.trans sourceSeven⟩
  · rw [EndpointShort.state_mem s sourceDestination counterReg]
    exact header
  · intro i
    rw [EndpointShort.state_mem s sourceDestination counterReg]
    exact index i

/-- Drop-in endpoint theorem for the patched verifier image. -/
theorem store_endpoint_with_word_carry (s : MachineState) (level tree leaf : Nat)
    (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x1640)
    (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (chainReg : s.getReg .x6 = BitVec.ofNat 64 chain.val)
    (valueWords : ∀ i : Fin 2,
      s.getMem (wordAddress 0x80020 i.val) = value.extractLsb' (64*i.val) 64)
    (carry : Hoist.HeaderWordCarry s level tree leaf) :
    ∃ final, OrdinarySteps verify s 12 final ∧
      ChainEntry final (chain.val+1) ∧
      final.getMem 0x80430 = BitVec.ofNat 64 (chain.val+1) ∧
      (∀ i : Fin 2, final.getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
        value.extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧
      final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, a ≠ 0x80430 →
        (∀ i : Fin 2, a ≠ KeygenEndpoint.endpointAddress chain.val i.val) →
        final.getMem a = s.getMem a) ∧
      Hoist.HeaderWordCarry final level tree leaf := by
  have destination : s.getReg .x12 = 0x80020 := by
    rcases carry with ⟨_, _, _, _, _, _, _, destination, _⟩
    exact destination
  obtain ⟨finalPC, finalCounter, endpoints, ra, sp, frame⟩ :=
    EndpointShort.state_post s chain value pc counter chainReg destination valueWords
  have nextEntry : ChainEntry (EndpointShort.stateAt s) (chain.val+1) := by
    constructor
    · by_cases terminal : chain.val+1=46
      · simpa [terminal] using finalPC
      · have positive : chain.val+1 ≠ 0 := by omega
        simpa [terminal, positive] using finalPC
    · right; right
      refine ⟨(EndpointShort.state_regs s).1, ?_⟩
      rw [(EndpointShort.state_regs s).2.1, chainReg, BitVec.ofNat_add]
      rfl
  exact ⟨EndpointShort.stateAt s,
    EndpointShort.block verify EndpointShort.verify_code s chain pc counter chainReg destination,
    nextEntry, finalCounter, endpoints, ra, sp, frame,
    endpoint_short_header_word_carry s level tree leaf chain counter chainReg carry⟩


/-- info: 'SigGolfCandidate.Hypertree.Verifying.store_endpoint_with_word_carry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms store_endpoint_with_word_carry

end SigGolfCandidate.Hypertree.Verifying
