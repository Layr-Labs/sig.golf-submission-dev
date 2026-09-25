import SigGolfCandidate.Hypertree.EndpointStore
import SigGolfCandidate.Hypertree.VerifyChainRecovery
import SigGolfCandidate.Hypertree.VerifyHoistHeader
import SigGolfCandidate.Hypertree.VerifyHoistWord

namespace SigGolfCandidate.Hypertree.Verifying.EndpointShort
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false

def CodeAt (image : Image) : Prop :=
  instructionAt image 0x163c = some (.base (.LUI .x28 128)) ∧
  instructionAt image 0x1640 = some (.base (.LD .x6 .x28 1072)) ∧
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
  let s := execInstrBr s (.LD .x6 .x28 1072)
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

theorem state_pc (s : MachineState) (pc : s.pc = 0x163c) :
    (stateAt s).pc = if s.getMem 0x80430 + 1 = 46 then 0x1690 else 0x1498 := by
  simp [stateAt, core, execInstrBr, pc, signExtend12, signExtend13, signExtend21,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  split_ifs <;> decide

theorem state_regs (s : MachineState) :
    (stateAt s).getReg .x28 = 0x80000 ∧
    (stateAt s).getReg .x6 = s.getMem 0x80430 + 1 ∧
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
    (destination : s.getReg .x12 = 0x80020) (a : Word) :
    (stateAt s).getMem a = (KeygenEndpoint.stateAt s (-508) 32 40).getMem a := by
  simp [stateAt, core, KeygenEndpoint.stateAt, execInstrBr, signExtend12,
    destination, BitVec.add_assoc,
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
    (pc : s.pc = 0x163c)
    (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
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
  · rw [state_pc s pc]
    simp only [eq]
  · rw [state_mem s destination, KeygenEndpoint.memAt, if_pos rfl, inc]
  · intro i
    rw [state_mem s destination, KeygenEndpoint.memAt, if_neg (neCounter i), addr8, addr]
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
    rw [state_mem s destination, KeygenEndpoint.memAt, if_neg hc, addr8, if_neg h1, addr, if_neg h0]


/-- The x12-relative endpoint uses thirteen ordinary instructions. -/
theorem block (image : Image) (code : CodeAt image) (s : MachineState)
    (chain : Reference.Chain)
    (pc : s.pc = 0x163c)
    (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (destination : s.getReg .x12 = 0x80020) :
    OrdinarySteps image s 13 (stateAt s) := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13⟩ := code
  have safe := KeygenEndpoint.address_safe s chain.val chain.isLt counter
  let s1 := execInstrBr s (.LUI .x28 128)
  let s2 := execInstrBr s1 (.LD .x6 .x28 1072)
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
      execInstrBr,pc,signExtend12,signExtend13,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  have coreEq : s11 = core s := rfl
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 128)) 12
  · simpa only [fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LD .x6 .x28 1072)) 11
  · have hp : s1.pc = 0x1640 := by simp [s1,execInstrBr,pc]
    simpa only [fetch_at,hp] using c1
  · simp [s1,s2,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      accessValid,rangeValid,MEMORY_BYTES]
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
      simpa [s6,s5,s4,s3,s2,s1,memoryArgumentsValid,execInstrBr,
        signExtend12,MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne] using safe0
    simp [ordinaryStep, valid, s7]
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x7 .x11 2024)) 5
  · have hp : s7.pc = 0x1658 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [fetch_at,hp] using c7
  · have valid : memoryArgumentsValid s7 (.SD .x7 .x11 (2024#12)) = true := by
      have safe8 := safe.2
      rw [← address_relative_next s destination] at safe8
      simpa [s7,s6,s5,s4,s3,s2,s1,memoryArgumentsValid,execInstrBr,
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
    (carry : Hoist.HeaderWordCarry s level tree leaf) :
    Hoist.HeaderWordCarry (EndpointShort.stateAt s) level tree leaf := by
  have old := endpoint_header_word_carry s level tree leaf chain counter carry
  rcases old with ⟨oldChain, oldStep, hc, hs, header, index, service, destination, seven⟩
  rcases carry with ⟨_, _, _, _, _, _, sourceService, sourceDestination, sourceSeven⟩
  obtain ⟨r5, r12, r31⟩ := EndpointShort.state_sticky s
  refine ⟨oldChain, oldStep, hc, hs, ?_, ?_, r5.trans sourceService,
    r12.trans sourceDestination, r31.trans sourceSeven⟩
  · rw [EndpointShort.state_mem s sourceDestination]
    exact header
  · intro i
    rw [EndpointShort.state_mem s sourceDestination]
    exact index i

/-- Drop-in endpoint theorem for the patched verifier image. -/
theorem store_endpoint_with_word_carry (s : MachineState) (level tree leaf : Nat)
    (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x163c)
    (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (valueWords : ∀ i : Fin 2,
      s.getMem (wordAddress 0x80020 i.val) = value.extractLsb' (64*i.val) 64)
    (carry : Hoist.HeaderWordCarry s level tree leaf) :
    ∃ final, OrdinarySteps verify s 13 final ∧
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
    EndpointShort.state_post s chain value pc counter destination valueWords
  have nextEntry : ChainEntry (EndpointShort.stateAt s) (chain.val+1) := by
    constructor
    · by_cases terminal : chain.val+1=46
      · simpa [terminal] using finalPC
      · have positive : chain.val+1 ≠ 0 := by omega
        simpa [terminal, positive] using finalPC
    · right; right
      refine ⟨(EndpointShort.state_regs s).1, ?_⟩
      rw [(EndpointShort.state_regs s).2.1, counter, BitVec.ofNat_add]
      rfl
  exact ⟨EndpointShort.stateAt s,
    EndpointShort.block verify EndpointShort.verify_code s chain pc counter destination,
    nextEntry, finalCounter, endpoints, ra, sp, frame,
    endpoint_short_header_word_carry s level tree leaf chain counter carry⟩


/-- info: 'SigGolfCandidate.Hypertree.Verifying.store_endpoint_with_word_carry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms store_endpoint_with_word_carry

end SigGolfCandidate.Hypertree.Verifying
