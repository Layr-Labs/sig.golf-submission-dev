import SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixData67

/-! The nine ordinary Fast2 instructions that prepare one WOTS chain. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastPrologue67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.Keygen
open SigGolfCandidate.Hypertree.Signing
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixData67
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

def EntryCode (image : Image) : Prop :=
  instructionAt image 0x1608 = some (.base (.LD .x13 .x22 0)) ∧
  instructionAt image 0x160c = some (.base (.LD .x14 .x22 8)) ∧
  instructionAt image 0x1610 = some (.base (.SD .x12 .x13 0)) ∧
  instructionAt image 0x1614 = some (.base (.SD .x12 .x14 8)) ∧
  instructionAt image 0x1618 = some (.base (.ADDI .x22 .x22 16)) ∧
  instructionAt image 0x161c = some (.base (.SB .x10 .x23 3)) ∧
  instructionAt image 0x1620 = some (.base (.LBU .x21 .x25 0)) ∧
  instructionAt image 0x1624 = some (.base (.ADDI .x25 .x25 1)) ∧
  instructionAt image 0x1628 = some (.base (.SB .x10 .x21 4))

theorem concrete_code : EntryCode image := by
  unfold EntryCode image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

def prefixState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x13 .x22 0)
  let s := execInstrBr s (.LD .x14 .x22 8)
  let s := execInstrBr s (.SD .x12 .x13 0)
  let s := execInstrBr s (.SD .x12 .x14 8)
  let s := execInstrBr s (.ADDI .x22 .x22 16)
  execInstrBr s (.SB .x10 .x23 3)

def prologueState (s : MachineState) : MachineState :=
  let s := prefixState s
  let s := execInstrBr s (.LBU .x21 .x25 0)
  let s := execInstrBr s (.ADDI .x25 .x25 1)
  execInstrBr s (.SB .x10 .x21 4)

theorem prologue_block (s : MachineState)
    (pc : s.pc = 0x1608)
    (valid0 : accessValid (s.getReg .x22) 8 = true)
    (valid8 : accessValid (s.getReg .x22 + 8) 8 = true)
    (digitValid : accessValid (s.getReg .x25) 1 = true)
    (src : s.getReg .x10 = 0x90000)
    (dst : s.getReg .x12 = 0x90020) :
    OrdinarySteps image s 9 (prologueState s) := by
  let s1 := execInstrBr s (.LD .x13 .x22 0)
  let s2 := execInstrBr s1 (.LD .x14 .x22 8)
  let s3 := execInstrBr s2 (.SD .x12 .x13 0)
  let s4 := execInstrBr s3 (.SD .x12 .x14 8)
  let s5 := execInstrBr s4 (.ADDI .x22 .x22 16)
  let s6 := execInstrBr s5 (.SB .x10 .x23 3)
  let s7 := execInstrBr s6 (.LBU .x21 .x25 0)
  let s8 := execInstrBr s7 (.ADDI .x25 .x25 1)
  change OrdinarySteps image s 9 (execInstrBr s8 (.SB .x10 .x21 4))
  rcases concrete_code with ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8⟩
  apply OrdinarySteps.step s s1 _ (.base (.LD .x13 .x22 0)) 8
  · simpa only [fetch_at, pc] using c0
  · simp [ordinaryStep, memoryArgumentsValid, signExtend12, valid0, s1]
  apply OrdinarySteps.step s1 s2 _ (.base (.LD .x14 .x22 8)) 7
  · have hp : s1.pc = 0x160c := by simp [s1, execInstrBr, pc]
    simpa only [fetch_at, hp] using c1
  · have ptr1 : s1.getReg .x22 = s.getReg .x22 := by
      simp [s1, execInstrBr, MachineState.getReg_setReg_ne]
    simp [ordinaryStep, memoryArgumentsValid, signExtend12, ptr1, s2]
    exact valid8
  apply OrdinarySteps.step s2 s3 _ (.base (.SD .x12 .x13 0)) 6
  · have hp : s2.pc = 0x1610 := by simp [s1, s2, execInstrBr, pc]
    simpa only [fetch_at, hp] using c2
  · have dst2 : s2.getReg .x12 = 0x90020 := by
      simp [s1, s2, execInstrBr, MachineState.getReg_setReg_ne, dst]
    simp [ordinaryStep, memoryArgumentsValid, signExtend12, dst2, s3,
      accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x12 .x14 8)) 5
  · have hp : s3.pc = 0x1614 := by simp [s1, s2, s3, execInstrBr, pc]
    simpa only [fetch_at, hp] using c3
  · have dst3 : s3.getReg .x12 = 0x90020 := by
      simp [s1, s2, s3, execInstrBr,
        MachineState.getReg_setReg_ne, dst]
    simp [ordinaryStep, memoryArgumentsValid, signExtend12, dst3, s4,
      accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x22 .x22 16)) 4
  · have hp : s4.pc = 0x1618 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simpa only [fetch_at, hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.SB .x10 .x23 3)) 3
  · have hp : s5.pc = 0x161c := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    simpa only [fetch_at, hp] using c5
  · have src5 : s5.getReg .x10 = 0x90000 := by
      simp [s1, s2, s3, s4, s5, execInstrBr,
        MachineState.getReg_setReg_ne, src]
    simp [ordinaryStep, memoryArgumentsValid, signExtend12, src5, s6,
      accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s6 s7 _ (.base (.LBU .x21 .x25 0)) 2
  · have hp : s6.pc = 0x1620 := by simp [s1, s2, s3, s4, s5, s6,
        execInstrBr, pc]
    simpa only [fetch_at, hp] using c6
  · have ptr6 : s6.getReg .x25 = s.getReg .x25 := by
      simp [s1, s2, s3, s4, s5, s6, execInstrBr,
        MachineState.getReg_setReg_ne]
    simp [ordinaryStep, memoryArgumentsValid, signExtend12, ptr6, s7]
    exact digitValid
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x25 .x25 1)) 1
  · have hp : s7.pc = 0x1624 := by simp [s1, s2, s3, s4, s5, s6, s7,
        execInstrBr, pc]
    simpa only [fetch_at, hp] using c7
  · rfl
  apply OrdinarySteps.step s8 (execInstrBr s8 (.SB .x10 .x21 4)) _
    (.base (.SB .x10 .x21 4)) 0
  · have hp : s8.pc = 0x1628 := by simp [s1, s2, s3, s4, s5, s6, s7,
        s8, execInstrBr, pc]
    simpa only [fetch_at, hp] using c8
  · have src8 : s8.getReg .x10 = 0x90000 := by
      simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr,
        MachineState.getReg_setReg_ne, src]
    simp [ordinaryStep, memoryArgumentsValid, signExtend12, src8,
      accessValid, rangeValid, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem prologue_pc (s : MachineState) :
    (prologueState s).pc = s.pc + 36 := by
  simp [prologueState, prefixState, execInstrBr, BitVec.add_assoc]

theorem prologue_digit_ptr (s : MachineState) :
    (prologueState s).getReg .x25 = s.getReg .x25 + 1 := by
  simp [prologueState, prefixState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

@[simp] private theorem getReg_setMem (s : MachineState) (a v : Word)
    (r : Reg) : (s.setMem a v).getReg r = s.getReg r := by
  cases r <;> rfl

@[simp] private theorem getReg_setByte (s : MachineState) (a : Word)
    (v : BitVec 8) (r : Reg) :
    (s.setByte a v).getReg r = s.getReg r := by
  simp [MachineState.setByte]

theorem prologue_reg_stable (s : MachineState) (r : Reg)
    (h13 : r ≠ .x13) (h14 : r ≠ .x14) (h22 : r ≠ .x22)
    (h21 : r ≠ .x21) (h25 : r ≠ .x25) :
    (prologueState s).getReg r = s.getReg r := by
  have n13 : .x13 ≠ r := Ne.symm h13
  have n14 : .x14 ≠ r := Ne.symm h14
  have n22 : .x22 ≠ r := Ne.symm h22
  have n21 : .x21 ≠ r := Ne.symm h21
  have n25 : .x25 ≠ r := Ne.symm h25
  simp [prologueState, prefixState, execInstrBr, MachineState.getReg_setReg_ne,
    n13, n14, n22, n21, n25]

theorem prefix_mem (s : MachineState) (a : Word)
    (src : s.getReg .x10 = 0x90000)
    (dst : s.getReg .x12 = 0x90020) :
    (prefixState s).getMem a =
      if a = 0x90000 then
        replaceByte (s.getMem 0x90000) 3 ((s.getReg .x23).truncate 8)
      else if a = 0x90028 then s.getMem (s.getReg .x22 + 8)
      else if a = 0x90020 then s.getMem (s.getReg .x22)
      else s.getMem a := by
  simp [prefixState, execInstrBr, signExtend12, MachineState.setByte,
    Expansion.mem_setMem, src, dst, alignToDword, byteOffset,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem prefix_reg_stable (s : MachineState) (r : Reg)
    (h13 : r ≠ .x13) (h14 : r ≠ .x14) (h22 : r ≠ .x22) :
    (prefixState s).getReg r = s.getReg r := by
  have n13 : .x13 ≠ r := Ne.symm h13
  have n14 : .x14 ≠ r := Ne.symm h14
  have n22 : .x22 ≠ r := Ne.symm h22
  simp [prefixState, execInstrBr, MachineState.getReg_setReg_ne,
    n13, n14, n22]

theorem prefix_digit_byte (s : MachineState)
    (src : s.getReg .x10 = 0x90000)
    (dst : s.getReg .x12 = 0x90020)
    (outside0 : alignToDword (s.getReg .x25) ≠ 0x90000)
    (outside1 : alignToDword (s.getReg .x25) ≠ 0x90020)
    (outside2 : alignToDword (s.getReg .x25) ≠ 0x90028) :
    (prefixState s).getByte (s.getReg .x25) =
      s.getByte (s.getReg .x25) := by
  simp only [MachineState.getByte]
  rw [prefix_mem s _ src dst, if_neg outside0,
    if_neg outside2, if_neg outside1]

theorem prologue_digit_reg (s : MachineState)
    (src : s.getReg .x10 = 0x90000)
    (dst : s.getReg .x12 = 0x90020)
    (outside0 : alignToDword (s.getReg .x25) ≠ 0x90000)
    (outside1 : alignToDword (s.getReg .x25) ≠ 0x90020)
    (outside2 : alignToDword (s.getReg .x25) ≠ 0x90028) :
    (prologueState s).getReg .x21 =
      (s.getByte (s.getReg .x25)).zeroExtend 64 := by
  have ptr : (prefixState s).getReg .x25 = s.getReg .x25 :=
    prefix_reg_stable s .x25 (by decide) (by decide) (by decide)
  have byte := prefix_digit_byte s src dst outside0 outside1 outside2
  simp [prologueState, execInstrBr, ptr, byte,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setByte, signExtend12]

theorem prologue_mem_from_prefix (s : MachineState) (a : Word)
    (src : s.getReg .x10 = 0x90000) :
    (prologueState s).getMem a =
      if a = 0x90000 then
        replaceByte ((prefixState s).getMem 0x90000) 4
          ((prefixState s).getByte (s.getReg .x25))
      else (prefixState s).getMem a := by
  have srcP : (prefixState s).getReg .x10 = 0x90000 :=
    (prefix_reg_stable s .x10 (by decide) (by decide) (by decide)).trans src
  have ptrP : (prefixState s).getReg .x25 = s.getReg .x25 :=
    prefix_reg_stable s .x25 (by decide) (by decide) (by decide)
  simp [prologueState, execInstrBr, MachineState.setByte,
    Expansion.mem_setMem, signExtend12, srcP, ptrP, alignToDword,
    byteOffset, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem prologue_mem (s : MachineState) (a : Word)
    (src : s.getReg .x10 = 0x90000)
    (dst : s.getReg .x12 = 0x90020)
    (outside0 : alignToDword (s.getReg .x25) ≠ 0x90000)
    (outside1 : alignToDword (s.getReg .x25) ≠ 0x90020)
    (outside2 : alignToDword (s.getReg .x25) ≠ 0x90028) :
    (prologueState s).getMem a =
      if a = 0x90000 then
        replaceByte
          (replaceByte (s.getMem 0x90000) 3 ((s.getReg .x23).truncate 8))
          4 (s.getByte (s.getReg .x25))
      else if a = 0x90028 then s.getMem (s.getReg .x22 + 8)
      else if a = 0x90020 then s.getMem (s.getReg .x22)
      else s.getMem a := by
  rw [prologue_mem_from_prefix s a src,
    prefix_digit_byte s src dst outside0 outside1 outside2,
    prefix_mem s 0x90000 src dst, prefix_mem s a src dst]
  split_ifs <;> simp_all

structure EntryData (s : MachineState) (base leaf : Nat)
    (chain : GroupedBalancedChecksum67.Chain)
    (message value : Reference.Digest) : Prop where
  oldHeader : ∃ oldChain oldStep : Nat,
    oldChain < 67 ∧ oldStep < 11 ∧
      s.getMem 0x90000 = KeygenDomain.header 2 base 0 oldChain oldStep
  indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x90008 i.val) =
    (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64
  witnessEq : ∀ i : Fin 2,
    s.getMem (s.getReg .x22 + BitVec.ofNat 64 (8*i.val)) =
      value.extractLsb' (64*i.val) 64
  digitEq : s.getByte (s.getReg .x25) =
    BitVec.ofNat 8 (GroupedBalancedChecksum67.digit message chain).val
  src : s.getReg .x10 = 0x90000
  len : s.getReg .x11 = 384
  dst : s.getReg .x12 = 0x90020
  service : s.getReg .x5 = 1
  chainReg : s.getReg .x23 = BitVec.ofNat 64 chain.val
  limitReg : s.getReg .x20 =
    BitVec.ofNat 64 (GroupedBalancedChecksum67.maxDigit chain)
  digitOutside0 : alignToDword (s.getReg .x25) ≠ 0x90000
  digitOutside1 : alignToDword (s.getReg .x25) ≠ 0x90020
  digitOutside2 : alignToDword (s.getReg .x25) ≠ 0x90028

theorem decoder_ptr_safe (chain : Nat) (bound : chain < 67) :
    accessValid (BitVec.ofNat 64 (0x80600 + chain)) 1 = true ∧
    alignToDword (BitVec.ofNat 64 (0x80600 + chain)) ≠ 0x90000 ∧
    alignToDword (BitVec.ofNat 64 (0x80600 + chain)) ≠ 0x90020 ∧
    alignToDword (BitVec.ofNat 64 (0x80600 + chain)) ≠ 0x90028 := by
  interval_cases chain <;> decide

theorem prologue_loop_data (s : MachineState) (base leaf : Nat)
    (chain : GroupedBalancedChecksum67.Chain)
    (message value : Reference.Digest) (baseBound : base < 256)
    (data : EntryData s base leaf chain message value) :
    LoopData (prologueState s) base leaf chain
      (GroupedBalancedChecksum67.digit message chain).val value := by
  let digit := (GroupedBalancedChecksum67.digit message chain).val
  have digitBound : digit < 256 := by
    have upper := GroupedBalancedChecksum67.digit_le_max message chain
    have max := max_digit_le_ten chain
    omega
  have byteChain : ((s.getReg .x23).truncate 8) =
      BitVec.ofNat 8 chain.val := by
    rw [data.chainReg]
    simp [BitVec.truncate_eq_setWidth]
  constructor
  · obtain ⟨oldChain, oldStep, oldChainBound, oldStepBound,
      oldHeader⟩ := data.oldHeader
    refine ⟨digit, by omega, ?_⟩
    rw [prologue_mem s 0x90000 data.src data.dst data.digitOutside0
      data.digitOutside1 data.digitOutside2]
    simp only
    rw [oldHeader, byteChain, data.digitEq]
    exact Verifying.Hoist.header_chain_step_replace base 0 oldChain
      oldStep chain.val digit baseBound (by decide) (by omega)
      (by omega) (by have := chain.isLt; omega) digitBound
  · intro i
    rw [prologue_mem s _ data.src data.dst data.digitOutside0
      data.digitOutside1 data.digitOutside2]
    have neq0 : wordAddress 0x90008 i.val ≠ 0x90000 := by
      fin_cases i <;> decide
    have neq1 : wordAddress 0x90008 i.val ≠ 0x90028 := by
      fin_cases i <;> decide
    have neq2 : wordAddress 0x90008 i.val ≠ 0x90020 := by
      fin_cases i <;> decide
    simp only [if_neg neq0, if_neg neq1, if_neg neq2]
    exact data.indexEq i
  · intro i
    fin_cases i
    · change (prologueState s).getMem 0x90020 =
        value.extractLsb' 0 64
      rw [prologue_mem s 0x90020 data.src data.dst data.digitOutside0
        data.digitOutside1 data.digitOutside2]
      simpa [wordAddress] using data.witnessEq 0
    · change (prologueState s).getMem 0x90028 =
        value.extractLsb' 64 64
      rw [prologue_mem s 0x90028 data.src data.dst data.digitOutside0
        data.digitOutside1 data.digitOutside2]
      simpa [wordAddress] using data.witnessEq 1
  · constructor
    · exact (prologue_reg_stable s .x5 (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans data.service
    · exact (prologue_reg_stable s .x10 (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans data.src
    · exact (prologue_reg_stable s .x11 (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans data.len
    · exact (prologue_reg_stable s .x12 (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans data.dst
    · rw [prologue_digit_reg s data.src data.dst
        data.digitOutside0 data.digitOutside1 data.digitOutside2,
        data.digitEq]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.zeroExtend_eq_setWidth,
        BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    · exact (prologue_reg_stable s .x20 (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans data.limitReg

/-- Nine entry instructions followed by the exact Fast2 WOTS suffix loop.
The decoder digit and 16-byte witness value enter through `EntryData`; the
result is the corresponding functional chain endpoint for every hash oracle. -/
theorem run_chain_from_entry (hash : Hash) (s : MachineState)
    (base leaf : Nat) (chain : GroupedBalancedChecksum67.Chain)
    (message value : Reference.Digest)
    (pc : s.pc = 0x1608)
    (valid0 : accessValid (s.getReg .x22) 8 = true)
    (valid8 : accessValid (s.getReg .x22 + 8) 8 = true)
    (digitValid : accessValid (s.getReg .x25) 1 = true)
    (baseBound : base < 256)
    (data : EntryData s base leaf chain message value) :
    ∃ final,
      Trace hash image s
        (4 * (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) + 10)
        (11 * (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) + 10)
        (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val)
        (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) final ∧
      final.pc = 0x1640 ∧
      LoopData final base leaf chain (GroupedBalancedChecksum67.maxDigit chain)
        (walk (GroupedBalancedUpperTree67.chainHash hash base leaf chain)
          (GroupedBalancedChecksum67.digit message chain).val
          (GroupedBalancedChecksum67.maxDigit chain -
            (GroupedBalancedChecksum67.digit message chain).val) value) ∧
      (∀ a, OutsideTick a → final.getMem a = s.getMem a) ∧
      final.getReg .x23 = s.getReg .x23 ∧
      final.getReg .x24 = s.getReg .x24 ∧
      final.getReg .x25 = s.getReg .x25 + 1 ∧
      final.getReg .x20 = s.getReg .x20 := by
  have pre := prologue_block s pc valid0 valid8 digitValid data.src data.dst
  have readyPC : (prologueState s).pc = 0x162c := by
    rw [prologue_pc, pc]
    decide
  have readyData := prologue_loop_data s base leaf chain message value
    baseBound data
  obtain ⟨final, tail, finalPC, finalData, finalFrame, finalRegs⟩ :=
    run_chain_suffix_data hash (prologueState s) base leaf chain
      message value readyPC baseBound readyData
  refine ⟨final, ?_, finalPC, finalData, ?_, ?_, ?_, ?_, ?_⟩
  · convert pre.trace.trans tail using 1 <;> omega
  · intro a outside
    rw [finalFrame a outside]
    rw [prologue_mem s a data.src data.dst data.digitOutside0
      data.digitOutside1 data.digitOutside2]
    have h0 : a ≠ 0x90000 := outside.1
    have h1 : a ≠ 0x90028 := by
      simpa [wordAddress] using outside.2 (1 : Fin 4)
    have h2 : a ≠ 0x90020 := by
      simpa [wordAddress] using outside.2 (0 : Fin 4)
    simp only [if_neg h0, if_neg h1, if_neg h2]
  · exact (finalRegs .x23 (by decide)).trans
      (prologue_reg_stable s .x23 (by decide) (by decide)
        (by decide) (by decide) (by decide))
  · exact (finalRegs .x24 (by decide)).trans
      (prologue_reg_stable s .x24 (by decide) (by decide)
        (by decide) (by decide) (by decide))
  · exact (finalRegs .x25 (by decide)).trans (prologue_digit_ptr s)
  · exact (finalRegs .x20 (by decide)).trans
      (prologue_reg_stable s .x20 (by decide) (by decide)
        (by decide) (by decide) (by decide))

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastPrologue67
