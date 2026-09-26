import SigGolfCandidate.Hypertree.GroupedBalancedByteFastLimit67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedByteFastEndpoint67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedByteFastIteration67. -/
section
/-! Fast2's five-instruction WOTS endpoint copy. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastEndpoint67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.Keygen
open SigGolfCandidate.Hypertree.Signing
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixData67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastPrologue67
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

def CopyCode (image : Image) : Prop :=
  instructionAt image 0x1640 = some (.base (.LD .x13 .x12 0)) ∧
  instructionAt image 0x1644 = some (.base (.LD .x14 .x12 8)) ∧
  instructionAt image 0x1648 = some (.base (.SD .x24 .x13 0)) ∧
  instructionAt image 0x164c = some (.base (.SD .x24 .x14 8)) ∧
  instructionAt image 0x1650 = some (.base (.ADDI .x24 .x24 16))

theorem concrete_code : CopyCode image := by
  unfold CopyCode image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

def copyState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x13 .x12 0)
  let s := execInstrBr s (.LD .x14 .x12 8)
  let s := execInstrBr s (.SD .x24 .x13 0)
  let s := execInstrBr s (.SD .x24 .x14 8)
  execInstrBr s (.ADDI .x24 .x24 16)

@[simp] private theorem getReg_setMem (s : MachineState) (a v : Word)
    (r : Reg) : (s.setMem a v).getReg r = s.getReg r := by
  cases r <;> rfl

theorem copy_block (s : MachineState)
    (pc : s.pc = 0x1640)
    (src : s.getReg .x12 = 0x90020)
    (dst0 : accessValid (s.getReg .x24) 8 = true)
    (dst8 : accessValid (s.getReg .x24 + 8) 8 = true) :
    OrdinarySteps image s 5 (copyState s) := by
  let s1 := execInstrBr s (.LD .x13 .x12 0)
  let s2 := execInstrBr s1 (.LD .x14 .x12 8)
  let s3 := execInstrBr s2 (.SD .x24 .x13 0)
  let s4 := execInstrBr s3 (.SD .x24 .x14 8)
  change OrdinarySteps image s 5 (execInstrBr s4 (.ADDI .x24 .x24 16))
  obtain ⟨c0,c1,c2,c3,c4⟩ := concrete_code
  apply OrdinarySteps.step s s1 _ (.base (.LD .x13 .x12 0)) 4
  · simpa only [fetch_at,pc] using c0
  · simp [ordinaryStep,memoryArgumentsValid,signExtend12,src,
      accessValid,rangeValid,MEMORY_BYTES,s1]
  apply OrdinarySteps.step s1 s2 _ (.base (.LD .x14 .x12 8)) 3
  · have hp : s1.pc = 0x1644 := by simp [s1,execInstrBr,pc]
    simpa only [fetch_at,hp] using c1
  · have src1 : s1.getReg .x12 = 0x90020 := by
      simp [s1,execInstrBr,MachineState.getReg_setReg_ne,src]
    simp [ordinaryStep,memoryArgumentsValid,signExtend12,src1,
      accessValid,rangeValid,MEMORY_BYTES,s2]
  apply OrdinarySteps.step s2 s3 _ (.base (.SD .x24 .x13 0)) 2
  · have hp : s2.pc = 0x1648 := by simp [s1,s2,execInstrBr,pc]
    simpa only [fetch_at,hp] using c2
  · have ptr2 : s2.getReg .x24 = s.getReg .x24 := by
      simp [s1,s2,execInstrBr,MachineState.getReg_setReg_ne]
    simp [ordinaryStep,memoryArgumentsValid,signExtend12,ptr2,s3]
    exact dst0
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x24 .x14 8)) 1
  · have hp : s3.pc = 0x164c := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [fetch_at,hp] using c3
  · have ptr3 : s3.getReg .x24 = s.getReg .x24 := by
      simp [s1,s2,s3,execInstrBr,MachineState.getReg_setReg_ne]
    simp [ordinaryStep,memoryArgumentsValid,signExtend12,ptr3,s4]
    exact dst8
  apply OrdinarySteps.step s4 (execInstrBr s4 (.ADDI .x24 .x24 16)) _
    (.base (.ADDI .x24 .x24 16)) 0
  · have hp : s4.pc = 0x1650 := by
      simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [fetch_at,hp] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem copy_pc (s : MachineState) (pc : s.pc = 0x1640) :
    (copyState s).pc = 0x1654 := by
  simp [copyState,execInstrBr,pc]

theorem copy_ptr (s : MachineState) :
    (copyState s).getReg .x24 = s.getReg .x24 + 16 := by
  simp [copyState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem copy_reg_stable (s : MachineState) (r : Reg)
    (h13 : r ≠ .x13) (h14 : r ≠ .x14) (h24 : r ≠ .x24) :
    (copyState s).getReg r = s.getReg r := by
  have n13 : .x13 ≠ r := Ne.symm h13
  have n14 : .x14 ≠ r := Ne.symm h14
  have n24 : .x24 ≠ r := Ne.symm h24
  simp [copyState,execInstrBr,MachineState.getReg_setReg_ne,
    n13,n14,n24]

theorem copy_mem (s : MachineState) (a : Word) :
    (copyState s).getMem a =
      if a = s.getReg .x24 + 8 then s.getMem (s.getReg .x12 + 8)
      else if a = s.getReg .x24 then s.getMem (s.getReg .x12)
      else s.getMem a := by
  simp [copyState,execInstrBr,signExtend12,Expansion.mem_setMem,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

private theorem ptr_ne_next (p : Word) : p ≠ p + 8 := by
  intro h
  have hn := congrArg (fun x : Word => x - p) h
  rw [BitVec.sub_self, BitVec.add_comm p 8, BitVec.add_sub_cancel] at hn
  exact (by decide : (0#64) ≠ 8) hn

theorem copy_value (s : MachineState) (value : Reference.Digest)
    (src : s.getReg .x12 = 0x90020)
    (valueEq : ∀ i : Fin 2,
      s.getMem (wordAddress 0x90020 i.val) =
        value.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (copyState s).getMem
        (s.getReg .x24 + BitVec.ofNat 64 (8*i.val)) =
        value.extractLsb' (64*i.val) 64 := by
  intro i
  fin_cases i
  · norm_num
    rw [copy_mem]
    simp only [if_neg (ptr_ne_next _), src]
    simpa [wordAddress] using valueEq 0
  · norm_num
    change (copyState s).getMem (s.getReg .x24 + 8) =
      value.extractLsb' 64 64
    rw [copy_mem]
    simp only [src]
    simpa [wordAddress] using valueEq 1

/-- One complete Fast2 WOTS recovery, including its endpoint write to x24. -/
theorem run_chain_and_copy (hash : Hash) (s : MachineState)
    (base leaf : Nat) (chain : GroupedBalancedChecksum67.Chain)
    (message value : Reference.Digest)
    (pc : s.pc = 0x1608)
    (valid0 : accessValid (s.getReg .x22) 8 = true)
    (valid8 : accessValid (s.getReg .x22 + 8) 8 = true)
    (digitValid : accessValid (s.getReg .x25) 1 = true)
    (dst0 : accessValid (s.getReg .x24) 8 = true)
    (dst8 : accessValid (s.getReg .x24 + 8) 8 = true)
    (baseBound : base < 256)
    (data : EntryData s base leaf chain message value) :
    ∃ final,
      Trace hash image s
        (4 * (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) + 15)
        (11 * (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) + 15)
        (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val)
        (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) final ∧
      final.pc = 0x1654 ∧
      (∀ i : Fin 2,
        final.getMem (s.getReg .x24 + BitVec.ofNat 64 (8*i.val)) =
          (walk (GroupedBalancedUpperTree67.chainHash hash base leaf chain)
            (GroupedBalancedChecksum67.digit message chain).val
            (GroupedBalancedChecksum67.maxDigit chain -
              (GroupedBalancedChecksum67.digit message chain).val) value).extractLsb'
              (64*i.val) 64) ∧
      final.getReg .x23 = s.getReg .x23 ∧
      final.getReg .x24 = s.getReg .x24 + 16 ∧
      final.getReg .x25 = s.getReg .x25 + 1 ∧
      final.getReg .x20 = s.getReg .x20 ∧
      (∀ a, OutsideTick a → a ≠ s.getReg .x24 →
        a ≠ s.getReg .x24 + 8 → final.getMem a = s.getMem a) := by
  obtain ⟨wots, first, wotsPC, wotsData, wotsFrame,
    wotsChain, wotsPtr, wotsDigitPtr, wotsLimit⟩ :=
    run_chain_from_entry hash s base leaf chain message value pc
      valid0 valid8 digitValid baseBound data
  have dst0' : accessValid (wots.getReg .x24) 8 = true := by
    rw [wotsPtr]
    exact dst0
  have dst8' : accessValid (wots.getReg .x24 + 8) 8 = true := by
    rw [wotsPtr]
    exact dst8
  have second := copy_block wots wotsPC wotsData.fields.dst dst0' dst8'
  let final := copyState wots
  have copiedValue := copy_value wots
    (walk (GroupedBalancedUpperTree67.chainHash hash base leaf chain)
      (GroupedBalancedChecksum67.digit message chain).val
      (GroupedBalancedChecksum67.maxDigit chain -
        (GroupedBalancedChecksum67.digit message chain).val) value)
    wotsData.fields.dst wotsData.valueEq
  refine ⟨final, ?_, copy_pc wots wotsPC, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert first.trans second.trace using 1 <;> omega
  · intro i
    simpa only [final,wotsPtr] using copiedValue i
  · exact (copy_reg_stable wots .x23 (by decide) (by decide)
      (by decide)).trans wotsChain
  · rw [copy_ptr,wotsPtr]
  · exact (copy_reg_stable wots .x25 (by decide) (by decide)
      (by decide)).trans wotsDigitPtr
  · exact (copy_reg_stable wots .x20 (by decide) (by decide)
      (by decide)).trans wotsLimit
  · intro a outside notLow notHigh
    rw [copy_mem]
    simp only [wotsPtr, if_neg notHigh, if_neg notLow]
    exact wotsFrame a outside

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastEndpoint67

end

/-! Complete ordinary-radix Fast2 WOTS iteration, from one chain entry to the
next, with exact resource counts. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastIteration67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastPrologue67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastEndpoint67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastLimit67
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

theorem short_iteration (hash : Hash) (s : MachineState)
    (base leaf : Nat) (chain : GroupedBalancedChecksum67.Chain)
    (message value : Reference.Digest)
    (short : chain.val < 64)
    (pc : s.pc = 0x1608)
    (valid0 : accessValid (s.getReg .x22) 8 = true)
    (valid8 : accessValid (s.getReg .x22 + 8) 8 = true)
    (digitValid : accessValid (s.getReg .x25) 1 = true)
    (dst0 : accessValid (s.getReg .x24) 8 = true)
    (dst8 : accessValid (s.getReg .x24 + 8) 8 = true)
    (baseBound : base < 256)
    (data : EntryData s base leaf chain message value) :
    ∃ final,
      Trace hash image s
        (4 * (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) + 18)
        (11 * (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) + 18)
        (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val)
        (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) final ∧
      final.pc = 0x1608 ∧
      final.getReg .x23 = BitVec.ofNat 64 (chain.val + 1) ∧
      final.getReg .x20 =
        BitVec.ofNat 64
          (GroupedBalancedChecksum67.maxDigit
            ⟨chain.val + 1, by omega⟩) ∧
      final.getReg .x24 = s.getReg .x24 + 16 ∧
      final.getReg .x25 = s.getReg .x25 + 1 ∧
      (∀ i : Fin 2,
        final.getMem (s.getReg .x24 + BitVec.ofNat 64 (8*i.val)) =
          (walk (GroupedBalancedUpperTree67.chainHash hash base leaf chain)
            (GroupedBalancedChecksum67.digit message chain).val
            (GroupedBalancedChecksum67.maxDigit chain -
              (GroupedBalancedChecksum67.digit message chain).val) value).extractLsb'
              (64*i.val) 64) := by
  obtain ⟨copied, core, copiedPC, copiedValue, copiedChain,
    copiedPtr, copiedDigitPtr, copiedLimit, _⟩ :=
    run_chain_and_copy hash s base leaf chain message value pc
      valid0 valid8 digitValid dst0 dst8 baseBound data
  have copiedChainVal : copied.getReg .x23 = BitVec.ofNat 64 chain.val :=
    copiedChain.trans data.chainReg
  have tail := advance_block copied copiedPC
  have nextPC := advance_short_pc copied chain.val copiedPC
    copiedChainVal short
  have nextChain := advance_chain copied chain.val copiedChainVal
  have nextLimit : (advanceState copied).getReg .x20 =
      BitVec.ofNat 64
        (GroupedBalancedChecksum67.maxDigit
          ⟨chain.val + 1, by omega⟩) := by
    rw [advance_limit,copiedLimit,data.limitReg]
    simp [GroupedBalancedChecksum67.maxDigit,
      show chain.val < 65 by omega,
      show chain.val + 1 < 65 by omega]
  refine ⟨advanceState copied, ?_, nextPC, nextChain,
    nextLimit, ?_, ?_, ?_⟩
  · convert core.trans tail.trace using 1 <;> omega
  · exact (advance_reg_stable copied .x24 (by decide) (by decide)).trans
      copiedPtr
  · exact (advance_reg_stable copied .x25 (by decide) (by decide)).trans
      copiedDigitPtr
  · intro i
    rw [advance_mem]
    exact copiedValue i

theorem chain64_iteration (hash : Hash) (s : MachineState)
    (base leaf : Nat) (message value : Reference.Digest)
    (pc : s.pc = 0x1608)
    (valid0 : accessValid (s.getReg .x22) 8 = true)
    (valid8 : accessValid (s.getReg .x22 + 8) 8 = true)
    (digitValid : accessValid (s.getReg .x25) 1 = true)
    (dst0 : accessValid (s.getReg .x24) 8 = true)
    (dst8 : accessValid (s.getReg .x24 + 8) 8 = true)
    (baseBound : base < 256)
    (data : EntryData s base leaf (64 : Fin 67) message value) :
    ∃ final,
      Trace hash image s
        (4 * (3 - (GroupedBalancedChecksum67.digit message (64 : Fin 67)).val) + 22)
        (11 * (3 - (GroupedBalancedChecksum67.digit message (64 : Fin 67)).val) + 22)
        (3 - (GroupedBalancedChecksum67.digit message (64 : Fin 67)).val)
        (3 - (GroupedBalancedChecksum67.digit message (64 : Fin 67)).val) final ∧
      final.pc = 0x1608 ∧
      final.getReg .x23 = 65 ∧ final.getReg .x20 = 8 ∧
      final.getReg .x24 = s.getReg .x24 + 16 ∧
      final.getReg .x25 = s.getReg .x25 + 1 ∧
      (∀ i : Fin 2,
        final.getMem (s.getReg .x24 + BitVec.ofNat 64 (8*i.val)) =
          (walk (GroupedBalancedUpperTree67.chainHash hash base leaf (64 : Fin 67))
            (GroupedBalancedChecksum67.digit message (64 : Fin 67)).val
            (3 - (GroupedBalancedChecksum67.digit message (64 : Fin 67)).val)
            value).extractLsb' (64*i.val) 64) := by
  obtain ⟨copied, core, copiedPC, copiedValue, copiedChain,
    copiedPtr, copiedDigitPtr, _, _⟩ :=
    run_chain_and_copy hash s base leaf (64 : Fin 67) message value pc
      valid0 valid8 digitValid dst0 dst8 baseBound data
  have copiedChainVal : copied.getReg .x23 = 64 :=
    copiedChain.trans data.chainReg
  have tail := next65_block copied copiedPC copiedChainVal
  refine ⟨next65State copied, ?_, next65_pc copied copiedPC copiedChainVal,
    next65_chain copied copiedChainVal, next65_limit copied, ?_, ?_, ?_⟩
  · simp [GroupedBalancedChecksum67.maxDigit] at core
    convert core.trans tail.trace using 1 <;> omega
  · exact (next65_reg_stable copied .x24 (by decide) (by decide)
      (by decide) (by decide)).trans copiedPtr
  · exact (next65_reg_stable copied .x25 (by decide) (by decide)
      (by decide) (by decide)).trans copiedDigitPtr
  · intro i
    rw [next65_mem]
    simpa [GroupedBalancedChecksum67.maxDigit] using copiedValue i

theorem chain65_iteration (hash : Hash) (s : MachineState)
    (base leaf : Nat) (message value : Reference.Digest)
    (pc : s.pc = 0x1608)
    (valid0 : accessValid (s.getReg .x22) 8 = true)
    (valid8 : accessValid (s.getReg .x22 + 8) 8 = true)
    (digitValid : accessValid (s.getReg .x25) 1 = true)
    (dst0 : accessValid (s.getReg .x24) 8 = true)
    (dst8 : accessValid (s.getReg .x24 + 8) 8 = true)
    (baseBound : base < 256)
    (data : EntryData s base leaf (65 : Fin 67) message value) :
    ∃ final,
      Trace hash image s
        (4 * (8 - (GroupedBalancedChecksum67.digit message (65 : Fin 67)).val) + 24)
        (11 * (8 - (GroupedBalancedChecksum67.digit message (65 : Fin 67)).val) + 24)
        (8 - (GroupedBalancedChecksum67.digit message (65 : Fin 67)).val)
        (8 - (GroupedBalancedChecksum67.digit message (65 : Fin 67)).val) final ∧
      final.pc = 0x1608 ∧
      final.getReg .x23 = 66 ∧ final.getReg .x20 = 10 ∧
      final.getReg .x24 = s.getReg .x24 + 16 ∧
      final.getReg .x25 = s.getReg .x25 + 1 ∧
      (∀ i : Fin 2,
        final.getMem (s.getReg .x24 + BitVec.ofNat 64 (8*i.val)) =
          (walk (GroupedBalancedUpperTree67.chainHash hash base leaf (65 : Fin 67))
            (GroupedBalancedChecksum67.digit message (65 : Fin 67)).val
            (8 - (GroupedBalancedChecksum67.digit message (65 : Fin 67)).val)
            value).extractLsb' (64*i.val) 64) := by
  obtain ⟨copied, core, copiedPC, copiedValue, copiedChain,
    copiedPtr, copiedDigitPtr, _, _⟩ :=
    run_chain_and_copy hash s base leaf (65 : Fin 67) message value pc
      valid0 valid8 digitValid dst0 dst8 baseBound data
  have copiedChainVal : copied.getReg .x23 = 65 :=
    copiedChain.trans data.chainReg
  have tail := next66_block copied copiedPC copiedChainVal
  refine ⟨next66State copied, ?_, next66_pc copied copiedPC copiedChainVal,
    next66_chain copied copiedChainVal, next66_limit copied, ?_, ?_, ?_⟩
  · simp [GroupedBalancedChecksum67.maxDigit] at core
    convert core.trans tail.trace using 1 <;> omega
  · exact (next66_reg_stable copied .x24 (by decide) (by decide)
      (by decide) (by decide)).trans copiedPtr
  · exact (next66_reg_stable copied .x25 (by decide) (by decide)
      (by decide) (by decide)).trans copiedDigitPtr
  · intro i
    rw [next66_mem]
    simpa [GroupedBalancedChecksum67.maxDigit] using copiedValue i

theorem chain66_iteration (hash : Hash) (s : MachineState)
    (base leaf : Nat) (message value : Reference.Digest)
    (pc : s.pc = 0x1608)
    (valid0 : accessValid (s.getReg .x22) 8 = true)
    (valid8 : accessValid (s.getReg .x22 + 8) 8 = true)
    (digitValid : accessValid (s.getReg .x25) 1 = true)
    (dst0 : accessValid (s.getReg .x24) 8 = true)
    (dst8 : accessValid (s.getReg .x24 + 8) 8 = true)
    (baseBound : base < 256)
    (data : EntryData s base leaf (66 : Fin 67) message value) :
    ∃ final,
      Trace hash image s
        (4 * (10 - (GroupedBalancedChecksum67.digit message (66 : Fin 67)).val) + 23)
        (11 * (10 - (GroupedBalancedChecksum67.digit message (66 : Fin 67)).val) + 23)
        (10 - (GroupedBalancedChecksum67.digit message (66 : Fin 67)).val)
        (10 - (GroupedBalancedChecksum67.digit message (66 : Fin 67)).val) final ∧
      final.pc = 0x1684 ∧
      final.getReg .x23 = 67 ∧ final.getReg .x20 = 10 ∧
      final.getReg .x24 = s.getReg .x24 + 16 ∧
      final.getReg .x25 = s.getReg .x25 + 1 ∧
      (∀ i : Fin 2,
        final.getMem (s.getReg .x24 + BitVec.ofNat 64 (8*i.val)) =
          (walk (GroupedBalancedUpperTree67.chainHash hash base leaf (66 : Fin 67))
            (GroupedBalancedChecksum67.digit message (66 : Fin 67)).val
            (10 - (GroupedBalancedChecksum67.digit message (66 : Fin 67)).val)
            value).extractLsb' (64*i.val) 64) := by
  obtain ⟨copied, core, copiedPC, copiedValue, copiedChain,
    copiedPtr, copiedDigitPtr, copiedLimit, _⟩ :=
    run_chain_and_copy hash s base leaf (66 : Fin 67) message value pc
      valid0 valid8 digitValid dst0 dst8 baseBound data
  have copiedChainVal : copied.getReg .x23 = 66 :=
    copiedChain.trans data.chainReg
  have tail := next_done_block copied copiedPC copiedChainVal
  refine ⟨nextDoneState copied, ?_, next_done_pc copied copiedPC
    copiedChainVal, next_done_chain copied copiedChainVal, ?_, ?_, ?_, ?_⟩
  · simp [GroupedBalancedChecksum67.maxDigit] at core
    convert core.trans tail.trace using 1 <;> omega
  · exact (next_done_reg_stable copied .x20 (by decide) (by decide)
      (by decide)).trans (copiedLimit.trans data.limitReg) |>.trans (by decide)
  · exact (next_done_reg_stable copied .x24 (by decide) (by decide)
      (by decide)).trans copiedPtr
  · exact (next_done_reg_stable copied .x25 (by decide) (by decide)
      (by decide)).trans copiedDigitPtr
  · intro i
    rw [next_done_mem]
    simpa [GroupedBalancedChecksum67.maxDigit] using copiedValue i

def overhead (chain : GroupedBalancedChecksum67.Chain) : Nat :=
  if chain.val < 64 then 18
  else if chain.val = 64 then 22
  else if chain.val = 65 then 24
  else 23

def iterationCycles (message : Reference.Digest)
    (chain : GroupedBalancedChecksum67.Chain) : Nat :=
  11 * (GroupedBalancedChecksum67.maxDigit chain -
    (GroupedBalancedChecksum67.digit message chain).val) + overhead chain

theorem overhead_sum :
    (∑ chain : GroupedBalancedChecksum67.Chain, overhead chain) = 1221 := by
  decide

/-- The 67 concrete per-chain traces contribute exactly this many cycles to
one Fast2 upper leaf, before its leaf compressor and Merkle path. -/
theorem all_iteration_cycles (message : Reference.Digest) :
    (∑ chain : GroupedBalancedChecksum67.Chain,
      iterationCycles message chain) =
      11 * GroupedBalancedChecksum67.suffixCost message + 1221 := by
  simp only [iterationCycles, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [overhead_sum]
  rfl

theorem all_iteration_cycles_le (message : Reference.Digest) :
    (∑ chain : GroupedBalancedChecksum67.Chain,
      iterationCycles message chain) ≤ 2299 := by
  rw [all_iteration_cycles]
  have h := GroupedBalancedChecksum67.suffix_cost_le message
  omega

theorem iteration_model_bridge (message : Reference.Digest) :
    (∑ chain : GroupedBalancedChecksum67.Chain,
      iterationCycles message chain) +
      (if GroupedBalancedQuaternary.needsFlip message then 0 else 1) =
      GroupedBalancedFastCycleModel67.groupCycles message + 1221 := by
  rw [all_iteration_cycles]
  unfold GroupedBalancedFastCycleModel67.groupCycles
  omega

theorem iterations_model_bridge (messages : List Reference.Digest) :
    (messages.map fun message =>
      ∑ chain : GroupedBalancedChecksum67.Chain,
        iterationCycles message chain).sum +
    (messages.map fun message =>
      if GroupedBalancedQuaternary.needsFlip message then 0 else 1).sum =
    (messages.map GroupedBalancedFastCycleModel67.groupCycles).sum +
      1221 * messages.length := by
  induction messages with
  | nil => simp
  | cons message rest ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      have bridge := iteration_model_bridge message
      omega

/-- The Fast2 cycle model's fixed term consists of 1,221 certified WOTS
iteration cycles for each of 45 upper leaves, plus 48,486 cycles for the
decoder, leaf compressor, Merkle path, bottom tree, and fixed setup. -/
theorem verifier_model_split (messages : List Reference.Digest)
    (rightEdges : Nat) (groups : messages.length = 45) :
    GroupedBalancedFastCycleModel67.verifierCycles messages rightEdges =
      48486 +
      (messages.map fun message =>
        ∑ chain : GroupedBalancedChecksum67.Chain,
          iterationCycles message chain).sum +
      (messages.map fun message =>
        if GroupedBalancedQuaternary.needsFlip message then 0 else 1).sum +
      rightEdges := by
  have bridge := iterations_model_bridge messages
  unfold GroupedBalancedFastCycleModel67.verifierCycles
  omega

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastIteration67
