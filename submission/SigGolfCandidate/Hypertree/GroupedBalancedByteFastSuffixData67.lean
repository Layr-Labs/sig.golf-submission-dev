import SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixLoop67
import SigGolfCandidate.Hypertree.GroupedBalancedUpperTree67
import SigGolfCandidate.Hypertree.VerifyHoistWord

/-! Functional query data for the direct67 Fast2 in-place suffix loop. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.Signing
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixLoop67
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

private theorem replace_step_bv (l f c old next : BitVec 8) :
    replaceByte
      (2#64 + ((l.zeroExtend 64) <<< 8) + ((f.zeroExtend 64) <<< 16) +
        ((c.zeroExtend 64) <<< 24) + ((old.zeroExtend 64) <<< 32))
      4 next =
      2#64 + ((l.zeroExtend 64) <<< 8) + ((f.zeroExtend 64) <<< 16) +
        ((c.zeroExtend 64) <<< 24) + ((next.zeroExtend 64) <<< 32) := by
  rw [Verifying.Hoist.prefix32 l f c]
  exact Verifying.Hoist.replace32 _ old next

theorem header_step_replace (base chain old next : Nat)
    (baseBound : base < 256) (chainBound : chain < 256)
    (oldBound : old < 256) (nextBound : next < 256) :
    replaceByte (KeygenDomain.header 2 base 0 chain old) 4
      (BitVec.ofNat 8 next) =
      KeygenDomain.header 2 base 0 chain next := by
  rw [Verifying.Hoist.header_unpack base 0 chain old baseBound (by decide)
      chainBound oldBound,
    Verifying.Hoist.header_unpack base 0 chain next baseBound (by decide)
      chainBound nextBound]
  exact replace_step_bv (BitVec.ofNat 8 base) (BitVec.ofNat 8 0)
    (BitVec.ofNat 8 chain) (BitVec.ofNat 8 old) (BitVec.ofNat 8 next)

abbrev Chain := GroupedBalancedChecksum67.Chain

/-- The header may still contain the preceding step at the branch. Fast2's
first instruction of each hash round writes the current step byte. -/
structure LoopData (s : MachineState) (base leaf : Nat)
    (chain : Chain) (step : Nat) (value : Reference.Digest) : Prop where
  headerCarry : ∃ old, old < 11 ∧
    s.getMem 0x90000 = KeygenDomain.header 2 base 0 chain.val old
  indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x90008 i.val) =
    (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64
  valueEq : ∀ i : Fin 2, s.getMem (wordAddress 0x90020 i.val) =
    value.extractLsb' (64*i.val) 64
  fields : Fields s step (GroupedBalancedChecksum67.maxDigit chain)

theorem query_eq (s : MachineState) (head : Word) (tree : Nat)
    (value : Reference.Digest)
    (src : s.getReg .x10 = 0x90000) (bits : s.getReg .x11 = 384)
    (words : ∀ i : Fin 6, s.getMem (wordAddress 0x90000 i.val) =
      KeygenDomain.inputWord head tree value i) :
    hashInput s = Reference.packed (KeygenDomain.payload head tree value) := by
  apply Serialization.hashInput_of_list s 0x90000
    (KeygenDomain.payload head tree value)
  · exact src
  · rw [bits, KeygenDomain.payload_length]; rfl
  · intro i hi
    have bound : i < 48 := by simpa using hi
    rw [Signing.getByte_word s 0x90000 i (by decide) (by omega),
      words ⟨i/8, by omega⟩]
    exact KeygenDomain.payload_byte head tree value ⟨i, bound⟩

private def stored (s : MachineState) : MachineState :=
  execInstrBr s (.SB .x10 .x21 4)

theorem stored_header (s : MachineState) (step : Nat)
    (src : s.getReg .x10 = 0x90000)
    (stepReg : s.getReg .x21 = BitVec.ofNat 64 step) :
    (stored s).getMem 0x90000 =
      replaceByte (s.getMem 0x90000) 4 (BitVec.ofNat 8 step) := by
  simp [stored, execInstrBr, MachineState.setByte, src, stepReg,
    signExtend12, alignToDword, byteOffset]

theorem stored_mem_other (s : MachineState) (a : Word)
    (src : s.getReg .x10 = 0x90000) (other : a ≠ 0x90000) :
    (stored s).getMem a = s.getMem a := by
  simp [stored, execInstrBr, MachineState.setByte, src, signExtend12,
    alignToDword, byteOffset, Expansion.mem_setMem]
  intro same
  exact False.elim (other same)

theorem stored_regs (s : MachineState) (r : Reg) :
    (stored s).getReg r = s.getReg r := by
  simp [stored, execInstrBr, MachineState.setByte]

theorem stored_query (hash : Hash) (s : MachineState)
    (base leaf : Nat) (chain : Chain) (step : Nat)
    (value : Reference.Digest) (baseBound : base < 256)
    (stepBound : step < 256)
    (data : LoopData s base leaf chain step value) :
    hash (hashInput (stored s)) =
      Reference.query hash 2 base leaf 0 chain.val step (bytes value) := by
  obtain ⟨old, oldBound, oldHeader⟩ := data.headerCarry
  have header : (stored s).getMem 0x90000 =
      KeygenDomain.header 2 base 0 chain.val step := by
    rw [stored_header s step data.fields.src data.fields.stepReg,
      oldHeader]
    exact header_step_replace base chain.val old step baseBound
      (by have := chain.isLt; omega) (by omega) stepBound
  have words : ∀ i : Fin 6,
      (stored s).getMem (wordAddress 0x90000 i.val) =
        KeygenDomain.inputWord
          (KeygenDomain.header 2 base 0 chain.val step) leaf value i := by
    intro i
    fin_cases i <;>
      simp only [wordAddress, KeygenDomain.inputWord] <;>
      norm_num
    · exact header
    · rw [stored_mem_other s _ data.fields.src (by decide)]
      exact data.indexEq 0
    · rw [stored_mem_other s _ data.fields.src (by decide)]
      exact data.indexEq 1
    · rw [stored_mem_other s _ data.fields.src (by decide)]
      exact data.indexEq 2
    · rw [stored_mem_other s _ data.fields.src (by decide)]
      exact data.valueEq 0
    · rw [stored_mem_other s _ data.fields.src (by decide)]
      exact data.valueEq 1
  rw [query_eq (stored s) _ leaf value
    ((stored_regs s .x10).trans data.fields.src)
    ((stored_regs s .x11).trans data.fields.len) words]
  rfl

theorem hash_word (s : MachineState) (answer : BitVec 256)
    (dst : s.getReg .x12 = 0x90020) (i : Fin 2) :
    (writeHash s answer).getMem (wordAddress 0x90020 i.val) =
      answer.extractLsb' (64*i.val) 64 := by
  fin_cases i <;> simp [writeHash, dst, wordAddress, MachineState.writeWords]

theorem hash_frame (s : MachineState) (answer : BitVec 256)
    (dst : s.getReg .x12 = 0x90020) (a : Word)
    (outside : ∀ i : Fin 4, a ≠ wordAddress 0x90020 i.val) :
    (writeHash s answer).getMem a = s.getMem a := by
  have h0 : a ≠ 0x90020 := outside 0
  have h1 : a ≠ 0x90028 := outside 1
  have h2 : a ≠ 0x90030 := outside 2
  have h3 : a ≠ 0x90038 := outside 3
  simp only [writeHash, MachineState.getMem_setPC, dst,
    MachineState.writeWords, Expansion.mem_setMem]
  change (if a = 0x90038 then _ else if a = 0x90030 then _ else
    if a = 0x90028 then _ else if a = 0x90020 then _ else s.getMem a) =
      s.getMem a
  rw [if_neg h3, if_neg h2, if_neg h1, if_neg h0]

theorem tick_mem (hash : Hash) (s : MachineState) (a : Word) :
    (tickState hash s).getMem a =
      (writeHash (stored s) (hash (hashInput (stored s)))).getMem a := by
  simp [tickState, stored, execInstrBr]

def OutsideTick (a : Word) : Prop :=
  a ≠ 0x90000 ∧ (∀ i : Fin 4, a ≠ wordAddress 0x90020 i.val)

theorem tick_frame (hash : Hash) (s : MachineState) (a : Word)
    (src : s.getReg .x10 = 0x90000)
    (dst : s.getReg .x12 = 0x90020)
    (outside : OutsideTick a) :
    (tickState hash s).getMem a = s.getMem a := by
  rw [tick_mem, hash_frame (stored s) _
    ((stored_regs s .x12).trans dst) a outside.2]
  exact stored_mem_other s a src outside.1

theorem tick_data (hash : Hash) (s : MachineState)
    (base leaf : Nat) (chain : Chain) (step : Nat)
    (value : Reference.Digest)
    (small : step < GroupedBalancedChecksum67.maxDigit chain)
    (baseBound : base < 256)
    (data : LoopData s base leaf chain step value) :
    LoopData (tickState hash s) base leaf chain (step + 1)
      (GroupedBalancedUpperTree67.chainHash hash base leaf chain step value) := by
  have stepBound : step < 256 := by
    have h := max_digit_le_ten chain
    omega
  have source : (stored s).getReg .x12 = 0x90020 :=
    (stored_regs s .x12).trans data.fields.dst
  have query := stored_query hash s base leaf chain step value
    baseBound stepBound data
  constructor
  · obtain ⟨old, oldBound, oldHeader⟩ := data.headerCarry
    refine ⟨step, by have h := max_digit_le_ten chain; omega, ?_⟩
    rw [tick_mem, hash_frame (stored s) _ source 0x90000
      (by intro i; fin_cases i <;> decide),
      stored_header s step data.fields.src data.fields.stepReg,
      oldHeader]
    exact header_step_replace base chain.val old step baseBound
      (by have := chain.isLt; omega) (by omega) stepBound
  · intro i
    rw [tick_mem, hash_frame (stored s) _ source _
      (by intro j; fin_cases i <;> fin_cases j <;> decide),
      stored_mem_other s _ data.fields.src (by fin_cases i <;> decide)]
    exact data.indexEq i
  · intro i
    rw [tick_mem, hash_word (stored s) _ source i, query]
    let result := Reference.query hash 2 base leaf 0 chain.val step (bytes value)
    change result.extractLsb' (64*i.val) 64 =
      (result.extractLsb' 0 128).extractLsb' (64*i.val) 64
    fin_cases i <;> ext j hj <;> simp (disch := omega)
  · exact tick_fields hash s step
      (GroupedBalancedChecksum67.maxDigit chain) data.fields

theorem branch_data (s : MachineState) (base leaf : Nat)
    (chain : Chain) (step : Nat) (value : Reference.Digest)
    (data : LoopData s base leaf chain step value) :
    LoopData (branchState s) base leaf chain step value := by
  constructor
  · obtain ⟨old, oldBound, oldHeader⟩ := data.headerCarry
    refine ⟨old, oldBound, ?_⟩
    simpa [branchState, execInstrBr] using oldHeader
  · intro i
    simpa [branchState, execInstrBr] using data.indexEq i
  · intro i
    simpa [branchState, execInstrBr] using data.valueEq i
  · exact branch_fields s step
      (GroupedBalancedChecksum67.maxDigit chain) data.fields

theorem hash_loop_data (hash : Hash) (s : MachineState)
    (base leaf : Nat) (chain : Chain) (step remaining : Nat)
    (value : Reference.Digest)
    (pc : s.pc = 0x1630)
    (length : step + remaining = GroupedBalancedChecksum67.maxDigit chain)
    (positive : 0 < remaining) (baseBound : base < 256)
    (data : LoopData s base leaf chain step value) :
    ∃ final,
      Trace hash image s (4 * remaining) (11 * remaining)
        remaining remaining final ∧
      final.pc = 0x1640 ∧
      LoopData final base leaf chain (GroupedBalancedChecksum67.maxDigit chain)
        (walk (GroupedBalancedUpperTree67.chainHash hash base leaf chain)
          step remaining value) ∧
      (∀ a, OutsideTick a → final.getMem a = s.getMem a) ∧
      (∀ r, r ≠ .x21 → final.getReg r = s.getReg r) := by
  induction remaining generalizing s step value with
  | zero => omega
  | succ remaining ih =>
      have small : step < GroupedBalancedChecksum67.maxDigit chain := by omega
      let next := tickState hash s
      have tick := tick_block hash concrete_code s step
        (GroupedBalancedChecksum67.maxDigit chain) pc data.fields
      have nextData := tick_data hash s base leaf chain step value
        small baseBound data
      by_cases zero : remaining = 0
      · subst remaining
        have last : step + 1 = GroupedBalancedChecksum67.maxDigit chain := by
          omega
        have nextPC : next.pc = 0x1640 := by
          rw [tick_pc hash s step (GroupedBalancedChecksum67.maxDigit chain)
            pc data.fields small (max_digit_le_ten chain)]
          simp [last]
        refine ⟨next, ?_, nextPC, ?_, ?_, ?_⟩
        · simpa using tick
        · simpa only [last, walk] using nextData
        · intro a outside
          exact tick_frame hash s a data.fields.src data.fields.dst outside
        · intro r other
          exact tick_regs hash s r other
      · have notLast : step + 1 ≠ GroupedBalancedChecksum67.maxDigit chain :=
          by omega
        have nextPC : next.pc = 0x1630 := by
          rw [tick_pc hash s step (GroupedBalancedChecksum67.maxDigit chain)
            pc data.fields small (max_digit_le_ten chain)]
          simp [notLast]
        obtain ⟨final, tail, finalPC, finalData, finalFrame, finalRegs⟩ :=
          ih next (step + 1)
            (GroupedBalancedUpperTree67.chainHash hash base leaf chain step value)
            nextPC (by omega) (by omega) nextData
        refine ⟨final, ?_, finalPC, ?_, ?_, ?_⟩
        · convert tick.trans tail using 1 <;> omega
        · simpa only [walk] using finalData
        · intro a outside
          exact (finalFrame a outside).trans
            (tick_frame hash s a data.fields.src data.fields.dst outside)
        · intro r other
          exact (finalRegs r other).trans (tick_regs hash s r other)

/-- Full functional refinement and exact local resource cost for the Fast2
suffix loop, conditional only on the six query words and the selected digit. -/
theorem run_suffix_data (hash : Hash) (s : MachineState)
    (base leaf : Nat) (chain : Chain) (step : Nat)
    (value : Reference.Digest)
    (pc : s.pc = 0x162c)
    (stepBound : step ≤ GroupedBalancedChecksum67.maxDigit chain)
    (baseBound : base < 256)
    (data : LoopData s base leaf chain step value) :
    ∃ final,
      Trace hash image s
        (4 * (GroupedBalancedChecksum67.maxDigit chain - step) + 1)
        (11 * (GroupedBalancedChecksum67.maxDigit chain - step) + 1)
        (GroupedBalancedChecksum67.maxDigit chain - step)
        (GroupedBalancedChecksum67.maxDigit chain - step) final ∧
      final.pc = 0x1640 ∧
      LoopData final base leaf chain (GroupedBalancedChecksum67.maxDigit chain)
        (walk (GroupedBalancedUpperTree67.chainHash hash base leaf chain)
          step (GroupedBalancedChecksum67.maxDigit chain - step) value) ∧
      (∀ a, OutsideTick a → final.getMem a = s.getMem a) ∧
      (∀ r, r ≠ .x21 → final.getReg r = s.getReg r) := by
  have pre := branch_block concrete_code s pc
  let ready := branchState s
  have readyData := branch_data s base leaf chain step value data
  by_cases zero : GroupedBalancedChecksum67.maxDigit chain - step = 0
  · have last : step = GroupedBalancedChecksum67.maxDigit chain := by omega
    have readyPC : ready.pc = 0x1640 := by
      rw [branch_pc s step (GroupedBalancedChecksum67.maxDigit chain) pc
        data.fields stepBound (max_digit_le_ten chain)]
      simp [last]
    refine ⟨ready, ?_, readyPC, ?_, ?_, ?_⟩
    · simpa [zero] using pre.trace
    · simpa [zero, last, walk] using readyData
    · intro a _
      simp [ready, branchState, execInstrBr]
    · intro r _
      exact branch_regs s r
  · have notLast : step ≠ GroupedBalancedChecksum67.maxDigit chain := by
      omega
    have readyPC : ready.pc = 0x1630 := by
      rw [branch_pc s step (GroupedBalancedChecksum67.maxDigit chain) pc
        data.fields stepBound (max_digit_le_ten chain)]
      simp [notLast]
    obtain ⟨final, tail, finalPC, finalData, finalFrame, finalRegs⟩ :=
      hash_loop_data hash ready base leaf chain step
        (GroupedBalancedChecksum67.maxDigit chain - step) value readyPC
        (by omega) (by omega) baseBound readyData
    refine ⟨final, ?_, finalPC, finalData, ?_, ?_⟩
    · convert pre.trace.trans tail using 1 <;> omega
    · intro a outside
      rw [finalFrame a outside]
      simp [ready, branchState, execInstrBr]
    · intro r other
      exact (finalRegs r other).trans (branch_regs s r)

theorem run_chain_suffix_data (hash : Hash) (s : MachineState)
    (base leaf : Nat) (chain : Chain) (message value : Reference.Digest)
    (pc : s.pc = 0x162c) (baseBound : base < 256)
    (data : LoopData s base leaf chain
      (GroupedBalancedChecksum67.digit message chain).val value) :
    ∃ final,
      Trace hash image s
        (4 * (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) + 1)
        (11 * (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) + 1)
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
      (∀ r, r ≠ .x21 → final.getReg r = s.getReg r) :=
  run_suffix_data hash s base leaf chain
    (GroupedBalancedChecksum67.digit message chain).val value pc
    (GroupedBalancedChecksum67.digit_le_max message chain) baseBound data

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixData67
