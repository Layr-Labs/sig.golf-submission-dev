import SigGolfCandidate.Hypertree.GroupedBalancedByteFastIteration67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastWotsFrame67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainCarry67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainReady67. -/
section
/-! The header and tree index survive a WOTS endpoint copy, allowing the
next chain to reuse the preceding chain's hash header. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainCarry67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.Signing
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixData67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastPrologue67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastEndpoint67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastLimit67
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

private theorem high_ne_low (a d : Word)
    (high : 0x90000 ≤ a.toNat) (low : d.toNat < 0x80500) : a ≠ d := by
  intro same
  have h := congrArg BitVec.toNat same
  omega

theorem copy_high_mem (s : MachineState) (a : Word)
    (high : 0x90000 ≤ a.toNat)
    (low0 : (s.getReg .x24).toNat < 0x80500)
    (low8 : (s.getReg .x24 + 8).toNat < 0x80500) :
    (copyState s).getMem a = s.getMem a := by
  rw [copy_mem]
  simp only [if_neg (high_ne_low a _ high low8),
    if_neg (high_ne_low a _ high low0)]

theorem copy_header (s : MachineState)
    (low0 : (s.getReg .x24).toNat < 0x80500)
    (low8 : (s.getReg .x24 + 8).toNat < 0x80500) :
    (copyState s).getMem 0x90000 = s.getMem 0x90000 := by
  exact copy_high_mem s 0x90000 (by decide) low0 low8

theorem copy_index (s : MachineState)
    (low0 : (s.getReg .x24).toNat < 0x80500)
    (low8 : (s.getReg .x24 + 8).toNat < 0x80500) :
    ∀ i : Fin 3,
      (copyState s).getMem (wordAddress 0x90008 i.val) =
        s.getMem (wordAddress 0x90008 i.val) := by
  intro i
  apply copy_high_mem s _ _ low0 low8
  fin_cases i <;> decide

theorem copy_header_index (s : MachineState) (base leaf : Nat)
    (chain : GroupedBalancedChecksum67.Chain) (step : Nat)
    (value : Reference.Digest)
    (low0 : (s.getReg .x24).toNat < 0x80500)
    (low8 : (s.getReg .x24 + 8).toNat < 0x80500)
    (data : LoopData s base leaf chain step value) :
    (∃ old, old < 11 ∧
      (copyState s).getMem 0x90000 =
        KeygenDomain.header 2 base 0 chain.val old) ∧
    (∀ i : Fin 3,
      (copyState s).getMem (wordAddress 0x90008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64) := by
  constructor
  · obtain ⟨old,oldBound,header⟩ := data.headerCarry
    exact ⟨old,oldBound,(copy_header s low0 low8).trans header⟩
  · intro i
    exact (copy_index s low0 low8 i).trans (data.indexEq i)

theorem prologue_witness_ptr (s : MachineState) :
    (prologueState s).getReg .x22 = s.getReg .x22 + 16 := by
  simp [prologueState,prefixState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

/-- The concrete WOTS body and endpoint copy retain the complete query
context needed by the next chain. -/
theorem run_chain_copy_carry (hash : Hash) (s : MachineState)
    (base leaf : Nat) (chain : GroupedBalancedChecksum67.Chain)
    (message value : Reference.Digest)
    (pc : s.pc = 0x1608)
    (valid0 : accessValid (s.getReg .x22) 8 = true)
    (valid8 : accessValid (s.getReg .x22 + 8) 8 = true)
    (digitValid : accessValid (s.getReg .x25) 1 = true)
    (dst0 : accessValid (s.getReg .x24) 8 = true)
    (dst8 : accessValid (s.getReg .x24 + 8) 8 = true)
    (low0 : (s.getReg .x24).toNat < 0x80500)
    (low8 : (s.getReg .x24 + 8).toNat < 0x80500)
    (baseBound : base < 256)
    (data : EntryData s base leaf chain message value) :
    ∃ copied,
      Trace hash image s
        (4 * (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) + 15)
        (11 * (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) + 15)
        (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val)
        (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) copied ∧
      copied.pc = 0x1654 ∧
      (∃ old, old < 11 ∧ copied.getMem 0x90000 =
        KeygenDomain.header 2 base 0 chain.val old) ∧
      (∀ i : Fin 3, copied.getMem (wordAddress 0x90008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64) ∧
      (∀ i : Fin 2,
        copied.getMem (s.getReg .x24 + BitVec.ofNat 64 (8*i.val)) =
          (walk (GroupedBalancedUpperTree67.chainHash hash base leaf chain)
            (GroupedBalancedChecksum67.digit message chain).val
            (GroupedBalancedChecksum67.maxDigit chain -
              (GroupedBalancedChecksum67.digit message chain).val) value).extractLsb'
              (64*i.val) 64) ∧
      copied.getReg .x22 = s.getReg .x22 + 16 ∧
      copied.getReg .x23 = s.getReg .x23 ∧
      copied.getReg .x24 = s.getReg .x24 + 16 ∧
      copied.getReg .x25 = s.getReg .x25 + 1 ∧
      copied.getReg .x20 = s.getReg .x20 ∧
      copied.getReg .x10 = 0x90000 ∧
      copied.getReg .x11 = 384 ∧
      copied.getReg .x12 = 0x90020 ∧
      copied.getReg .x5 = 1 ∧
      (∀ a, OutsideTick a → a ≠ s.getReg .x24 →
        a ≠ s.getReg .x24 + 8 → copied.getMem a = s.getMem a) := by
  have pre := prologue_block s pc valid0 valid8 digitValid data.src data.dst
  have readyPC : (prologueState s).pc = 0x162c := by
    rw [prologue_pc,pc]
    decide
  have readyData := prologue_loop_data s base leaf chain message value
    baseBound data
  obtain ⟨wots, tail, wotsPC, wotsData, tailFrame, tailRegs⟩ :=
    run_chain_suffix_data hash (prologueState s) base leaf chain
      message value readyPC baseBound readyData
  have first : Trace hash image s
      (4 * (GroupedBalancedChecksum67.maxDigit chain -
        (GroupedBalancedChecksum67.digit message chain).val) + 10)
      (11 * (GroupedBalancedChecksum67.maxDigit chain -
        (GroupedBalancedChecksum67.digit message chain).val) + 10)
      (GroupedBalancedChecksum67.maxDigit chain -
        (GroupedBalancedChecksum67.digit message chain).val)
      (GroupedBalancedChecksum67.maxDigit chain -
        (GroupedBalancedChecksum67.digit message chain).val) wots := by
    convert pre.trace.trans tail using 1 <;> omega
  have wotsFrame : ∀ a, OutsideTick a → wots.getMem a = s.getMem a := by
    intro a outside
    rw [tailFrame a outside]
    rw [prologue_mem s a data.src data.dst data.digitOutside0
      data.digitOutside1 data.digitOutside2]
    have h0 : a ≠ 0x90000 := outside.1
    have h1 : a ≠ 0x90028 := by
      simpa [wordAddress] using outside.2 (1 : Fin 4)
    have h2 : a ≠ 0x90020 := by
      simpa [wordAddress] using outside.2 (0 : Fin 4)
    simp only [if_neg h0,if_neg h1,if_neg h2]
  have wotsChain : wots.getReg .x23 = s.getReg .x23 :=
    (tailRegs .x23 (by decide)).trans
      (prologue_reg_stable s .x23 (by decide) (by decide)
        (by decide) (by decide) (by decide))
  have wotsPtr : wots.getReg .x24 = s.getReg .x24 :=
    (tailRegs .x24 (by decide)).trans
      (prologue_reg_stable s .x24 (by decide) (by decide)
        (by decide) (by decide) (by decide))
  have wotsDigitPtr : wots.getReg .x25 = s.getReg .x25 + 1 :=
    (tailRegs .x25 (by decide)).trans (prologue_digit_ptr s)
  have wotsLimit : wots.getReg .x20 = s.getReg .x20 :=
    (tailRegs .x20 (by decide)).trans
      (prologue_reg_stable s .x20 (by decide) (by decide)
        (by decide) (by decide) (by decide))
  have wotsWitnessPtr : wots.getReg .x22 = s.getReg .x22 + 16 :=
    (tailRegs .x22 (by decide)).trans (prologue_witness_ptr s)
  have dst0' : accessValid (wots.getReg .x24) 8 = true := by
    rw [wotsPtr]; exact dst0
  have dst8' : accessValid (wots.getReg .x24 + 8) 8 = true := by
    rw [wotsPtr]; exact dst8
  have second := copy_block wots wotsPC wotsData.fields.dst dst0' dst8'
  have low0' : (wots.getReg .x24).toNat < 0x80500 := by
    rw [wotsPtr]; exact low0
  have low8' : (wots.getReg .x24 + 8).toNat < 0x80500 := by
    rw [wotsPtr]; exact low8
  obtain ⟨header,index⟩ := copy_header_index wots base leaf chain _ _
    low0' low8' wotsData
  let copied := copyState wots
  have copiedValue := copy_value wots
    (walk (GroupedBalancedUpperTree67.chainHash hash base leaf chain)
      (GroupedBalancedChecksum67.digit message chain).val
      (GroupedBalancedChecksum67.maxDigit chain -
        (GroupedBalancedChecksum67.digit message chain).val) value)
    wotsData.fields.dst wotsData.valueEq
  refine ⟨copied, ?_, copy_pc wots wotsPC, header, index,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert first.trans second.trace using 1 <;> omega
  · intro i
    simpa only [copied,wotsPtr] using copiedValue i
  · exact (copy_reg_stable wots .x22 (by decide) (by decide)
      (by decide)).trans wotsWitnessPtr
  · exact (copy_reg_stable wots .x23 (by decide) (by decide)
      (by decide)).trans wotsChain
  · rw [copy_ptr,wotsPtr]
  · exact (copy_reg_stable wots .x25 (by decide) (by decide)
      (by decide)).trans wotsDigitPtr
  · exact (copy_reg_stable wots .x20 (by decide) (by decide)
      (by decide)).trans wotsLimit
  · exact (copy_reg_stable wots .x10 (by decide) (by decide)
      (by decide)).trans wotsData.fields.src
  · exact (copy_reg_stable wots .x11 (by decide) (by decide)
      (by decide)).trans wotsData.fields.len
  · exact (copy_reg_stable wots .x12 (by decide) (by decide)
      (by decide)).trans wotsData.fields.dst
  · exact (copy_reg_stable wots .x5 (by decide) (by decide)
      (by decide)).trans wotsData.fields.service
  · intro a outside notLow notHigh
    rw [copy_mem]
    simp only [wotsPtr, if_neg notHigh, if_neg notLow]
    exact wotsFrame a outside

structure CarriedContext (s : MachineState) (base leaf : Nat)
    (previous : GroupedBalancedChecksum67.Chain) : Prop where
  header : ∃ old, old < 11 ∧ s.getMem 0x90000 =
    KeygenDomain.header 2 base 0 previous.val old
  index : ∀ i : Fin 3, s.getMem (wordAddress 0x90008 i.val) =
    (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64
  src : s.getReg .x10 = 0x90000
  len : s.getReg .x11 = 384
  dst : s.getReg .x12 = 0x90020
  service : s.getReg .x5 = 1

theorem context_of_copied (s : MachineState) (base leaf : Nat)
    (previous : GroupedBalancedChecksum67.Chain)
    (header : ∃ old, old < 11 ∧ s.getMem 0x90000 =
      KeygenDomain.header 2 base 0 previous.val old)
    (index : ∀ i : Fin 3, s.getMem (wordAddress 0x90008 i.val) =
      (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (src : s.getReg .x10 = 0x90000)
    (len : s.getReg .x11 = 384)
    (dst : s.getReg .x12 = 0x90020)
    (service : s.getReg .x5 = 1) :
    CarriedContext s base leaf previous :=
  ⟨header,index,src,len,dst,service⟩

theorem context_transfer (s t : MachineState) (base leaf : Nat)
    (previous : GroupedBalancedChecksum67.Chain)
    (context : CarriedContext s base leaf previous)
    (mem : ∀ a : Word, t.getMem a = s.getMem a)
    (reg : ∀ r ∈ ([.x10,.x11,.x12,.x5] : List Reg),
      t.getReg r = s.getReg r) :
    CarriedContext t base leaf previous := by
  constructor
  · obtain ⟨old,oldBound,header⟩ := context.header
    exact ⟨old,oldBound,(mem _).trans header⟩
  · intro i
    exact (mem _).trans (context.index i)
  · exact (reg .x10 (by simp)).trans context.src
  · exact (reg .x11 (by simp)).trans context.len
  · exact (reg .x12 (by simp)).trans context.dst
  · exact (reg .x5 (by simp)).trans context.service

theorem advance_context (s : MachineState) (base leaf : Nat)
    (previous : GroupedBalancedChecksum67.Chain)
    (context : CarriedContext s base leaf previous) :
    CarriedContext (advanceState s) base leaf previous := by
  apply context_transfer s (advanceState s) base leaf previous context
    (advance_mem s)
  intro r hr
  exact advance_reg_stable s r (by simp at hr; rcases hr with h|h|h|h <;> simp [h])
    (by simp at hr; rcases hr with h|h|h|h <;> simp [h])

theorem next65_context (s : MachineState) (base leaf : Nat)
    (previous : GroupedBalancedChecksum67.Chain)
    (context : CarriedContext s base leaf previous) :
    CarriedContext (next65State s) base leaf previous := by
  apply context_transfer s (next65State s) base leaf previous context
    (next65_mem s)
  intro r hr
  exact next65_reg_stable s r
    (by simp at hr; rcases hr with h|h|h|h <;> simp [h])
    (by simp at hr; rcases hr with h|h|h|h <;> simp [h])
    (by simp at hr; rcases hr with h|h|h|h <;> simp [h])
    (by simp at hr; rcases hr with h|h|h|h <;> simp [h])

theorem next66_context (s : MachineState) (base leaf : Nat)
    (previous : GroupedBalancedChecksum67.Chain)
    (context : CarriedContext s base leaf previous) :
    CarriedContext (next66State s) base leaf previous := by
  apply context_transfer s (next66State s) base leaf previous context
    (next66_mem s)
  intro r hr
  exact next66_reg_stable s r
    (by simp at hr; rcases hr with h|h|h|h <;> simp [h])
    (by simp at hr; rcases hr with h|h|h|h <;> simp [h])
    (by simp at hr; rcases hr with h|h|h|h <;> simp [h])
    (by simp at hr; rcases hr with h|h|h|h <;> simp [h])

theorem nextDone_context (s : MachineState) (base leaf : Nat)
    (previous : GroupedBalancedChecksum67.Chain)
    (context : CarriedContext s base leaf previous) :
    CarriedContext (nextDoneState s) base leaf previous := by
  apply context_transfer s (nextDoneState s) base leaf previous context
    (next_done_mem s)
  intro r hr
  exact next_done_reg_stable s r
    (by simp at hr; rcases hr with h|h|h|h <;> simp [h])
    (by simp at hr; rcases hr with h|h|h|h <;> simp [h])
    (by simp at hr; rcases hr with h|h|h|h <;> simp [h])

#print axioms copy_header_index
#print axioms run_chain_copy_carry

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainCarry67

end

/-! The state carried from one concrete WOTS chain entry to the next. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainReady67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.Signing
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixData67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastPrologue67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastEndpoint67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastLimit67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainCarry67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastWotsFrame67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteContract67
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

def witnessAddress (start : Nat) (chain : Fin 67) (half : Fin 2) : Word :=
  BitVec.ofNat 64 (start + 16*chain.val + 8*half.val)

def WitnessWords (s : MachineState) (start : Nat)
    (values : Fin 67 → Reference.Digest) : Prop :=
  ∀ chain : Fin 67, ∀ half : Fin 2,
    s.getMem (witnessAddress start chain half) =
      (values chain).extractLsb' (64*half.val) 64

def SafeWitnesses (start : Nat) : Prop :=
  ∀ chain : Fin 67, ∀ half : Fin 2,
    accessValid (witnessAddress start chain half) 8 = true ∧
      (witnessAddress start chain half).toNat < 0x80020

structure Ready (s : MachineState) (base leaf start : Nat)
    (chain : Fin 67) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest) : Prop where
  pc : s.pc = 0x1608
  context : ∃ previous : Fin 67,
    CarriedContext s base leaf previous
  witnessPtr : s.getReg .x22 =
    BitVec.ofNat 64 (start + 16*chain.val)
  chainReg : s.getReg .x23 = BitVec.ofNat 64 chain.val
  outputPtr : s.getReg .x24 =
    BitVec.ofNat 64 (0x80020 + 16*chain.val)
  digitPtr : s.getReg .x25 =
    BitVec.ofNat 64 (0x80600 + chain.val)
  limitReg : s.getReg .x20 =
    BitVec.ofNat 64 (GroupedBalancedChecksum67.maxDigit chain)
  witnesses : WitnessWords s start values
  digits : Digits s message
  tables : Tables s

theorem ready_entry_data (s : MachineState) (base leaf start : Nat)
    (chain : Fin 67) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (ready : Ready s base leaf start chain message values) :
    EntryData s base leaf chain message (values chain) := by
  obtain ⟨previous,context⟩ := ready.context
  have safe := decoder_ptr_safe chain.val chain.isLt
  constructor
  · obtain ⟨old,oldBound,header⟩ := context.header
    exact ⟨previous.val,old,previous.isLt,oldBound,header⟩
  · exact context.index
  · intro half
    have addr : s.getReg .x22 + BitVec.ofNat 64 (8*half.val) =
        witnessAddress start chain half := by
      rw [ready.witnessPtr]
      simp [witnessAddress,BitVec.ofNat_add]
    rw [addr]
    exact ready.witnesses chain half
  · rw [ready.digitPtr]
    exact ready.digits chain
  · exact context.src
  · exact context.len
  · exact context.dst
  · exact context.service
  · exact ready.chainReg
  · exact ready.limitReg
  · rw [ready.digitPtr]
    exact safe.2.1
  · rw [ready.digitPtr]
    exact safe.2.2.1
  · rw [ready.digitPtr]
    exact safe.2.2.2

theorem ready_valid (s : MachineState) (base leaf start : Nat)
    (chain : Fin 67) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start)
    (ready : Ready s base leaf start chain message values) :
    accessValid (s.getReg .x22) 8 = true ∧
      accessValid (s.getReg .x22 + 8) 8 = true ∧
      accessValid (s.getReg .x25) 1 = true := by
  have h0 := (safe chain 0).1
  have h1 := (safe chain 1).1
  have digit := (decoder_ptr_safe chain.val chain.isLt).1
  constructor
  · simpa [ready.witnessPtr,witnessAddress] using h0
  constructor
  · have addr : s.getReg .x22 + 8 = witnessAddress start chain 1 := by
      rw [ready.witnessPtr]
      simp [witnessAddress,BitVec.ofNat_add]
    rw [addr]
    exact h1
  · rw [ready.digitPtr]
    exact digit

theorem output_valid (s : MachineState) (base leaf start : Nat)
    (chain : Fin 67) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (ready : Ready s base leaf start chain message values) :
    accessValid (s.getReg .x24) 8 = true ∧
      accessValid (s.getReg .x24 + 8) 8 = true := by
  rw [ready.outputPtr]
  constructor
  · simp only [accessValid,rangeValid,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80020+16*chain.val < 2^64),
      Bool.and_eq_true,decide_eq_true_eq]
    constructor <;> (try unfold MEMORY_BYTES) <;> omega
  · change accessValid
      (BitVec.ofNat 64 (0x80020+16*chain.val) + BitVec.ofNat 64 8) 8 = true
    rw [← BitVec.ofNat_add]
    simp only [accessValid,rangeValid,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80020+16*chain.val+8 < 2^64),
      Bool.and_eq_true,decide_eq_true_eq]
    constructor <;> (try unfold MEMORY_BYTES) <;> omega

structure AfterCopy (s : MachineState) (base leaf start : Nat)
    (chain : Fin 67) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest) : Prop where
  pc : s.pc = 0x1654
  context : CarriedContext s base leaf chain
  witnessPtr : s.getReg .x22 =
    BitVec.ofNat 64 (start + 16*(chain.val+1))
  chainReg : s.getReg .x23 = BitVec.ofNat 64 chain.val
  outputPtr : s.getReg .x24 =
    BitVec.ofNat 64 (0x80020 + 16*(chain.val+1))
  digitPtr : s.getReg .x25 =
    BitVec.ofNat 64 (0x80600 + chain.val+1)
  limitReg : s.getReg .x20 =
    BitVec.ofNat 64 (GroupedBalancedChecksum67.maxDigit chain)
  witnesses : WitnessWords s start values
  digits : Digits s message
  tables : Tables s

theorem run_to_after_copy (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (chain : Fin 67)
    (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (ready : Ready s base leaf start chain message values) :
    ∃ copied,
      Trace hash image s
        (4 * (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) + 15)
        (11 * (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) + 15)
        (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val)
        (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) copied ∧
      AfterCopy copied base leaf start chain message values ∧
      (∀ half : Fin 2,
        copied.getMem
          (BitVec.ofNat 64 (0x80020+16*chain.val+8*half.val)) =
        (walk (GroupedBalancedUpperTree67.chainHash hash base leaf chain)
          (GroupedBalancedChecksum67.digit message chain).val
          (GroupedBalancedChecksum67.maxDigit chain -
            (GroupedBalancedChecksum67.digit message chain).val)
          (values chain)).extractLsb' (64*half.val) 64) ∧
      (∀ a, OutsideTick a → a ≠ s.getReg .x24 →
        a ≠ s.getReg .x24 + 8 → copied.getMem a = s.getMem a) := by
  obtain ⟨source0,source8,digitValid⟩ :=
    ready_valid s base leaf start chain message values safe ready
  obtain ⟨dest0,dest8⟩ :=
    output_valid s base leaf start chain message values ready
  obtain ⟨destLow0,destLow8⟩ := chain_dest_low s chain ready.outputPtr
  obtain ⟨destGe0,destGe8⟩ := chain_dest_ge s chain ready.outputPtr
  obtain ⟨copied,trace,copiedPC,header,index,endpoint,
    witnessPtr,chainReg,outputPtr,digitPtr,limitReg,
    src,len,dst,service,frame⟩ :=
    run_chain_copy_carry hash s base leaf chain message (values chain)
      ready.pc source0 source8 digitValid dest0 dest8
      destLow0 destLow8 baseBound
      (ready_entry_data s base leaf start chain message values ready)
  obtain ⟨tables,digits⟩ := input_frame_of_endpoint s copied message
    destLow0 destLow8 frame ready.tables ready.digits
  have lowFrame := low_frame_of_endpoint s copied destGe0 destGe8 frame
  have witnesses : WitnessWords copied start values := by
    intro c half
    rw [lowFrame _ (safe c half).2]
    exact ready.witnesses c half
  have context : CarriedContext copied base leaf chain :=
    context_of_copied copied base leaf chain header index src len dst service
  have witnessPtr' : copied.getReg .x22 =
      BitVec.ofNat 64 (start+16*(chain.val+1)) := by
    rw [witnessPtr,ready.witnessPtr]
    change BitVec.ofNat 64 (start+16*chain.val) + BitVec.ofNat 64 16 = _
    rw [← BitVec.ofNat_add]
    congr 1
  have outputPtr' : copied.getReg .x24 =
      BitVec.ofNat 64 (0x80020+16*(chain.val+1)) := by
    rw [outputPtr,ready.outputPtr]
    change BitVec.ofNat 64 (0x80020+16*chain.val) + BitVec.ofNat 64 16 = _
    rw [← BitVec.ofNat_add]
    congr 1
  have digitPtr' : copied.getReg .x25 =
      BitVec.ofNat 64 (0x80600+chain.val+1) := by
    rw [digitPtr,ready.digitPtr]
    change BitVec.ofNat 64 (0x80600+chain.val) + BitVec.ofNat 64 1 = _
    rw [← BitVec.ofNat_add]
  refine ⟨copied,trace,?_,?_,frame⟩
  · exact ⟨copiedPC,context,witnessPtr',chainReg.trans ready.chainReg,
      outputPtr',digitPtr',limitReg.trans ready.limitReg,
      witnesses,digits,tables⟩
  · intro half
    have addr : s.getReg .x24 + BitVec.ofNat 64 (8*half.val) =
        BitVec.ofNat 64 (0x80020+16*chain.val+8*half.val) := by
      rw [ready.outputPtr,← BitVec.ofNat_add]
    rw [← addr]
    exact endpoint half

theorem after_copy_short (s : MachineState) (base leaf start : Nat)
    (chain : Fin 67) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (short : chain.val < 64)
    (after : AfterCopy s base leaf start chain message values) :
    OrdinarySteps image s 3 (advanceState s) ∧
    Ready (advanceState s) base leaf start
      ⟨chain.val+1,by omega⟩ message values := by
  have block := advance_block s after.pc
  have nextPC := advance_short_pc s chain.val after.pc
    after.chainReg short
  have nextChain := advance_chain s chain.val after.chainReg
  have nextLimit : (advanceState s).getReg .x20 =
      BitVec.ofNat 64
        (GroupedBalancedChecksum67.maxDigit ⟨chain.val+1,by omega⟩) := by
    rw [advance_limit,after.limitReg]
    simp [GroupedBalancedChecksum67.maxDigit,
      show chain.val < 65 by omega,
      show chain.val+1 < 65 by omega]
  obtain ⟨tables,digits⟩ := advance_input_frame s message
    after.tables after.digits
  refine ⟨block,?_⟩
  constructor
  · exact nextPC
  · exact ⟨chain,advance_context s base leaf chain after.context⟩
  · exact (advance_reg_stable s .x22 (by decide) (by decide)).trans
      after.witnessPtr
  · exact nextChain
  · exact (advance_reg_stable s .x24 (by decide) (by decide)).trans
      after.outputPtr
  · exact (advance_reg_stable s .x25 (by decide) (by decide)).trans
      after.digitPtr
  · exact nextLimit
  · intro c half
    rw [advance_mem]
    exact after.witnesses c half
  · exact digits
  · exact tables

theorem after_copy_64 (s : MachineState) (base leaf start : Nat)
    (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (after : AfterCopy s base leaf start (64 : Fin 67) message values) :
    OrdinarySteps image s 7 (next65State s) ∧
    Ready (next65State s) base leaf start
      (65 : Fin 67) message values := by
  have chain : s.getReg .x23 = 64 := by simpa using after.chainReg
  have block := next65_block s after.pc chain
  have nextPC := next65_pc s after.pc chain
  have nextChain := next65_chain s chain
  have nextLimit := next65_limit s
  obtain ⟨tables,digits⟩ := next65_input_frame s message
    after.tables after.digits
  refine ⟨block,?_⟩
  constructor
  · exact nextPC
  · exact ⟨(64 : Fin 67),next65_context s base leaf _ after.context⟩
  · exact (next65_reg_stable s .x22 (by decide) (by decide)
      (by decide) (by decide)).trans after.witnessPtr
  · exact nextChain
  · exact (next65_reg_stable s .x24 (by decide) (by decide)
      (by decide) (by decide)).trans after.outputPtr
  · exact (next65_reg_stable s .x25 (by decide) (by decide)
      (by decide) (by decide)).trans after.digitPtr
  · exact nextLimit
  · intro c half
    rw [next65_mem]
    exact after.witnesses c half
  · exact digits
  · exact tables

theorem after_copy_65 (s : MachineState) (base leaf start : Nat)
    (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (after : AfterCopy s base leaf start (65 : Fin 67) message values) :
    OrdinarySteps image s 9 (next66State s) ∧
    Ready (next66State s) base leaf start
      (66 : Fin 67) message values := by
  have chain : s.getReg .x23 = 65 := by simpa using after.chainReg
  have block := next66_block s after.pc chain
  have nextPC := next66_pc s after.pc chain
  have nextChain := next66_chain s chain
  have nextLimit := next66_limit s
  obtain ⟨tables,digits⟩ := next66_input_frame s message
    after.tables after.digits
  refine ⟨block,?_⟩
  constructor
  · exact nextPC
  · exact ⟨(65 : Fin 67),next66_context s base leaf _ after.context⟩
  · exact (next66_reg_stable s .x22 (by decide) (by decide)
      (by decide) (by decide)).trans after.witnessPtr
  · exact nextChain
  · exact (next66_reg_stable s .x24 (by decide) (by decide)
      (by decide) (by decide)).trans after.outputPtr
  · exact (next66_reg_stable s .x25 (by decide) (by decide)
      (by decide) (by decide)).trans after.digitPtr
  · exact nextLimit
  · intro c half
    rw [next66_mem]
    exact after.witnesses c half
  · exact digits
  · exact tables

structure Done (s : MachineState) (base leaf start : Nat)
    (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest) : Prop where
  pc : s.pc = 0x1684
  context : CarriedContext s base leaf (66 : Fin 67)
  witnessPtr : s.getReg .x22 = BitVec.ofNat 64 (start+16*67)
  chainReg : s.getReg .x23 = 67
  outputPtr : s.getReg .x24 = BitVec.ofNat 64 (0x80020+16*67)
  digitPtr : s.getReg .x25 = BitVec.ofNat 64 (0x80600+67)
  limitReg : s.getReg .x20 = 10
  witnesses : WitnessWords s start values
  digits : Digits s message
  tables : Tables s

theorem after_copy_66 (s : MachineState) (base leaf start : Nat)
    (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (after : AfterCopy s base leaf start (66 : Fin 67) message values) :
    OrdinarySteps image s 8 (nextDoneState s) ∧
    Done (nextDoneState s) base leaf start message values := by
  have chain : s.getReg .x23 = 66 := by simpa using after.chainReg
  have block := next_done_block s after.pc chain
  have nextPC := next_done_pc s after.pc chain
  have nextChain := next_done_chain s chain
  have nextLimit : (nextDoneState s).getReg .x20 = 10 := by
    rw [next_done_reg_stable s .x20 (by decide) (by decide) (by decide),
      after.limitReg]
    decide
  obtain ⟨tables,digits⟩ := nextDone_input_frame s message
    after.tables after.digits
  refine ⟨block,?_⟩
  constructor
  · exact nextPC
  · exact nextDone_context s base leaf _ after.context
  · exact (next_done_reg_stable s .x22 (by decide) (by decide)
      (by decide)).trans after.witnessPtr
  · exact nextChain
  · exact (next_done_reg_stable s .x24 (by decide) (by decide)
      (by decide)).trans after.outputPtr
  · exact (next_done_reg_stable s .x25 (by decide) (by decide)
      (by decide)).trans after.digitPtr
  · exact nextLimit
  · intro c half
    rw [next_done_mem]
    exact after.witnesses c half
  · exact digits
  · exact tables

#print axioms ready_entry_data
#print axioms run_to_after_copy
#print axioms after_copy_short
#print axioms after_copy_64
#print axioms after_copy_65
#print axioms after_copy_66

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainReady67
