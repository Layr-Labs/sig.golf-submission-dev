import SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainReady67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainConcrete67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedByteFastEndpointAccum67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainEndpoints67. -/
section
/-! Previously recovered WOTS endpoints survive each later chain write. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastEndpointAccum67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.Signing
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixData67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastLimit67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainReady67
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

def endpointAddress (chain : Fin 67) (half : Fin 2) : Word :=
  BitVec.ofNat 64 (0x80020+16*chain.val+8*half.val)

def expectedEndpoint (hash : Hash) (base leaf : Nat)
    (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (chain : Fin 67) : Reference.Digest :=
  walk (GroupedBalancedUpperTree67.chainHash hash base leaf chain)
    (GroupedBalancedChecksum67.digit message chain).val
    (GroupedBalancedChecksum67.maxDigit chain -
      (GroupedBalancedChecksum67.digit message chain).val)
    (values chain)

def EndpointWords (hash : Hash) (s : MachineState) (base leaf : Nat)
    (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest) (before : Nat) : Prop :=
  ∀ chain : Fin 67, chain.val < before → ∀ half : Fin 2,
    s.getMem (endpointAddress chain half) =
      (expectedEndpoint hash base leaf message values chain).extractLsb'
        (64*half.val) 64

theorem endpoint_address_nat (chain : Fin 67) (half : Fin 2) :
    (endpointAddress chain half).toNat =
      0x80020+16*chain.val+8*half.val := by
  simp only [endpointAddress,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega :
      0x80020+16*chain.val+8*half.val < 2^64)]

private theorem outside_endpoint (chain : Fin 67) (half : Fin 2) :
    OutsideTick (endpointAddress chain half) := by
  have low : (endpointAddress chain half).toNat < 0x90000 := by
    rw [endpoint_address_nat]
    omega
  constructor
  · intro eq
    have h := congrArg BitVec.toNat eq
    have h0 : (0x90000 : Word).toNat = 0x90000 := by decide
    rw [h0] at h
    omega
  · intro i eq
    have h := congrArg BitVec.toNat eq
    simp only [wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x90020+8*i.val < 2^64)] at h
    omega

private theorem current_dest_nat (s : MachineState) (chain : Fin 67)
    (ptr : s.getReg .x24 = BitVec.ofNat 64 (0x80020+16*chain.val)) :
    (s.getReg .x24).toNat = 0x80020+16*chain.val ∧
    (s.getReg .x24 + 8).toNat = 0x80020+16*chain.val+8 := by
  constructor
  · rw [ptr]
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80020+16*chain.val < 2^64)]
  · rw [ptr]
    change (BitVec.ofNat 64 (0x80020+16*chain.val) +
      BitVec.ofNat 64 8).toNat = _
    rw [← BitVec.ofNat_add]
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80020+16*chain.val+8 < 2^64)]

theorem earlier_endpoint_frame (s copied : MachineState)
    (chain previous : Fin 67) (half : Fin 2)
    (earlier : previous.val < chain.val)
    (ptr : s.getReg .x24 =
      BitVec.ofNat 64 (0x80020+16*chain.val))
    (frame : ∀ a, OutsideTick a → a ≠ s.getReg .x24 →
      a ≠ s.getReg .x24 + 8 → copied.getMem a = s.getMem a) :
    copied.getMem (endpointAddress previous half) =
      s.getMem (endpointAddress previous half) := by
  obtain ⟨dest0,dest8⟩ := current_dest_nat s chain ptr
  have previousNat := endpoint_address_nat previous half
  apply frame _ (outside_endpoint previous half)
  · intro eq
    have h := congrArg BitVec.toNat eq
    omega
  · intro eq
    have h := congrArg BitVec.toNat eq
    omega

theorem endpoint_words_copy (hash : Hash) (s copied : MachineState)
    (base leaf : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest) (chain : Fin 67)
    (ptr : s.getReg .x24 =
      BitVec.ofNat 64 (0x80020+16*chain.val))
    (old : EndpointWords hash s base leaf message values chain.val)
    (current : ∀ half : Fin 2,
      copied.getMem (endpointAddress chain half) =
        (expectedEndpoint hash base leaf message values chain).extractLsb'
          (64*half.val) 64)
    (frame : ∀ a, OutsideTick a → a ≠ s.getReg .x24 →
      a ≠ s.getReg .x24 + 8 → copied.getMem a = s.getMem a) :
    EndpointWords hash copied base leaf message values (chain.val+1) := by
  intro previous previousBound half
  by_cases equal : previous.val = chain.val
  · have same : previous = chain := Fin.ext equal
    subst previous
    exact current half
  · have earlier : previous.val < chain.val := by omega
    rw [earlier_endpoint_frame s copied chain previous half earlier ptr frame]
    exact old previous earlier half

theorem endpoint_words_mem (hash : Hash) (s t : MachineState)
    (base leaf : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest) (before : Nat)
    (old : EndpointWords hash s base leaf message values before)
    (mem : ∀ a, t.getMem a = s.getMem a) :
    EndpointWords hash t base leaf message values before := by
  intro chain earlier half
  rw [mem]
  exact old chain earlier half

theorem initial_endpoints (hash : Hash) (s : MachineState)
    (base leaf : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest) :
    EndpointWords hash s base leaf message values 0 := by
  intro chain earlier
  omega

#print axioms endpoint_words_copy

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastEndpointAccum67

end

/-! The complete WOTS trace with all 67 recovered endpoint words retained. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainEndpoints67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastLimit67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainReady67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainConcrete67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastEndpointAccum67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainFold67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def StrongReady (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (chain : Fin 67)
    (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest) : Prop :=
  Ready s base leaf start chain message values ∧
  EndpointWords hash s base leaf message values chain.val

def StrongDone (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest) : Prop :=
  Done s base leaf start message values ∧
  EndpointWords hash s base leaf message values 67

theorem run_to_after_copy_strong (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (chain : Fin 67)
    (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (ready : StrongReady hash s base leaf start chain message values) :
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
      EndpointWords hash copied base leaf message values (chain.val+1) := by
  obtain ⟨copied,trace,after,current,frame⟩ :=
    run_to_after_copy hash s base leaf start chain message values
      safe baseBound ready.1
  have endpoints := endpoint_words_copy hash s copied base leaf message
    values chain ready.1.outputPtr ready.2 current frame
  exact ⟨copied,trace,after,endpoints⟩

theorem strong_step_short (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (chain : Fin 67)
    (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (short : chain.val < 64)
    (ready : StrongReady hash s base leaf start chain message values) :
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
      StrongReady hash final base leaf start ⟨chain.val+1,by omega⟩
        message values := by
  obtain ⟨copied,first,after,endpoints⟩ :=
    run_to_after_copy_strong hash s base leaf start chain message values
      safe baseBound ready
  obtain ⟨second,next⟩ := after_copy_short copied base leaf start
    chain message values short after
  refine ⟨advanceState copied,?_,⟨next,?_⟩⟩
  · convert first.trans second.trace using 1 <;> omega
  · exact endpoint_words_mem hash copied (advanceState copied) base leaf
      message values _ endpoints (advance_mem copied)

theorem strong_step_64 (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (ready : StrongReady hash s base leaf start (64 : Fin 67)
      message values) :
    ∃ final,
      Trace hash image s
        (4 * (3 - (GroupedBalancedChecksum67.digit message (64 : Fin 67)).val) + 22)
        (11 * (3 - (GroupedBalancedChecksum67.digit message (64 : Fin 67)).val) + 22)
        (3 - (GroupedBalancedChecksum67.digit message (64 : Fin 67)).val)
        (3 - (GroupedBalancedChecksum67.digit message (64 : Fin 67)).val)
        final ∧
      StrongReady hash final base leaf start (65 : Fin 67)
        message values := by
  obtain ⟨copied,first,after,endpoints⟩ :=
    run_to_after_copy_strong hash s base leaf start (64 : Fin 67)
      message values safe baseBound ready
  obtain ⟨second,next⟩ := after_copy_64 copied base leaf start
    message values after
  refine ⟨next65State copied,?_,⟨next,?_⟩⟩
  · simp [GroupedBalancedChecksum67.maxDigit] at first
    convert first.trans second.trace using 1 <;> omega
  · exact endpoint_words_mem hash copied (next65State copied) base leaf
      message values _ endpoints (next65_mem copied)

theorem strong_step_65 (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (ready : StrongReady hash s base leaf start (65 : Fin 67)
      message values) :
    ∃ final,
      Trace hash image s
        (4 * (8 - (GroupedBalancedChecksum67.digit message (65 : Fin 67)).val) + 24)
        (11 * (8 - (GroupedBalancedChecksum67.digit message (65 : Fin 67)).val) + 24)
        (8 - (GroupedBalancedChecksum67.digit message (65 : Fin 67)).val)
        (8 - (GroupedBalancedChecksum67.digit message (65 : Fin 67)).val)
        final ∧
      StrongReady hash final base leaf start (66 : Fin 67)
        message values := by
  obtain ⟨copied,first,after,endpoints⟩ :=
    run_to_after_copy_strong hash s base leaf start (65 : Fin 67)
      message values safe baseBound ready
  obtain ⟨second,next⟩ := after_copy_65 copied base leaf start
    message values after
  refine ⟨next66State copied,?_,⟨next,?_⟩⟩
  · simp [GroupedBalancedChecksum67.maxDigit] at first
    convert first.trans second.trace using 1 <;> omega
  · exact endpoint_words_mem hash copied (next66State copied) base leaf
      message values _ endpoints (next66_mem copied)

theorem strong_step_66 (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (ready : StrongReady hash s base leaf start (66 : Fin 67)
      message values) :
    ∃ final,
      Trace hash image s
        (4 * (10 - (GroupedBalancedChecksum67.digit message (66 : Fin 67)).val) + 23)
        (11 * (10 - (GroupedBalancedChecksum67.digit message (66 : Fin 67)).val) + 23)
        (10 - (GroupedBalancedChecksum67.digit message (66 : Fin 67)).val)
        (10 - (GroupedBalancedChecksum67.digit message (66 : Fin 67)).val)
        final ∧
      StrongDone hash final base leaf start message values := by
  obtain ⟨copied,first,after,endpoints⟩ :=
    run_to_after_copy_strong hash s base leaf start (66 : Fin 67)
      message values safe baseBound ready
  obtain ⟨second,next⟩ := after_copy_66 copied base leaf start
    message values after
  refine ⟨nextDoneState copied,?_,⟨next,?_⟩⟩
  · simp [GroupedBalancedChecksum67.maxDigit] at first
    convert first.trans second.trace using 1 <;> omega
  · exact endpoint_words_mem hash copied (nextDoneState copied) base leaf
      message values _ endpoints (next_done_mem copied)

def StrongInvariant (hash : Hash) (base leaf start : Nat)
    (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (i : Nat) (s : MachineState) : Prop :=
  if hi : i < 67 then
    StrongReady hash s base leaf start ⟨i,hi⟩ message values
  else
    i = 67 ∧ StrongDone hash s base leaf start message values

theorem strong_concrete_step (hash : Hash)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (i : Nat) (hi : i < 67) (s : MachineState)
    (inv : StrongInvariant hash base leaf start message values i s) :
    ∃ final,
      Trace hash image s
        (stepsAt message i) (cyclesAt message i)
        (gapAt message i) (gapAt message i) final ∧
      StrongInvariant hash base leaf start message values (i+1) final := by
  have ready : StrongReady hash s base leaf start ⟨i,hi⟩
      message values := by
    simpa [StrongInvariant,hi] using inv
  by_cases short : i < 64
  · obtain ⟨final,trace,next⟩ := strong_step_short hash s base leaf start
      ⟨i,hi⟩ message values safe baseBound short ready
    have hnext : i+1 < 67 := by omega
    refine ⟨final,?_,?_⟩
    · have hgap := gap_at_eq message i hi
      have hover := overhead_at_eq i hi
      simpa [stepsAt,cyclesAt,hgap,hover,
        GroupedBalancedByteFastIteration67.overhead,short] using trace
    · simpa [StrongInvariant,hnext] using next
  · have cases : i = 64 ∨ i = 65 ∨ i = 66 := by omega
    rcases cases with eq64 | eq65 | eq66
    · subst i
      obtain ⟨final,trace,next⟩ := strong_step_64 hash s base leaf start
        message values safe baseBound (by simpa using ready)
      refine ⟨final,?_,?_⟩
      · simpa [stepsAt,cyclesAt,gap_at_eq,overhead_at_eq,
          GroupedBalancedByteFastIteration67.overhead,
          GroupedBalancedChecksum67.maxDigit] using trace
      · simpa [StrongInvariant] using next
    · subst i
      obtain ⟨final,trace,next⟩ := strong_step_65 hash s base leaf start
        message values safe baseBound (by simpa using ready)
      refine ⟨final,?_,?_⟩
      · simpa [stepsAt,cyclesAt,gap_at_eq,overhead_at_eq,
          GroupedBalancedByteFastIteration67.overhead,
          GroupedBalancedChecksum67.maxDigit] using trace
      · simpa [StrongInvariant] using next
    · subst i
      obtain ⟨final,trace,done⟩ := strong_step_66 hash s base leaf start
        message values safe baseBound (by simpa using ready)
      refine ⟨final,?_,?_⟩
      · simpa [stepsAt,cyclesAt,gap_at_eq,overhead_at_eq,
          GroupedBalancedByteFastIteration67.overhead,
          GroupedBalancedChecksum67.maxDigit] using trace
      · simpa [StrongInvariant] using done

/-- Complete WOTS instruction trace and all 67 endpoint words. -/
theorem all_wots_endpoints (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (ready : Ready s base leaf start (0 : Fin 67) message values) :
    ∃ final,
      Trace hash image s
        (4 * GroupedBalancedChecksum67.suffixCost message + 1221)
        (11 * GroupedBalancedChecksum67.suffixCost message + 1221)
        (GroupedBalancedChecksum67.suffixCost message)
        (GroupedBalancedChecksum67.suffixCost message) final ∧
      StrongDone hash final base leaf start message values := by
  have initial : StrongInvariant hash base leaf start message values 0 s := by
    simpa [StrongInvariant,StrongReady] using
      And.intro ready (initial_endpoints hash s base leaf message values)
  obtain ⟨final,trace,inv⟩ := fold_all hash image message
    (StrongInvariant hash base leaf start message values) s initial
    (fun i hi s proof => strong_concrete_step hash base leaf start message
      values safe baseBound i hi s proof)
  refine ⟨final,trace,?_⟩
  simpa [StrongInvariant] using inv

#print axioms strong_step_66
#print axioms all_wots_endpoints

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainEndpoints67
