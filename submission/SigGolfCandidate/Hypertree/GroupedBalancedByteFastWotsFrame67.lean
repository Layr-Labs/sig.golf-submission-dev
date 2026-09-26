import SigGolfCandidate.Hypertree.GroupedBalancedByteFastIteration67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteContract67

/-! The upper WOTS chain never overwrites the decoder tables or digits. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastWotsFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.Signing
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixData67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastPrologue67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastEndpoint67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastLimit67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteContract67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def Digits (s : MachineState) (message : BitVec 128) : Prop :=
  ∀ chain : Fin 67,
    s.getByte (BitVec.ofNat 64 (0x80600+chain.val)) =
      BitVec.ofNat 8 (GroupedBalancedChecksum67.digit message chain).val

private theorem align_decomp (a : Word) :
    (alignToDword a).toNat + byteOffset a = a.toNat := by
  unfold alignToDword byteOffset
  simp only [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ofNat,
    show (7 : Nat) % 2^64 = 7 from rfl]
  have hlo : a.toNat &&& 7 = a.toNat % 8 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod a.toNat 3
  have hhi_mod : (a.toNat &&& (2^64-1-7)) % 8 = 0 := by
    rw [show (8 : Nat) = 2^3 from rfl, Nat.and_mod_two_pow,
      show (2^64-1-7 : Nat) % 2^3 = 0 from by decide]
    simp
  have hhi_div : (a.toNat &&& (2^64-1-7)) / 8 = a.toNat / 8 := by
    rw [show (8 : Nat) = 2^3 from rfl, Nat.and_div_two_pow,
      show (2^64-1-7 : Nat) / 2^3 = 2^61-1 from by decide]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow
      (by have := a.isLt; omega)
  have hhi : a.toNat &&& (2^64-1-7) = a.toNat / 8 * 8 := by
    have heucl := Nat.div_add_mod (a.toNat &&& (2^64-1-7)) 8
    omega
  rw [hlo,hhi]
  omega

private theorem table_align_high (i : Nat) (hi : i < 2304) :
    0x90040 ≤ (alignToDword (BitVec.ofNat 64 (0xfff700+i))).toNat := by
  let a : Word := BitVec.ofNat 64 (0xfff700+i)
  have ha : a.toNat = 0xfff700+i := by
    have bound : 0xfff700+i < 2^64 := by omega
    simpa [a,BitVec.toNat_ofNat] using (Nat.mod_eq_of_lt bound)
  have decomp := align_decomp a
  have offset := byteOffset_lt_8 (addr := a)
  change 0x90040 ≤ (alignToDword a).toNat
  omega

private theorem digit_align_bounds (i : Nat) (hi : i < 67) :
    0x80500 ≤ (alignToDword (BitVec.ofNat 64 (0x80600+i))).toNat ∧
      (alignToDword (BitVec.ofNat 64 (0x80600+i))).toNat < 0x90000 := by
  let a : Word := BitVec.ofNat 64 (0x80600+i)
  have ha : a.toNat = 0x80600+i := by
    have bound : 0x80600+i < 2^64 := by omega
    simpa [a,BitVec.toNat_ofNat] using (Nat.mod_eq_of_lt bound)
  have decomp := align_decomp a
  have offset := byteOffset_lt_8 (addr := a)
  change 0x80500 ≤ (alignToDword a).toNat ∧
    (alignToDword a).toNat < 0x90000
  omega

private theorem outside_high (a : Word) (high : 0x90040 ≤ a.toNat) :
    OutsideTick a := by
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    have hc : (0x90000 : Word).toNat = 0x90000 := by decide
    rw [hc] at hn
    omega
  · intro j h
    have hn := congrArg BitVec.toNat h
    simp only [wordAddress, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x90020+8*j.val < 2^64)] at hn
    omega

private theorem outside_low (a : Word) (low : a.toNat < 0x90000) :
    OutsideTick a := by
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    have hc : (0x90000 : Word).toNat = 0x90000 := by decide
    rw [hc] at hn
    omega
  · intro j h
    have hn := congrArg BitVec.toNat h
    simp only [wordAddress, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x90020+8*j.val < 2^64)] at hn
    omega

private theorem byte_of_mem_frame (s t : MachineState) (a : Word)
    (mem : t.getMem (alignToDword a) = s.getMem (alignToDword a)) :
    t.getByte a = s.getByte a := by
  simp only [MachineState.getByte]
  rw [mem]

theorem input_frame_of_endpoint (s final : MachineState)
    (message : BitVec 128)
    (dest0 : (s.getReg .x24).toNat < 0x80500)
    (dest8 : (s.getReg .x24 + 8).toNat < 0x80500)
    (frame : ∀ a, OutsideTick a → a ≠ s.getReg .x24 →
      a ≠ s.getReg .x24 + 8 → final.getMem a = s.getMem a)
    (tables : Tables s) (digits : Digits s message) :
    Tables final ∧ Digits final message := by
  constructor
  · intro i hi
    let a : Word := BitVec.ofNat 64 (0xfff700+i)
    have high : 0x90040 ≤ (alignToDword a).toNat :=
      table_align_high i hi
    have hout : OutsideTick (alignToDword a) := outside_high _ high
    have hne0 : alignToDword a ≠ s.getReg .x24 := by
      intro h
      have hn := congrArg BitVec.toNat h
      omega
    have hne8 : alignToDword a ≠ s.getReg .x24 + 8 := by
      intro h
      have hn := congrArg BitVec.toNat h
      omega
    exact (byte_of_mem_frame s final a (frame _ hout hne0 hne8)).trans
      (tables i hi)
  · intro chain
    let a : Word := BitVec.ofNat 64 (0x80600+chain.val)
    have bounds : 0x80500 ≤ (alignToDword a).toNat ∧
        (alignToDword a).toNat < 0x90000 :=
      digit_align_bounds chain.val chain.isLt
    have hout : OutsideTick (alignToDword a) := outside_low _ bounds.2
    have hne0 : alignToDword a ≠ s.getReg .x24 := by
      intro h
      have hn := congrArg BitVec.toNat h
      omega
    have hne8 : alignToDword a ≠ s.getReg .x24 + 8 := by
      intro h
      have hn := congrArg BitVec.toNat h
      omega
    exact (byte_of_mem_frame s final a (frame _ hout hne0 hne8)).trans
      (digits chain)

/-- Endpoint stores start at the WOTS output buffer. Every earlier witness
word remains available for subsequent upper groups. -/
theorem low_frame_of_endpoint (s final : MachineState)
    (dest0 : 0x80020 ≤ (s.getReg .x24).toNat)
    (dest8 : 0x80020 ≤ (s.getReg .x24 + 8).toNat)
    (frame : ∀ a, OutsideTick a → a ≠ s.getReg .x24 →
      a ≠ s.getReg .x24 + 8 → final.getMem a = s.getMem a) :
    ∀ a : Word, a.toNat < 0x80020 → final.getMem a = s.getMem a := by
  intro a low
  have hout : OutsideTick a := outside_low a (by omega)
  have hne0 : a ≠ s.getReg .x24 := by
    intro h
    have hn := congrArg BitVec.toNat h
    omega
  have hne8 : a ≠ s.getReg .x24 + 8 := by
    intro h
    have hn := congrArg BitVec.toNat h
    omega
  exact frame a hout hne0 hne8

theorem low_byte_frame_of_endpoint (s final : MachineState)
    (dest0 : 0x80020 ≤ (s.getReg .x24).toNat)
    (dest8 : 0x80020 ≤ (s.getReg .x24 + 8).toNat)
    (frame : ∀ a, OutsideTick a → a ≠ s.getReg .x24 →
      a ≠ s.getReg .x24 + 8 → final.getMem a = s.getMem a) :
    ∀ a : Word, a.toNat < 0x80020 → final.getByte a = s.getByte a := by
  intro a low
  have lowWord : (alignToDword a).toNat < 0x80020 := by
    have decomp := align_decomp a
    omega
  exact byte_of_mem_frame s final a
    (low_frame_of_endpoint s final dest0 dest8 frame _ lowWord)

#print axioms input_frame_of_endpoint

private theorem input_frame_of_mem_eq (s final : MachineState)
    (message : BitVec 128)
    (mem : ∀ a : Word, final.getMem a = s.getMem a)
    (tables : Tables s) (digits : Digits s message) :
    Tables final ∧ Digits final message := by
  constructor
  · intro i hi
    exact (byte_of_mem_frame s final _ (mem _)).trans (tables i hi)
  · intro chain
    exact (byte_of_mem_frame s final _ (mem _)).trans (digits chain)

theorem advance_input_frame (s : MachineState) (message : BitVec 128)
    (tables : Tables s) (digits : Digits s message) :
    Tables (advanceState s) ∧ Digits (advanceState s) message :=
  input_frame_of_mem_eq s (advanceState s) message (advance_mem s) tables digits

theorem next65_input_frame (s : MachineState) (message : BitVec 128)
    (tables : Tables s) (digits : Digits s message) :
    Tables (next65State s) ∧ Digits (next65State s) message :=
  input_frame_of_mem_eq s (next65State s) message (next65_mem s) tables digits

theorem next66_input_frame (s : MachineState) (message : BitVec 128)
    (tables : Tables s) (digits : Digits s message) :
    Tables (next66State s) ∧ Digits (next66State s) message :=
  input_frame_of_mem_eq s (next66State s) message (next66_mem s) tables digits

theorem nextDone_input_frame (s : MachineState) (message : BitVec 128)
    (tables : Tables s) (digits : Digits s message) :
    Tables (nextDoneState s) ∧ Digits (nextDoneState s) message :=
  input_frame_of_mem_eq s (nextDoneState s) message (next_done_mem s) tables digits

theorem low_frame_of_mem_eq (s t : MachineState)
    (mem : ∀ a, t.getMem a = s.getMem a) :
    ∀ a : Word, a.toNat < 0x80020 → t.getMem a = s.getMem a := by
  intro a _
  exact mem a

theorem advance_low_frame (s : MachineState) :
    ∀ a : Word, a.toNat < 0x80020 →
      (advanceState s).getMem a = s.getMem a :=
  low_frame_of_mem_eq s (advanceState s) (advance_mem s)

theorem next65_low_frame (s : MachineState) :
    ∀ a : Word, a.toNat < 0x80020 →
      (next65State s).getMem a = s.getMem a :=
  low_frame_of_mem_eq s (next65State s) (next65_mem s)

theorem next66_low_frame (s : MachineState) :
    ∀ a : Word, a.toNat < 0x80020 →
      (next66State s).getMem a = s.getMem a :=
  low_frame_of_mem_eq s (next66State s) (next66_mem s)

theorem nextDone_low_frame (s : MachineState) :
    ∀ a : Word, a.toNat < 0x80020 →
      (nextDoneState s).getMem a = s.getMem a :=
  low_frame_of_mem_eq s (nextDoneState s) (next_done_mem s)

theorem chain_dest_low (s : MachineState)
    (chain : GroupedBalancedChecksum67.Chain)
    (ptr : s.getReg .x24 = BitVec.ofNat 64 (0x80020+16*chain.val)) :
    (s.getReg .x24).toNat < 0x80500 ∧
      (s.getReg .x24 + 8).toNat < 0x80500 := by
  constructor
  · rw [ptr]
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80020+16*chain.val < 2^64)]
    omega
  · rw [ptr]
    rw [BitVec.toNat_add]
    have h0 : (BitVec.ofNat 64 (0x80020+16*chain.val)).toNat =
        0x80020+16*chain.val := by
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80020+16*chain.val < 2^64)]
    have h8 : (8 : Word).toNat = 8 := by decide
    rw [h0,h8]
    rw [Nat.mod_eq_of_lt (by omega : 0x80020+16*chain.val+8 < 2^64)]
    omega

theorem chain_dest_ge (s : MachineState)
    (chain : GroupedBalancedChecksum67.Chain)
    (ptr : s.getReg .x24 = BitVec.ofNat 64 (0x80020+16*chain.val)) :
    0x80020 ≤ (s.getReg .x24).toNat ∧
      0x80020 ≤ (s.getReg .x24 + 8).toNat := by
  constructor
  · rw [ptr]
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80020+16*chain.val < 2^64)]
    omega
  · rw [ptr, BitVec.toNat_add]
    have h0 : (BitVec.ofNat 64 (0x80020+16*chain.val)).toNat =
        0x80020+16*chain.val := by
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80020+16*chain.val < 2^64)]
    have h8 : (8 : Word).toNat = 8 := by decide
    rw [h0,h8]
    rw [Nat.mod_eq_of_lt (by omega : 0x80020+16*chain.val+8 < 2^64)]
    omega

#print axioms chain_dest_low

theorem run_chain_input_frame (hash : Hash) (s : MachineState)
    (base leaf : Nat) (chain : GroupedBalancedChecksum67.Chain)
    (message value : Reference.Digest)
    (pc : s.pc = 0x1608)
    (valid0 : accessValid (s.getReg .x22) 8 = true)
    (valid8 : accessValid (s.getReg .x22 + 8) 8 = true)
    (digitValid : accessValid (s.getReg .x25) 1 = true)
    (dst0 : accessValid (s.getReg .x24) 8 = true)
    (dst8 : accessValid (s.getReg .x24 + 8) 8 = true)
    (baseBound : base < 256)
    (data : EntryData s base leaf chain message value)
    (ptr : s.getReg .x24 = BitVec.ofNat 64 (0x80020+16*chain.val))
    (tables : Tables s) (digits : Digits s message) :
    ∃ copied,
      Trace hash GroupedBalancedByteFastSuffixLoop67.image s
        (4 * (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) + 15)
        (11 * (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) + 15)
        (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val)
        (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) copied ∧
      copied.pc = 0x1654 ∧
      (∀ i : Fin 2,
        copied.getMem (s.getReg .x24 + BitVec.ofNat 64 (8*i.val)) =
          (walk (GroupedBalancedUpperTree67.chainHash hash base leaf chain)
            (GroupedBalancedChecksum67.digit message chain).val
            (GroupedBalancedChecksum67.maxDigit chain -
              (GroupedBalancedChecksum67.digit message chain).val) value).extractLsb'
              (64*i.val) 64) ∧
      copied.getReg .x23 = s.getReg .x23 ∧
      copied.getReg .x24 = s.getReg .x24 + 16 ∧
      copied.getReg .x25 = s.getReg .x25 + 1 ∧
      copied.getReg .x20 = s.getReg .x20 ∧
      Tables copied ∧ Digits copied message ∧
      (∀ a : Word, a.toNat < 0x80020 →
        copied.getMem a = s.getMem a) := by
  obtain ⟨copied, trace, copiedPC, copiedValue, copiedChain,
    copiedPtr, copiedDigitPtr, copiedLimit, frame⟩ :=
    run_chain_and_copy hash s base leaf chain message value pc
      valid0 valid8 digitValid dst0 dst8 baseBound data
  obtain ⟨dest0,dest8⟩ := chain_dest_low s chain ptr
  obtain ⟨dest0ge,dest8ge⟩ := chain_dest_ge s chain ptr
  obtain ⟨copiedTables,copiedDigits⟩ :=
    input_frame_of_endpoint s copied message dest0 dest8 frame tables digits
  exact ⟨copied, trace, copiedPC, copiedValue, copiedChain,
    copiedPtr, copiedDigitPtr, copiedLimit, copiedTables, copiedDigits,
    low_frame_of_endpoint s copied dest0ge dest8ge frame⟩

#print axioms run_chain_input_frame

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastWotsFrame67
