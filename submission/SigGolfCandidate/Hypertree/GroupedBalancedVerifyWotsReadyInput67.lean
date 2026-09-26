import SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsReadyFields67

/-! The WOTS header writes leave the decoder's tables and digits intact. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsReadyInput67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyWotsReady67
open GroupedBalancedVerifyWotsHeaderFields67
open GroupedBalancedByteFastWotsFrame67
open GroupedBalancedVerifyByteContract67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

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

private theorem header_frame_at (s : MachineState) (a : Word)
    (low : a.toNat < 0x81030 ∨ 0x90020 ≤ a.toNat) :
    (GroupedBalancedVerifyWotsHeaderBlock67.headerState s).getMem a =
      s.getMem a := by
  have neq (b : Word) (middle : 0x81030 ≤ b.toNat ∧
      b.toNat < 0x90020) : a ≠ b := by
    intro eq
    rcases low with lo | hi
    · rw [eq] at lo
      omega
    · rw [eq] at hi
      omega
  apply header_mem_frame
  all_goals apply neq _; decide

private theorem ready_byte_frame (s : MachineState) (a : Word)
    (low : (alignToDword a).toNat < 0x81030 ∨
      0x90020 ≤ (alignToDword a).toNat) :
    (readyState s).getByte a = s.getByte a := by
  simp only [MachineState.getByte]
  rw [ready_mem,header_frame_at s _ low]

theorem ready_tables (s : MachineState) (tables : Tables s) :
    Tables (readyState s) := by
  intro i hi
  let a : Word := BitVec.ofNat 64 (0xfff700+i)
  have ha : a.toNat = 0xfff700+i := by
    simp only [a,BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hd := align_decomp a
  have ho := byteOffset_lt_8 (addr := a)
  have high : 0x90020 ≤ (alignToDword a).toNat := by omega
  exact (ready_byte_frame s a (Or.inr high)).trans (tables i hi)

theorem ready_digits (s : MachineState) (message : Reference.Digest)
    (digits : Digits s message) :
    Digits (readyState s) message := by
  intro chain
  let a : Word := BitVec.ofNat 64 (0x80600+chain.val)
  have ha : a.toNat = 0x80600+chain.val := by
    simp only [a,BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hd := align_decomp a
  have ho := byteOffset_lt_8 (addr := a)
  have low : (alignToDword a).toNat < 0x81030 := by omega
  exact (ready_byte_frame s a (Or.inl low)).trans (digits chain)

theorem ready_first (s : MachineState) (base leaf start : Nat)
    (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (pc : s.pc = 0x1518)
    (baseWord : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (index : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (startWord : s.getMem 0x81048 = BitVec.ofNat 64 start)
    (safe : GroupedBalancedByteFastChainReady67.SafeWitnesses start)
    (witnesses : GroupedBalancedByteFastChainReady67.WitnessWords
      s start values)
    (tables : Tables s)
    (digits : Digits s message) :
    GroupedBalancedByteFastChainReady67.Ready
      (readyState s) base leaf start ⟨0,by decide⟩ message values :=
  GroupedBalancedVerifyWotsReadyFields67.ready_first
    s base leaf start message values pc baseWord index startWord
      safe witnesses (ready_tables s tables) (ready_digits s message digits)

#print axioms ready_tables
#print axioms ready_digits
#print axioms ready_first
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsReadyInput67
