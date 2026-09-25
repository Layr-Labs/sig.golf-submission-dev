import SigGolfCandidate.Hypertree.BalancedPatchBodySemantics

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion
set_option maxRecDepth 4096

/-- The flipped bytes encode the balanced payload digit on the low-sum branch. -/
theorem flipBody_payload (s : MachineState) (message : Reference.Digest)
    (base : s.getReg .x15 = 0x80600)
    (mask : s.getReg .x16 = 0x0707070707070707)
    (rawDigits : ∀ i : Fin 43,
      s.getByte (BitVec.ofNat 64 (0x80600+i.val)) =
        BitVec.ofNat 8 (Reference.messageDigit message i))
    (flip : Reference.needsFlip message) :
    ∀ i : Fin 43,
      (flipBody s).getByte (BitVec.ofNat 64 (0x80600+i.val)) =
        BitVec.ofNat 8 (Reference.payloadDigit message i) := by
  have bound (i : Fin 43) : Reference.messageDigit message i < 8 := by
    unfold Reference.messageDigit
    exact Nat.mod_lt _ (by decide)
  have rawBound : ∀ i : Fin 43,
      (s.getByte (BitVec.ofNat 64 (0x80600+i.val))).toNat ≤ 7 := by
    intro i
    rw [rawDigits i, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := bound i; omega :
      Reference.messageDigit message i < 2^8)]
    have := bound i
    omega
  intro i
  have changed := flipBody_byte s i base mask rawBound
  rw [rawDigits i, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := bound i; omega : Reference.messageDigit message i < 2^8)] at changed
  simpa only [Reference.payloadDigit, if_pos flip] using changed

/-- The low-sum branch is the only path that changes raw message digits. -/
theorem rawDigits_payload_no_flip (s : MachineState) (message : Reference.Digest)
    (rawDigits : ∀ i : Fin 43,
      s.getByte (BitVec.ofNat 64 (0x80600+i.val)) =
        BitVec.ofNat 8 (Reference.messageDigit message i))
    (noFlip : ¬ Reference.needsFlip message) :
    ∀ i : Fin 43,
      s.getByte (BitVec.ofNat 64 (0x80600+i.val)) =
        BitVec.ofNat 8 (Reference.payloadDigit message i) := by
  intro i
  simpa only [Reference.payloadDigit, if_neg noFlip] using rawDigits i

#print axioms flipBody_payload
#print axioms rawDigits_payload_no_flip
end SigGolfCandidate.Hypertree.Signing
