import SigGolfCandidate.Hypertree.BalancedPatch

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion

private theorem tail_address (s : MachineState) (j : Fin 3)
    (base : s.getReg .x15 = 0x80600) :
    BitVec.ofNat 64 (0x80600+40+j.val) =
      s.getReg .x15 + signExtend12 (BitVec.ofNat 12 (40+j.val)) := by
  rw [base]
  fin_cases j <;> decide

/-- The three trailing message bytes are complemented bytewise. -/
theorem flipTail_digit (s : MachineState) (j : Fin 3)
    (base : s.getReg .x15 = 0x80600)
    (raw : (s.getByte (BitVec.ofNat 64 (0x80600+40+j.val))).toNat ≤ 7) :
    (flipTail s (BitVec.ofNat 12 (40+j.val))).getByte
        (BitVec.ofNat 64 (0x80600+40+j.val)) =
      BitVec.ofNat 8 (7-(s.getByte (BitVec.ofNat 64 (0x80600+40+j.val))).toNat) := by
  have addr := tail_address s j base
  rw [flipTail_byte, if_pos addr]
  rw [← addr]
  have small : (s.getByte (BitVec.ofNat 64 (0x80600+40+j.val))).toNat < 8 := by omega
  simpa using BalancedPacked.flip_digit _ small

/-- Every other byte is unchanged by a trailing flip. -/
theorem flipTail_other (s : MachineState) (j : Fin 3) (a : Word)
    (base : s.getReg .x15 = 0x80600)
    (outside : a ≠ BitVec.ofNat 64 (0x80600+40+j.val)) :
    (flipTail s (BitVec.ofNat 12 (40+j.val))).getByte a = s.getByte a := by
  have addr := tail_address s j base
  rw [flipTail_byte, if_neg]
  simpa only [← addr] using outside

#print axioms flipTail_digit
#print axioms flipTail_other
end SigGolfCandidate.Hypertree.Signing
