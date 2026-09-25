import SigGolfCandidate.Hypertree.BalancedPatchTail
import SigGolfCandidate.Hypertree.BalancedPatchWords

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def tailPass (s : MachineState) : MachineState :=
  flipTail (flipTail (flipTail s 40) 41) 42

theorem tailPass_block (image : Image) (entry start : Word) (forward back : BitVec 21)
    (code : PatchCode image entry start forward back)
    (s : MachineState) (pc : s.pc = start+96)
    (base : s.getReg .x15 = 0x80600) :
    OrdinarySteps image s 9 (tailPass s) := by
  let s1 := flipTail s 40
  let s2 := flipTail s1 41
  let s3 := flipTail s2 42
  have base1 : s1.getReg .x15 = 0x80600 := (flipTail_regs s 40).1.trans base
  have base2 : s2.getReg .x15 = 0x80600 := (flipTail_regs s1 41).1.trans base1
  have b0 : OrdinarySteps image s 3 s1 :=
    flipTail_block image (start+96) 40 (patch_tail_code image entry start forward back code 0)
      s pc (by rw [base]; decide)
  have b1 : OrdinarySteps image s1 3 s2 :=
    flipTail_block image (start+108) 41 (patch_tail_code image entry start forward back code 1)
      s1 (by simp [s1,flipTail_pc,pc,BitVec.add_assoc]) (by rw [base1]; decide)
  have b2 : OrdinarySteps image s2 3 s3 :=
    flipTail_block image (start+120) 42 (patch_tail_code image entry start forward back code 2)
      s2 (by simp [s2,s1,flipTail_pc,pc,BitVec.add_assoc]) (by rw [base2]; decide)
  change OrdinarySteps image s 9 s3
  exact Keygen.ordinary_trans image s _ _ 6 3
    (Keygen.ordinary_trans image s _ _ 3 3 b0 b1) b2

theorem tailPass_pc (s : MachineState) : (tailPass s).pc = s.pc+36 := by
  simp [tailPass,flipTail_pc,BitVec.add_assoc]

theorem tailPass_regs (s : MachineState) :
    (tailPass s).getReg .x15 = s.getReg .x15 ∧
    (tailPass s).getReg .x16 = s.getReg .x16 ∧
    (tailPass s).getReg .x12 = s.getReg .x12 ∧
    (tailPass s).getReg .x10 = s.getReg .x10 ∧
    (tailPass s).getReg .x2 = s.getReg .x2 := by
  simp [tailPass, (flipTail_regs _ _).1, (flipTail_regs _ _).2.1,
    (flipTail_regs _ _).2.2.1, (flipTail_regs _ _).2.2.2.1,
    (flipTail_regs _ _).2.2.2.2]

theorem tailPass_ra (s : MachineState) :
    (tailPass s).getReg .x1 = s.getReg .x1 := by
  simp [tailPass,flipTail,execInstrBr,MachineState.getReg_setReg_ne]

private theorem tailPass_base1 (s : MachineState) (base : s.getReg .x15 = 0x80600) :
    (flipTail s 40).getReg .x15 = 0x80600 := (flipTail_regs s 40).1.trans base
private theorem tailPass_base2 (s : MachineState) (base : s.getReg .x15 = 0x80600) :
    (flipTail (flipTail s 40) 41).getReg .x15 = 0x80600 :=
  (flipTail_regs (flipTail s 40) 41).1.trans (tailPass_base1 s base)

theorem tailPass_digit (s : MachineState) (i : Fin 3)
    (base : s.getReg .x15 = 0x80600)
    (raw : ∀ j : Fin 3,
      (s.getByte (BitVec.ofNat 64 (0x80600+40+j.val))).toNat ≤ 7) :
    (tailPass s).getByte (BitVec.ofNat 64 (0x80600+40+i.val)) =
      BitVec.ofNat 8 (7-(s.getByte (BitVec.ofNat 64 (0x80600+40+i.val))).toNat) := by
  let s1 := flipTail s 40
  let s2 := flipTail s1 41
  have base1 : s1.getReg .x15 = 0x80600 := tailPass_base1 s base
  have base2 : s2.getReg .x15 = 0x80600 := tailPass_base2 s base
  fin_cases i
  · have h0 := flipTail_digit s 0 base (raw 0)
    have h1 := flipTail_other s1 1 (BitVec.ofNat 64 (0x80600+40)) base1 (by decide)
    have h2 := flipTail_other s2 2 (BitVec.ofNat 64 (0x80600+40)) base2 (by decide)
    simpa [tailPass,s1,s2] using h2.trans (h1.trans h0)
  · have old : s1.getByte (BitVec.ofNat 64 (0x80600+41)) =
        s.getByte (BitVec.ofNat 64 (0x80600+41)) :=
      flipTail_other s 0 _ base (by decide)
    have raw1 : (s1.getByte (BitVec.ofNat 64 (0x80600+40+(1:Fin 3).val))).toNat ≤ 7 := by
      change (s1.getByte (BitVec.ofNat 64 (0x80600+41))).toNat ≤ 7
      rw [old]
      simpa using raw 1
    have h1 := flipTail_digit s1 1 base1 raw1
    have h2 := flipTail_other s2 2 (BitVec.ofNat 64 (0x80600+41)) base2 (by decide)
    change s2.getByte (BitVec.ofNat 64 (0x80600+41)) =
      BitVec.ofNat 8 (7-(s1.getByte (BitVec.ofNat 64 (0x80600+41))).toNat) at h1
    rw [old] at h1
    simpa [tailPass,s1,s2] using h2.trans h1
  · have old0 : s1.getByte (BitVec.ofNat 64 (0x80600+42)) =
        s.getByte (BitVec.ofNat 64 (0x80600+42)) :=
      flipTail_other s 0 _ base (by decide)
    have old1 : s2.getByte (BitVec.ofNat 64 (0x80600+42)) =
        s1.getByte (BitVec.ofNat 64 (0x80600+42)) :=
      flipTail_other s1 1 _ base1 (by decide)
    have raw2 : (s2.getByte (BitVec.ofNat 64 (0x80600+40+(2:Fin 3).val))).toNat ≤ 7 := by
      change (s2.getByte (BitVec.ofNat 64 (0x80600+42))).toNat ≤ 7
      rw [old1,old0]
      simpa using raw 2
    have h2 := flipTail_digit s2 2 base2 raw2
    change (tailPass s).getByte (BitVec.ofNat 64 (0x80600+42)) =
      BitVec.ofNat 8 (7-(s2.getByte (BitVec.ofNat 64 (0x80600+42))).toNat) at h2
    rw [old1,old0] at h2
    simpa using h2

theorem tailPass_other (s : MachineState) (a : Word)
    (base : s.getReg .x15 = 0x80600)
    (outside : ∀ i : Fin 3, a ≠ BitVec.ofNat 64 (0x80600+40+i.val)) :
    (tailPass s).getByte a = s.getByte a := by
  let s1 := flipTail s 40
  let s2 := flipTail s1 41
  have base1 : s1.getReg .x15 = 0x80600 := tailPass_base1 s base
  have base2 : s2.getReg .x15 = 0x80600 := tailPass_base2 s base
  have h0 := flipTail_other s 0 a base (outside 0)
  have h1 := flipTail_other s1 1 a base1 (outside 1)
  have h2 := flipTail_other s2 2 a base2 (outside 2)
  simpa [tailPass,s1,s2] using h2.trans (h1.trans h0)

#print axioms tailPass_block
#print axioms tailPass_digit
#print axioms tailPass_other
end SigGolfCandidate.Hypertree.Signing
