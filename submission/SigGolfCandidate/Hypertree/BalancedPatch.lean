import Mathlib
import SigGolfCandidate.Hypertree.SignEncodeFinish

/-! Inlined from SigGolfCandidate.Hypertree.BalancedPacked; its only importer was SigGolfCandidate.Hypertree.BalancedPatch. -/
section
namespace SigGolfCandidate.Hypertree.BalancedPacked
set_option maxHeartbeats 1000000

def mask : Nat → Nat
  | 0 => 0
  | k+1 => 7 + 256 * mask k

theorem flip_rec (k : Nat) : ∀ n : Nat, n < 256^k →
    (∀ i, i < k → n / 256^i % 256 ≤ 7) →
    n ≤ mask k ∧ ∀ i, i < k →
      (mask k - n) / 256^i % 256 = 7 - n / 256^i % 256 := by
  induction k with
  | zero =>
    intro n hn _
    have nzero : n = 0 := by simpa using hn
    subst n
    constructor
    · simp [mask]
    · intro i hi; omega
  | succ k ih =>
    intro n hn hb
    have hq : n / 256 < 256^k := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa only [pow_succ, Nat.mul_comm] using hn
    have hbq : ∀ i, i < k → (n/256) / 256^i % 256 ≤ 7 := by
      intro i hi
      have h := hb (i+1) (by omega)
      simpa only [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm] using h
    obtain ⟨qle, qdigits⟩ := ih (n/256) hq hbq
    have hd : n % 256 ≤ 7 := by simpa using hb 0 (by omega)
    have ndec : n = 256 * (n/256) + n%256 := by omega
    have hle : n ≤ mask (k+1) := by simp only [mask]; omega
    refine ⟨hle, ?_⟩
    intro i hi
    have hsub : mask (k+1) - n = (7 - n%256) + 256*(mask k - n/256) := by
      simp only [mask]
      omega
    rw [hsub]
    cases i with
    | zero =>
      simp only [pow_zero, Nat.div_one]
      omega
    | succ j =>
      have hj : j < k := by omega
      have hr : 7 - n%256 < 256 := by omega
      have hquot : ((7-n%256)+256*(mask k-n/256))/256 = mask k-n/256 := by omega
      have dpow : 256^(j+1) = 256*256^j := by simp [pow_succ, Nat.mul_comm]
      rw [dpow, ← Nat.div_div_eq_div_mul, hquot]
      rw [← Nat.div_div_eq_div_mul]
      exact qdigits j hj
#print axioms flip_rec

theorem mask8_eq : mask 8 = 0x0707070707070707 := by decide

private theorem pow_byte (i : Nat) : 2 ^ (8*i) = 256^i := by
  rw [pow_mul]
  norm_num

theorem flip_word_byte (w : BitVec 64)
    (hb : ∀ i : Fin 8, (w.extractLsb' (8*i.val) 8).toNat ≤ 7)
    (i : Fin 8) :
    ((0x0707070707070707#64 - w).extractLsb' (8*i.val) 8).toNat =
      7 - (w.extractLsb' (8*i.val) 8).toNat := by
  have hbytes : ∀ j, j < 8 → w.toNat / 256^j % 256 ≤ 7 := by
    intro j hj
    have h := hb ⟨j,hj⟩
    simpa only [BitVec.extractLsb', BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, pow_byte] using h
  obtain ⟨hle, hrec⟩ := flip_rec 8 w.toNat (by
    simpa only [show 256^8 = 2^64 by decide] using w.isLt) hbytes
  have hmask : (0x0707070707070707#64).toNat = mask 8 := by
    rw [mask8_eq]
    decide
  have hmaskLt : mask 8 < 2^64 := by rw [mask8_eq]; decide
  have hsub : (0x0707070707070707#64 - w).toNat = mask 8 - w.toNat := by
    rw [BitVec.toNat_sub, hmask]
    have hx := w.isLt
    omega
  simpa only [BitVec.extractLsb', BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, pow_byte, hsub] using hrec i.val i.isLt
#print axioms flip_word_byte

theorem flip_digit (d : Nat) (hd : d < 8) :
    (BitVec.ofNat 8 d ^^^ 7#8) = BitVec.ofNat 8 (7-d) := by
  interval_cases d <;> decide
#print axioms flip_digit
end SigGolfCandidate.Hypertree.BalancedPacked

end

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def patchInstructions (back : BitVec 21) : List Instr := [
  .ADDI .x14 .x12 (-151),
  .SRLI .x14 .x14 63,
  .BNE .x14 .x0 132,
  .LUI .x15 0x80,
  .ADDI .x15 .x15 0x600,
  .LUI .x16 0x7070,
  .ADDI .x16 .x16 0x707,
  .SLLI .x17 .x16 32,
  .ADD .x16 .x16 .x17,
  .LD .x17 .x15 0,
  .SUB .x17 .x16 .x17,
  .SD .x15 .x17 0,
  .LD .x17 .x15 8,
  .SUB .x17 .x16 .x17,
  .SD .x15 .x17 8,
  .LD .x17 .x15 16,
  .SUB .x17 .x16 .x17,
  .SD .x15 .x17 16,
  .LD .x17 .x15 24,
  .SUB .x17 .x16 .x17,
  .SD .x15 .x17 24,
  .LD .x17 .x15 32,
  .SUB .x17 .x16 .x17,
  .SD .x15 .x17 32,
  .LBU .x17 .x15 40,
  .XORI .x17 .x17 7,
  .SB .x15 .x17 40,
  .LBU .x17 .x15 41,
  .XORI .x17 .x17 7,
  .SB .x15 .x17 41,
  .LBU .x17 .x15 42,
  .XORI .x17 .x17 7,
  .SB .x15 .x17 42,
  .ADDI .x14 .x0 301,
  .SUB .x12 .x14 .x12,
  .ANDI .x13 .x12 7,
  .JAL .x0 back]

def PatchCode (image : Image) (entry start : Word) (forward back : BitVec 21) : Prop :=
  instructionAt image entry = some (.base (.JAL .x0 forward)) ∧
  ∀ i : Fin 37, instructionAt image (start + BitVec.ofNat 64 (4*i.val)) =
    some (.base ((patchInstructions back)[i.val]'(by simpa [patchInstructions] using i.isLt)))

theorem sign_patch_code : PatchCode sign 0x1398 0x1c70 0x8d8 (-2404) := by
  constructor
  · decide
  · intro i; fin_cases i <;> decide

theorem verify_patch_code : PatchCode verify 0x12c0 0x1948 0x688 (-1812) := by
  constructor
  · decide
  · intro i; fin_cases i <;> decide

def flipChunk (s : MachineState) (off : BitVec 12) : MachineState :=
  let s := execInstrBr s (.LD .x17 .x15 off)
  let s := execInstrBr s (.SUB .x17 .x16 .x17)
  execInstrBr s (.SD .x15 .x17 off)

theorem flipChunk_mem (s : MachineState) (off : BitVec 12) (a : Word) :
    (flipChunk s off).getMem a =
      if a = s.getReg .x15 + signExtend12 off then
        s.getReg .x16 - s.getMem (s.getReg .x15 + signExtend12 off)
      else s.getMem a := by
  simp [flipChunk, execInstrBr, signExtend12, Expansion.mem_setMem,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  rfl

theorem flipChunk_regs (s : MachineState) (off : BitVec 12) :
    (flipChunk s off).getReg .x15 = s.getReg .x15 ∧
    (flipChunk s off).getReg .x16 = s.getReg .x16 ∧
    (flipChunk s off).getReg .x12 = s.getReg .x12 ∧
    (flipChunk s off).getReg .x10 = s.getReg .x10 ∧
    (flipChunk s off).getReg .x2 = s.getReg .x2 := by
  simp [flipChunk, execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem flipChunk_pc (s : MachineState) (off : BitVec 12) :
    (flipChunk s off).pc = s.pc + 12 := by
  simp [flipChunk, execInstrBr, BitVec.add_assoc]

def ChunkCode (image : Image) (pc : Word) (off : BitVec 12) : Prop :=
  instructionAt image pc = some (.base (.LD .x17 .x15 off)) ∧
  instructionAt image (pc+4) = some (.base (.SUB .x17 .x16 .x17)) ∧
  instructionAt image (pc+8) = some (.base (.SD .x15 .x17 off))

theorem patch_chunk_code (image : Image) (entry start : Word)
    (forward back : BitVec 21) (code : PatchCode image entry start forward back)
    (j : Fin 5) :
    ChunkCode image (start + BitVec.ofNat 64 (36 + 12*j.val))
      (BitVec.ofNat 12 (8*j.val)) := by
  have h0 := code.2 ⟨9 + 3*j.val, by have := j.isLt; omega⟩
  have h1 := code.2 ⟨10 + 3*j.val, by have := j.isLt; omega⟩
  have h2 := code.2 ⟨11 + 3*j.val, by have := j.isLt; omega⟩
  refine ⟨?_, ?_, ?_⟩
  · fin_cases j <;> simpa [patchInstructions, BitVec.add_assoc] using h0
  · fin_cases j <;> simpa [patchInstructions, BitVec.add_assoc] using h1
  · fin_cases j <;> simpa [patchInstructions, BitVec.add_assoc] using h2

theorem flipChunk_block (image : Image) (pc : Word) (off : BitVec 12)
    (code : ChunkCode image pc off) (s : MachineState) (atPC : s.pc = pc)
    (valid : accessValid (s.getReg .x15 + signExtend12 off) 8 = true) :
    OrdinarySteps image s 3 (flipChunk s off) := by
  rcases code with ⟨c0,c1,c2⟩
  let s1 := execInstrBr s (.LD .x17 .x15 off)
  let s2 := execInstrBr s1 (.SUB .x17 .x16 .x17)
  let s3 := execInstrBr s2 (.SD .x15 .x17 off)
  apply OrdinarySteps.step s s1 _ (.base (.LD .x17 .x15 off)) 2
  · simpa only [fetch_at, atPC] using c0
  · simp [s1, ordinaryStep, memoryArgumentsValid, execInstrBr, valid]
  apply OrdinarySteps.step s1 s2 _ (.base (.SUB .x17 .x16 .x17)) 1
  · have hp : s1.pc = pc+4 := by simp [s1, execInstrBr, atPC]
    simpa only [fetch_at, hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.SD .x15 .x17 off)) 0
  · have hp : s2.pc = pc+8 := by simp [s1,s2,execInstrBr,atPC,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c2
  · simp [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,valid,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

def flipTail (s : MachineState) (off : BitVec 12) : MachineState :=
  let s := execInstrBr s (.LBU .x17 .x15 off)
  let s := execInstrBr s (.XORI .x17 .x17 7)
  execInstrBr s (.SB .x15 .x17 off)

theorem flipTail_byte (s : MachineState) (off : BitVec 12) (a : Word) :
    (flipTail s off).getByte a =
      if a = s.getReg .x15 + signExtend12 off then
        s.getByte (s.getReg .x15 + signExtend12 off) ^^^ 7#8
      else s.getByte a := by
  simp [flipTail, execInstrBr, Signing.getByte_setByte,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    BitVec.truncate, BitVec.zeroExtend]
  rfl

theorem flipTail_regs (s : MachineState) (off : BitVec 12) :
    (flipTail s off).getReg .x15 = s.getReg .x15 ∧
    (flipTail s off).getReg .x16 = s.getReg .x16 ∧
    (flipTail s off).getReg .x12 = s.getReg .x12 ∧
    (flipTail s off).getReg .x10 = s.getReg .x10 ∧
    (flipTail s off).getReg .x2 = s.getReg .x2 := by
  simp [flipTail, execInstrBr, MachineState.setByte,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem flipTail_pc (s : MachineState) (off : BitVec 12) :
    (flipTail s off).pc = s.pc + 12 := by
  simp [flipTail, execInstrBr, BitVec.add_assoc]

def TailCode (image : Image) (pc : Word) (off : BitVec 12) : Prop :=
  instructionAt image pc = some (.base (.LBU .x17 .x15 off)) ∧
  instructionAt image (pc+4) = some (.base (.XORI .x17 .x17 7)) ∧
  instructionAt image (pc+8) = some (.base (.SB .x15 .x17 off))

theorem patch_tail_code (image : Image) (entry start : Word)
    (forward back : BitVec 21) (code : PatchCode image entry start forward back)
    (j : Fin 3) :
    TailCode image (start + BitVec.ofNat 64 (96 + 12*j.val))
      (BitVec.ofNat 12 (40+j.val)) := by
  have h0 := code.2 ⟨24 + 3*j.val, by have := j.isLt; omega⟩
  have h1 := code.2 ⟨25 + 3*j.val, by have := j.isLt; omega⟩
  have h2 := code.2 ⟨26 + 3*j.val, by have := j.isLt; omega⟩
  refine ⟨?_, ?_, ?_⟩
  · fin_cases j <;> simpa [patchInstructions, BitVec.add_assoc] using h0
  · fin_cases j <;> simpa [patchInstructions, BitVec.add_assoc] using h1
  · fin_cases j <;> simpa [patchInstructions, BitVec.add_assoc] using h2

theorem flipTail_block (image : Image) (pc : Word) (off : BitVec 12)
    (code : TailCode image pc off) (s : MachineState) (atPC : s.pc = pc)
    (valid : accessValid (s.getReg .x15 + signExtend12 off) 1 = true) :
    OrdinarySteps image s 3 (flipTail s off) := by
  rcases code with ⟨c0,c1,c2⟩
  let s1 := execInstrBr s (.LBU .x17 .x15 off)
  let s2 := execInstrBr s1 (.XORI .x17 .x17 7)
  let s3 := execInstrBr s2 (.SB .x15 .x17 off)
  apply OrdinarySteps.step s s1 _ (.base (.LBU .x17 .x15 off)) 2
  · simpa only [fetch_at, atPC] using c0
  · simp [s1, ordinaryStep, memoryArgumentsValid, execInstrBr, valid]
  apply OrdinarySteps.step s1 s2 _ (.base (.XORI .x17 .x17 7)) 1
  · have hp : s1.pc = pc+4 := by simp [s1, execInstrBr, atPC]
    simpa only [fetch_at, hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.SB .x15 .x17 off)) 0
  · have hp : s2.pc = pc+8 := by simp [s1,s2,execInstrBr,atPC,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c2
  · simp [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,valid,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

end SigGolfCandidate.Hypertree.Signing
