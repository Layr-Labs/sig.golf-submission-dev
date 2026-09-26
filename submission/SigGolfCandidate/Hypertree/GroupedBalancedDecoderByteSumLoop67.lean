import SigGolfCandidate.Execution
import SigGolfCandidate.Hypertree.GroupedBalancedDecoderByte67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteLoop67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteSumLoop67. -/
section
/-! One certified seven-instruction body of the byte-sum decoder loop. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteLoop67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByte67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def sumBody (s : MachineState) : MachineState :=
  let s1 := execInstrBr s (.LBU .x19 .x6 0)
  let s2 := execInstrBr s1 (.ADD .x20 .x17 .x19)
  let s3 := execInstrBr s2 (.LBU .x20 .x20 0)
  let s4 := execInstrBr s3 (.ADD .x14 .x14 .x20)
  let s5 := execInstrBr s4 (.ADDI .x6 .x6 1)
  let s6 := execInstrBr s5 (.ADDI .x18 .x18 (-1))
  execInstrBr s6 (.BNE .x18 .x0 (-24))

theorem sumBody_block (s : MachineState) (pc : s.pc = 0x1020)
    (validInput : accessValid (s.getReg .x6) 1 = true)
    (validTable : accessValid
      ((execInstrBr (execInstrBr s (.LBU .x19 .x6 0))
        (.ADD .x20 .x17 .x19)).getReg .x20) 1 = true) :
    OrdinarySteps image s 7 (sumBody s) := by
  let s1 := execInstrBr s (.LBU .x19 .x6 0)
  let s2 := execInstrBr s1 (.ADD .x20 .x17 .x19)
  let s3 := execInstrBr s2 (.LBU .x20 .x20 0)
  let s4 := execInstrBr s3 (.ADD .x14 .x14 .x20)
  let s5 := execInstrBr s4 (.ADDI .x6 .x6 1)
  let s6 := execInstrBr s5 (.ADDI .x18 .x18 (-1))
  let s7 := execInstrBr s6 (.BNE .x18 .x0 (-24))
  change OrdinarySteps image s 7 s7
  apply OrdinarySteps.step s s1 _ (.base (.LBU .x19 .x6 0)) 6
  · simp [fetch, pc, image, code, decodeInstruction]; rfl
  · simp [ordinaryStep, memoryArgumentsValid, signExtend12, validInput, s1]
  apply OrdinarySteps.step s1 s2 _ (.base (.ADD .x20 .x17 .x19)) 5
  · have hp : s1.pc = 0x1024 := by simp [s1, execInstrBr, pc]; rfl
    simp [fetch, hp, image, code, decodeInstruction]; rfl
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LBU .x20 .x20 0)) 4
  · have hp : s2.pc = 0x1028 := by simp [s1, s2, execInstrBr, pc]; rfl
    simp [fetch, hp, image, code, decodeInstruction]; rfl
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, signExtend12]
    exact validTable
  apply OrdinarySteps.step s3 s4 _ (.base (.ADD .x14 .x14 .x20)) 3
  · have hp : s3.pc = 0x102c := by simp [s1, s2, s3, execInstrBr, pc]; rfl
    simp [fetch, hp, image, code, decodeInstruction]; rfl
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x6 .x6 1)) 2
  · have hp : s4.pc = 0x1030 := by simp [s1, s2, s3, s4, execInstrBr, pc]; rfl
    simp [fetch, hp, image, code, decodeInstruction]; rfl
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x18 .x18 (-1))) 1
  · have hp : s5.pc = 0x1034 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]; rfl
    simp [fetch, hp, image, code, decodeInstruction]; rfl
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.BNE .x18 .x0 (-24))) 0
  · have hp : s6.pc = 0x1038 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc]; rfl
    simp [fetch, hp, image, code, decodeInstruction]; rfl
  · rfl
  exact OrdinarySteps.refl _

#print axioms sumBody_block

private theorem bne_preserves_reg (s : MachineState) (r : Reg) :
    (execInstrBr s (.BNE .x18 .x0 (-24))).getReg r = s.getReg r := by
  simp only [execInstrBr]
  split_ifs <;> simp only [MachineState.getReg_setPC]

theorem sumBody_input_pointer (s : MachineState) :
    (sumBody s).getReg .x6 = s.getReg .x6 + 1 := by
  unfold sumBody
  rw [bne_preserves_reg]
  simp [execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, signExtend12]

theorem sumBody_remaining (s : MachineState) :
    (sumBody s).getReg .x18 = s.getReg .x18 - 1 := by
  unfold sumBody
  rw [bne_preserves_reg]
  simp [execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, signExtend12, BitVec.sub_eq_add_neg]

theorem sumBody_total (s : MachineState) :
    (sumBody s).getReg .x14 = s.getReg .x14 + BitVec.setWidth 64
      (s.getByte (s.getReg .x17 + BitVec.setWidth 64 (s.getByte (s.getReg .x6)))) := by
  unfold sumBody
  rw [bne_preserves_reg]
  simp [execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, MachineState.getByte, MachineState.getMem_setReg,
    MachineState.getMem_setPC, signExtend12]

theorem sumBody_table_pointer (s : MachineState) :
    (sumBody s).getReg .x17 = s.getReg .x17 := by
  unfold sumBody
  rw [bne_preserves_reg]
  simp [execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, signExtend12]

#print axioms sumBody_input_pointer
#print axioms sumBody_remaining
#print axioms sumBody_total
#print axioms sumBody_table_pointer

private def beforeBranch (s : MachineState) : MachineState :=
  let s1 := execInstrBr s (.LBU .x19 .x6 0)
  let s2 := execInstrBr s1 (.ADD .x20 .x17 .x19)
  let s3 := execInstrBr s2 (.LBU .x20 .x20 0)
  let s4 := execInstrBr s3 (.ADD .x14 .x14 .x20)
  let s5 := execInstrBr s4 (.ADDI .x6 .x6 1)
  execInstrBr s5 (.ADDI .x18 .x18 (-1))

private theorem beforeBranch_pc (s : MachineState) :
    (beforeBranch s).pc = s.pc + 24 := by
  have lbu_pc (t : MachineState) (rd base : Reg) :
      (execInstrBr t (.LBU rd base 0)).pc = t.pc + 4 := rfl
  have add_pc (t : MachineState) (rd a b : Reg) :
      (execInstrBr t (.ADD rd a b)).pc = t.pc + 4 := rfl
  have addi_pc (t : MachineState) (rd a : Reg) (imm : BitVec 12) :
      (execInstrBr t (.ADDI rd a imm)).pc = t.pc + 4 := rfl
  simp only [beforeBranch, lbu_pc, add_pc, addi_pc]
  simp [BitVec.add_assoc]

private theorem beforeBranch_remaining (s : MachineState) :
    (beforeBranch s).getReg .x18 = s.getReg .x18 - 1 := by
  simp [beforeBranch, execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, signExtend12, BitVec.sub_eq_add_neg]

private theorem beforeBranch_x0 (s : MachineState) :
    (beforeBranch s).getReg .x0 = 0 := by
  rfl

theorem sumBody_pc (s : MachineState) :
    (sumBody s).pc = if s.getReg .x18 = 1 then s.pc + 28 else s.pc := by
  change (execInstrBr (beforeBranch s) (.BNE .x18 .x0 (-24))).pc = _
  simp only [execInstrBr, beforeBranch_pc, beforeBranch_remaining, beforeBranch_x0]
  have hzero (x : BitVec 64) : (x - 1 = 0) ↔ x = 1 := by
    simp only [← BitVec.toNat_inj, BitVec.toNat_sub,
      show (1 : BitVec 64).toNat = 1 by decide,
      show (0 : BitVec 64).toNat = 0 by decide]
    have hx := x.isLt
    omega
  by_cases hb : (s.getReg .x18 - 1 != 0) = true
  · have hn : s.getReg .x18 ≠ 1 := by
      intro h
      have hz := (hzero _).2 h
      have hne : s.getReg .x18 - 1 ≠ 0 := (bne_iff_ne).1 hb
      exact hne hz
    simp only [hb, ite_true, if_neg hn]
    simp [signExtend13, BitVec.add_assoc]
    rfl
  · have hz : s.getReg .x18 - 1 = 0 := by
      by_contra hc
      exact hb ((bne_iff_ne).2 hc)
    have h : s.getReg .x18 = 1 := (hzero _).1 hz
    simp only [hb, if_pos h]
    simp [BitVec.add_assoc]
    rfl

#print axioms sumBody_pc

private theorem lbu_byte (s : MachineState) (rd base : Reg) (a : Word) :
    (execInstrBr s (.LBU rd base 0)).getByte a = s.getByte a := by
  simp [MachineState.getByte, execInstrBr, MachineState.getMem_setReg,
    MachineState.getMem_setPC]

private theorem add_byte (s : MachineState) (rd x y : Reg) (a : Word) :
    (execInstrBr s (.ADD rd x y)).getByte a = s.getByte a := by
  simp [MachineState.getByte, execInstrBr, MachineState.getMem_setReg,
    MachineState.getMem_setPC]

private theorem addi_byte (s : MachineState) (rd x : Reg) (i : BitVec 12) (a : Word) :
    (execInstrBr s (.ADDI rd x i)).getByte a = s.getByte a := by
  simp [MachineState.getByte, execInstrBr, MachineState.getMem_setReg,
    MachineState.getMem_setPC]

private theorem bne_byte (s : MachineState) (x y : Reg) (i : BitVec 13) (a : Word) :
    (execInstrBr s (.BNE x y i)).getByte a = s.getByte a := by
  simp only [MachineState.getByte, execInstrBr]
  split_ifs <;> simp only [MachineState.getMem_setPC]

theorem sumBody_byte (s : MachineState) (a : Word) :
    (sumBody s).getByte a = s.getByte a := by
  simp only [sumBody, bne_byte, addi_byte, add_byte, lbu_byte]

#print axioms sumBody_byte

end SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteLoop67

end

open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByte67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteSumLoop67

def sumLoop (s : MachineState) : Nat → MachineState
| 0 => s
| n+1 => sumBody (sumLoop s n)

theorem sumLoop_remaining (s : MachineState) (n : Nat) :
    (sumLoop s n).getReg .x18 = s.getReg .x18 - BitVec.ofNat 64 n := by
  induction n with
  | zero => simp [sumLoop]
  | succ n ih =>
    simp only [sumLoop, sumBody_remaining, ih]
    rw [BitVec.sub_sub, BitVec.ofNat_add]
    rfl

theorem sumLoop_input_pointer (s : MachineState) (n : Nat) :
    (sumLoop s n).getReg .x6 = s.getReg .x6 + BitVec.ofNat 64 n := by
  induction n with
  | zero => simp [sumLoop]
  | succ n ih =>
    simp only [sumLoop, sumBody_input_pointer, ih]
    simp [BitVec.ofNat_add, BitVec.add_assoc]

theorem sumLoop_table_pointer (s : MachineState) (n : Nat) :
    (sumLoop s n).getReg .x17 = s.getReg .x17 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [sumLoop, sumBody_table_pointer] using ih

theorem sumLoop_byte (s : MachineState) (n : Nat) (a : Word) :
    (sumLoop s n).getByte a = s.getByte a := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [sumLoop, sumBody_byte] using ih

def tableByte (s : MachineState) (n : Nat) : Word :=
  BitVec.setWidth 64
    (s.getByte (s.getReg .x17 + BitVec.setWidth 64
      (s.getByte (s.getReg .x6 + BitVec.ofNat 64 n))))

def tableTotal (s : MachineState) : Nat → Word
| 0 => 0
| n+1 => tableTotal s n + tableByte s n

theorem sumLoop_total (s : MachineState) (n : Nat) :
    (sumLoop s n).getReg .x14 = s.getReg .x14 + tableTotal s n := by
  induction n with
  | zero => simp [sumLoop, tableTotal]
  | succ n ih =>
    simp only [sumLoop, sumBody_total, ih, tableTotal, tableByte]
    rw [sumLoop_table_pointer, sumLoop_input_pointer]
    rw [sumLoop_byte, sumLoop_byte]
    simp [BitVec.add_assoc]

theorem remaining_ne_one (n : Nat) (hn : n < 15) :
    (BitVec.ofNat 64 16 - BitVec.ofNat 64 n) ≠ 1 := by
  intro h
  have hnat := congrArg BitVec.toNat h
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at hnat
  simp only [show n % 2 ^ 64 = n from Nat.mod_eq_of_lt (by omega),
    show 16 % 2 ^ 64 = 16 by decide,
    show (1 : BitVec 64).toNat = 1 by decide] at hnat
  omega

theorem sumLoop_pc (s : MachineState) (pc : s.pc = 0x1020)
    (rem : s.getReg .x18 = 16) (n : Nat) (hn : n < 16) :
    (sumLoop s n).pc = 0x1020 := by
  induction n with
  | zero => simpa [sumLoop] using pc
  | succ n ih =>
    have hn0 : n < 16 := by omega
    have hn1 : n < 15 := by omega
    have hprev := ih hn0
    simp only [sumLoop, sumBody_pc]
    rw [sumLoop_remaining, rem]
    split_ifs with h
    · exact False.elim ((remaining_ne_one n hn1) h)
    · exact hprev

theorem sumLoop_exit_pc (s : MachineState) (pc : s.pc = 0x1020)
    (rem : s.getReg .x18 = 16) :
    (sumLoop s 16).pc = 0x103c := by
  have hlast : (sumLoop s 15).getReg .x18 = 1 := by
    rw [sumLoop_remaining, rem]
    decide
  change (sumBody (sumLoop s 15)).pc = 0x103c
  rw [sumBody_pc, hlast]
  simp only [ite_true]
  rw [sumLoop_pc s pc rem 15 (by decide)]
  decide

theorem sumLoop_pc_same (s : MachineState)
    (rem : s.getReg .x18 = 16) (n : Nat) (hn : n < 16) :
    (sumLoop s n).pc = s.pc := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn0 : n < 16 := by omega
    have hn1 : n < 15 := by omega
    have hprev := ih hn0
    simp only [sumLoop, sumBody_pc]
    rw [sumLoop_remaining, rem]
    split_ifs with h
    · exact False.elim ((remaining_ne_one n hn1) h)
    · exact hprev

theorem sumLoop_exit_pc_add (s : MachineState) (rem : s.getReg .x18 = 16) :
    (sumLoop s 16).pc = s.pc + 28 := by
  have hlast : (sumLoop s 15).getReg .x18 = 1 := by
    rw [sumLoop_remaining, rem]
    decide
  change (sumBody (sumLoop s 15)).pc = s.pc + 28
  rw [sumBody_pc, hlast]
  simp only [ite_true]
  rw [sumLoop_pc_same s rem 15 (by decide)]

theorem body_table_address (s : MachineState) :
    (execInstrBr (execInstrBr s (.LBU .x19 .x6 0))
      (.ADD .x20 .x17 .x19)).getReg .x20 =
      s.getReg .x17 + BitVec.setWidth 64 (s.getByte (s.getReg .x6)) := by
  simp [execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, signExtend12]

theorem valid_table_address (s : MachineState)
    (hbase : s.getReg .x17 = 0xfff700) :
    accessValid (s.getReg .x17 + BitVec.setWidth 64
      (s.getByte (s.getReg .x6))) 1 = true := by
  rw [hbase]
  simp only [accessValid, rangeValid, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · simp only [BitVec.toNat_add, BitVec.toNat_setWidth]
    have hb := (s.getByte (s.getReg .x6)).isLt
    simp only [show (0xfff700 : Word).toNat = 0xfff700 by decide,
      show (s.getByte (s.getReg .x6)).toNat % 2 ^ 64 =
        (s.getByte (s.getReg .x6)).toNat from Nat.mod_eq_of_lt (by omega),
      MEMORY_BYTES]
    omega
  · simp [Nat.mod_one]

theorem valid_input_address (s : MachineState) (n : Nat) (hn : n < 16)
    (hbase : s.getReg .x6 = 0x80500) :
    accessValid (s.getReg .x6 + BitVec.ofNat 64 n) 1 = true := by
  rw [hbase]
  simp only [accessValid, rangeValid, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [show (0x80500 : Word).toNat = 0x80500 by decide,
      show n % 2 ^ 64 = n from Nat.mod_eq_of_lt (by omega),
      MEMORY_BYTES]
    omega
  · simp [Nat.mod_one]

theorem steps_comp {image : Image} {s t u : MachineState} {n m : Nat}
    (a : OrdinarySteps image s n t) (b : OrdinarySteps image t m u) :
    OrdinarySteps image s (n+m) u := by
  induction a with
  | refl => simpa using b
  | step s t final instruction steps hf hs tail ih =>
    simpa [Nat.succ_add] using OrdinarySteps.step s t u instruction (steps+m) hf hs (ih b)

theorem sumLoop_steps (s : MachineState)
    (pc : s.pc = 0x1020) (rem : s.getReg .x18 = 16)
    (input : s.getReg .x6 = 0x80500) (table : s.getReg .x17 = 0xfff700)
    (n : Nat) (hn : n ≤ 16) :
    OrdinarySteps SigGolfCandidate.Hypertree.GroupedBalancedDecoderByte67.image s (7*n) (sumLoop s n) := by
  induction n with
  | zero => simpa [sumLoop] using OrdinarySteps.refl (image := SigGolfCandidate.Hypertree.GroupedBalancedDecoderByte67.image) s
  | succ n ih =>
    have hn0 : n ≤ 16 := by omega
    have hn1 : n < 16 := by omega
    have initial := ih hn0
    have hpc := sumLoop_pc s pc rem n hn1
    have hinput : accessValid ((sumLoop s n).getReg .x6) 1 = true := by
      rw [sumLoop_input_pointer]
      exact valid_input_address s n hn1 input
    have htable : accessValid
        ((execInstrBr (execInstrBr (sumLoop s n) (.LBU .x19 .x6 0))
          (.ADD .x20 .x17 .x19)).getReg .x20) 1 = true := by
      rw [body_table_address]
      exact valid_table_address (sumLoop s n) (by rw [sumLoop_table_pointer]; exact table)
    have one := sumBody_block (sumLoop s n) hpc hinput htable
    have both := steps_comp initial one
    simpa only [sumLoop, Nat.mul_succ, Nat.add_comm] using both

#print axioms sumLoop_steps
#print axioms sumLoop_total
#print axioms sumLoop_exit_pc

end SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteSumLoop67
