import SigGolfCandidate.Hypertree.GroupedBalancedSignByteLoop67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopy67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopyLoop67. -/
section
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopy67

def copyBody (s : MachineState) : MachineState :=
  let s1 := execInstrBr s (.LBU .x19 .x10 0)
  let s2 := execInstrBr s1 (.SLLI .x20 .x19 2)
  let s3 := execInstrBr s2 (.ADD .x21 .x17 .x20)
  let s4 := execInstrBr s3 (.LW .x22 .x21 0)
  let s5 := execInstrBr s4 (.SW .x11 .x22 0)
  let s6 := execInstrBr s5 (.ADDI .x10 .x10 1)
  let s7 := execInstrBr s6 (.ADDI .x11 .x11 4)
  let s8 := execInstrBr s7 (.ADDI .x18 .x18 (-1))
  execInstrBr s8 (.BNE .x18 .x0 (-32))
private theorem word1114 : GroupedBalancedSignImage67Byte.code[1114]? = some 0x00054983 := by decide
private theorem word1115 : GroupedBalancedSignImage67Byte.code[1115]? = some 0x00299a13 := by decide
private theorem word1116 : GroupedBalancedSignImage67Byte.code[1116]? = some 0x01488ab3 := by decide
private theorem word1117 : GroupedBalancedSignImage67Byte.code[1117]? = some 0x000aab03 := by decide
private theorem word1118 : GroupedBalancedSignImage67Byte.code[1118]? = some 0x0165a023 := by decide
private theorem word1119 : GroupedBalancedSignImage67Byte.code[1119]? = some 0x00150513 := by decide
private theorem word1120 : GroupedBalancedSignImage67Byte.code[1120]? = some 0x00458593 := by decide
private theorem word1121 : GroupedBalancedSignImage67Byte.code[1121]? = some 0xfff90913 := by decide
private theorem word1122 : GroupedBalancedSignImage67Byte.code[1122]? = some 0xfe0910e3 := by decide

theorem copyBody_block (s : MachineState) (pc : s.pc = 0x2168)
    (validInput : accessValid (s.getReg .x10) 1 = true)
    (validTable : accessValid
      ((execInstrBr (execInstrBr (execInstrBr s (.LBU .x19 .x10 0))
        (.SLLI .x20 .x19 2)) (.ADD .x21 .x17 .x20)).getReg .x21) 4 = true)
    (validOutput : accessValid (s.getReg .x11) 4 = true) :
    OrdinarySteps GroupedBalancedSignImage67Byte.image s 9 (copyBody s) := by
  let s1 := execInstrBr s (.LBU .x19 .x10 0)
  let s2 := execInstrBr s1 (.SLLI .x20 .x19 2)
  let s3 := execInstrBr s2 (.ADD .x21 .x17 .x20)
  let s4 := execInstrBr s3 (.LW .x22 .x21 0)
  let s5 := execInstrBr s4 (.SW .x11 .x22 0)
  let s6 := execInstrBr s5 (.ADDI .x10 .x10 1)
  let s7 := execInstrBr s6 (.ADDI .x11 .x11 4)
  let s8 := execInstrBr s7 (.ADDI .x18 .x18 (-1))
  let s9 := execInstrBr s8 (.BNE .x18 .x0 (-32))
  change OrdinarySteps GroupedBalancedSignImage67Byte.image s 9 s9
  apply OrdinarySteps.step s s1 _ (.base (.LBU .x19 .x10 0)) 8
  · simp [fetch, pc, GroupedBalancedSignImage67Byte.image, word1114]; rfl
  · simp [ordinaryStep, memoryArgumentsValid, signExtend12, validInput, s1]
  apply OrdinarySteps.step s1 s2 _ (.base (.SLLI .x20 .x19 2)) 7
  · have hp : s1.pc = 0x216c := by simp [s1, execInstrBr, pc]; rfl
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1115]; rfl
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADD .x21 .x17 .x20)) 6
  · have hp : s2.pc = 0x2170 := by simp [s1, s2, execInstrBr, pc]; rfl
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1116]; rfl
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LW .x22 .x21 0)) 5
  · have hp : s3.pc = 0x2174 := by simp [s1, s2, s3, execInstrBr, pc]; rfl
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1117]; rfl
  · simp [s1,s2,s3,s4,ordinaryStep,memoryArgumentsValid,signExtend12]
    exact validTable
  apply OrdinarySteps.step s4 s5 _ (.base (.SW .x11 .x22 0)) 4
  · have hp : s4.pc = 0x2178 := by simp [s1, s2, s3, s4, execInstrBr, pc]; rfl
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1118]; rfl
  · simp [s1,s2,s3,s4,s5,ordinaryStep,memoryArgumentsValid,signExtend12]
    exact validOutput
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x10 .x10 1)) 3
  · have hp : s5.pc = 0x217c := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]; rfl
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1119]; rfl
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x11 .x11 4)) 2
  · have hp : s6.pc = 0x2180 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc]; rfl
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1120]; rfl
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x18 .x18 (-1))) 1
  · have hp : s7.pc = 0x2184 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc]; rfl
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1121]; rfl
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.BNE .x18 .x0 (-32))) 0
  · have hp : s8.pc = 0x2188 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc]; rfl
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1122]; rfl
  · rfl
  exact OrdinarySteps.refl _

private theorem getReg_setWord32 (s : MachineState) (a : Word) (v : BitVec 32)
    (r : Reg) : (s.setWord32 a v).getReg r = s.getReg r := by
  simp [MachineState.setWord32, MachineState.setMem]
  cases r <;> rfl

private theorem copy_bne_preserves_reg (s : MachineState) (r : Reg) :
    (execInstrBr s (.BNE .x18 .x0 (-32))).getReg r = s.getReg r := by
  simp only [execInstrBr]
  split_ifs <;> simp only [MachineState.getReg_setPC]

theorem copyBody_input_pointer (s : MachineState) :
    (copyBody s).getReg .x10 = s.getReg .x10 + 1 := by
  unfold copyBody
  rw [copy_bne_preserves_reg]
  simp [execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, getReg_setWord32, signExtend12]

theorem copyBody_output_pointer (s : MachineState) :
    (copyBody s).getReg .x11 = s.getReg .x11 + 4 := by
  unfold copyBody
  rw [copy_bne_preserves_reg]
  simp [execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, getReg_setWord32, signExtend12]

theorem copyBody_remaining (s : MachineState) :
    (copyBody s).getReg .x18 = s.getReg .x18 - 1 := by
  unfold copyBody
  rw [copy_bne_preserves_reg]
  simp [execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, getReg_setWord32, signExtend12, BitVec.sub_eq_add_neg]

theorem copyBody_table_pointer (s : MachineState) :
    (copyBody s).getReg .x17 = s.getReg .x17 := by
  unfold copyBody
  rw [copy_bne_preserves_reg]
  simp [execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, getReg_setWord32, signExtend12]

private def beforeCopyBranch (s : MachineState) : MachineState :=
  let s1 := execInstrBr s (.LBU .x19 .x10 0)
  let s2 := execInstrBr s1 (.SLLI .x20 .x19 2)
  let s3 := execInstrBr s2 (.ADD .x21 .x17 .x20)
  let s4 := execInstrBr s3 (.LW .x22 .x21 0)
  let s5 := execInstrBr s4 (.SW .x11 .x22 0)
  let s6 := execInstrBr s5 (.ADDI .x10 .x10 1)
  let s7 := execInstrBr s6 (.ADDI .x11 .x11 4)
  execInstrBr s7 (.ADDI .x18 .x18 (-1))

private theorem beforeCopyBranch_pc (s : MachineState) :
    (beforeCopyBranch s).pc = s.pc + 32 := by
  have lbu_pc (t : MachineState) (rd base : Reg) :
      (execInstrBr t (.LBU rd base 0)).pc = t.pc + 4 := rfl
  have slli_pc (t : MachineState) (rd base : Reg) (n : BitVec 6) :
      (execInstrBr t (.SLLI rd base n)).pc = t.pc + 4 := rfl
  have add_pc (t : MachineState) (rd a b : Reg) :
      (execInstrBr t (.ADD rd a b)).pc = t.pc + 4 := rfl
  have lw_pc (t : MachineState) (rd base : Reg) :
      (execInstrBr t (.LW rd base 0)).pc = t.pc + 4 := rfl
  have sw_pc (t : MachineState) (base value : Reg) :
      (execInstrBr t (.SW base value 0)).pc = t.pc + 4 := rfl
  have addi_pc (t : MachineState) (rd a : Reg) (imm : BitVec 12) :
      (execInstrBr t (.ADDI rd a imm)).pc = t.pc + 4 := rfl
  simp only [beforeCopyBranch, lbu_pc, slli_pc, add_pc, lw_pc, sw_pc, addi_pc]
  simp [BitVec.add_assoc]

private theorem beforeCopyBranch_remaining (s : MachineState) :
    (beforeCopyBranch s).getReg .x18 = s.getReg .x18 - 1 := by
  simp [beforeCopyBranch, execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, getReg_setWord32, signExtend12, BitVec.sub_eq_add_neg]

private theorem beforeCopyBranch_x0 (s : MachineState) :
    (beforeCopyBranch s).getReg .x0 = 0 := by
  rfl

theorem copyBody_pc (s : MachineState) :
    (copyBody s).pc = if s.getReg .x18 = 1 then s.pc + 36 else s.pc := by
  change (execInstrBr (beforeCopyBranch s) (.BNE .x18 .x0 (-32))).pc = _
  simp only [execInstrBr, beforeCopyBranch_pc, beforeCopyBranch_remaining,
    beforeCopyBranch_x0]
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

#print axioms copyBody_block
#print axioms copyBody_pc
#print axioms copyBody_input_pointer
#print axioms copyBody_output_pointer

end SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopy67

end

open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopy67
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteSumLoop67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopyLoop67

def copyLoop (s : MachineState) : Nat → MachineState
| 0 => s
| n+1 => copyBody (copyLoop s n)

theorem copyLoop_input_pointer (s : MachineState) (n : Nat) :
    (copyLoop s n).getReg .x10 = s.getReg .x10 + BitVec.ofNat 64 n := by
  induction n with
  | zero => simp [copyLoop]
  | succ n ih =>
    simp only [copyLoop, copyBody_input_pointer, ih]
    simp [BitVec.ofNat_add, BitVec.add_assoc]

theorem copyLoop_output_pointer (s : MachineState) (n : Nat) :
    (copyLoop s n).getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 (4*n) := by
  induction n with
  | zero => simp [copyLoop]
  | succ n ih =>
    simp only [copyLoop, copyBody_output_pointer, ih]
    simp [Nat.mul_succ, BitVec.ofNat_add, BitVec.add_assoc]

theorem copyLoop_remaining (s : MachineState) (n : Nat) :
    (copyLoop s n).getReg .x18 = s.getReg .x18 - BitVec.ofNat 64 n := by
  induction n with
  | zero => simp [copyLoop]
  | succ n ih =>
    simp only [copyLoop, copyBody_remaining, ih]
    rw [BitVec.sub_sub, BitVec.ofNat_add]
    rfl

theorem copyLoop_table_pointer (s : MachineState) (n : Nat) :
    (copyLoop s n).getReg .x17 = s.getReg .x17 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [copyLoop, copyBody_table_pointer] using ih

theorem copyLoop_pc_same (s : MachineState)
    (rem : s.getReg .x18 = 16) (n : Nat) (hn : n < 16) :
    (copyLoop s n).pc = s.pc := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn0 : n < 16 := by omega
    have hn1 : n < 15 := by omega
    have hprev := ih hn0
    simp only [copyLoop, copyBody_pc]
    rw [copyLoop_remaining, rem]
    split_ifs with h
    · exact False.elim ((remaining_ne_one n hn1) h)
    · exact hprev

theorem copyLoop_exit_pc_add (s : MachineState) (rem : s.getReg .x18 = 16) :
    (copyLoop s 16).pc = s.pc + 36 := by
  have hlast : (copyLoop s 15).getReg .x18 = 1 := by
    rw [copyLoop_remaining, rem]
    decide
  change (copyBody (copyLoop s 15)).pc = s.pc + 36
  rw [copyBody_pc, hlast]
  simp only [ite_true]
  rw [copyLoop_pc_same s rem 15 (by decide)]

theorem copy_body_table_address (s : MachineState) :
    (execInstrBr (execInstrBr (execInstrBr s (.LBU .x19 .x10 0))
      (.SLLI .x20 .x19 2)) (.ADD .x21 .x17 .x20)).getReg .x21 =
      s.getReg .x17 + BitVec.setWidth 64 (s.getByte (s.getReg .x10)) <<< 2 := by
  simp [execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, signExtend12]

private theorem valid_copy_table_base (base : Word)
    (hb : base = 0xfff800 ∨ base = 0xfffc00) (v : BitVec 8) :
    accessValid (base + (BitVec.setWidth 64 v <<< 2)) 4 = true := by
  rcases hb with hb | hb <;> subst base
  · simp only [accessValid, rangeValid, decide_eq_true_eq, Bool.and_eq_true]
    constructor
    · simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft,
        BitVec.toNat_setWidth, Nat.shiftLeft_eq]
      have hv := v.isLt
      simp only [show (0xfff800 : Word).toNat = 0xfff800 by decide,
        show v.toNat % 2 ^ 64 = v.toNat from Nat.mod_eq_of_lt (by omega),
        MEMORY_BYTES]
      omega
    · simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft,
        BitVec.toNat_setWidth, Nat.shiftLeft_eq]
      have hv := v.isLt
      simp only [show (0xfff800 : Word).toNat = 0xfff800 by decide,
        show v.toNat % 2 ^ 64 = v.toNat from Nat.mod_eq_of_lt (by omega)]
      omega
  · simp only [accessValid, rangeValid, decide_eq_true_eq, Bool.and_eq_true]
    constructor
    · simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft,
        BitVec.toNat_setWidth, Nat.shiftLeft_eq]
      have hv := v.isLt
      simp only [show (0xfffc00 : Word).toNat = 0xfffc00 by decide,
        show v.toNat % 2 ^ 64 = v.toNat from Nat.mod_eq_of_lt (by omega),
        MEMORY_BYTES]
      omega
    · simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft,
        BitVec.toNat_setWidth, Nat.shiftLeft_eq]
      have hv := v.isLt
      simp only [show (0xfffc00 : Word).toNat = 0xfffc00 by decide,
        show v.toNat % 2 ^ 64 = v.toNat from Nat.mod_eq_of_lt (by omega)]
      omega

private theorem valid_copy_input_address (s : MachineState) (n : Nat) (hn : n < 16)
    (hbase : s.getReg .x10 = 0x80500) :
    accessValid (s.getReg .x10 + BitVec.ofNat 64 n) 1 = true := by
  rw [hbase]
  simp only [accessValid, rangeValid, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [show (0x80500 : Word).toNat = 0x80500 by decide,
      show n % 2 ^ 64 = n from Nat.mod_eq_of_lt (by omega), MEMORY_BYTES]
    omega
  · simp [Nat.mod_one]

private theorem valid_copy_output_address (s : MachineState) (n : Nat) (hn : n < 16)
    (hbase : s.getReg .x11 = 0x80600) :
    accessValid (s.getReg .x11 + BitVec.ofNat 64 (4*n)) 4 = true := by
  rw [hbase]
  simp only [accessValid, rangeValid, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [show (0x80600 : Word).toNat = 0x80600 by decide,
      show 4*n % 2 ^ 64 = 4*n from Nat.mod_eq_of_lt (by omega), MEMORY_BYTES]
    omega
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [show (0x80600 : Word).toNat = 0x80600 by decide,
      show 4*n % 2 ^ 64 = 4*n from Nat.mod_eq_of_lt (by omega)]
    omega

theorem copyLoop_steps (s : MachineState)
    (pc : s.pc = 0x2168) (rem : s.getReg .x18 = 16)
    (input : s.getReg .x10 = 0x80500) (output : s.getReg .x11 = 0x80600)
    (table : s.getReg .x17 = 0xfff800 ∨ s.getReg .x17 = 0xfffc00)
    (n : Nat) (hn : n ≤ 16) :
    OrdinarySteps GroupedBalancedSignImage67Byte.image s (9*n) (copyLoop s n) := by
  induction n with
  | zero => simpa [copyLoop] using OrdinarySteps.refl (image := GroupedBalancedSignImage67Byte.image) s
  | succ n ih =>
    have hn0 : n ≤ 16 := by omega
    have hn1 : n < 16 := by omega
    have initial := ih hn0
    have hpc : (copyLoop s n).pc = 0x2168 := by
      rw [copyLoop_pc_same s rem n hn1, pc]
    have hinput : accessValid ((copyLoop s n).getReg .x10) 1 = true := by
      rw [copyLoop_input_pointer]
      exact valid_copy_input_address s n hn1 input
    have htable : accessValid
        ((execInstrBr (execInstrBr (execInstrBr (copyLoop s n) (.LBU .x19 .x10 0))
          (.SLLI .x20 .x19 2)) (.ADD .x21 .x17 .x20)).getReg .x21) 4 = true := by
      rw [copy_body_table_address]
      have ht : (copyLoop s n).getReg .x17 = 0xfff800 ∨
          (copyLoop s n).getReg .x17 = 0xfffc00 := by
        rw [copyLoop_table_pointer]
        exact table
      exact valid_copy_table_base _ ht _
    have houtput : accessValid ((copyLoop s n).getReg .x11) 4 = true := by
      rw [copyLoop_output_pointer]
      exact valid_copy_output_address s n hn1 output
    have one := copyBody_block (copyLoop s n) hpc hinput htable houtput
    have both := steps_comp initial one
    simpa only [copyLoop, Nat.mul_succ, Nat.add_comm] using both

theorem copyLoop_interface_control (s : MachineState)
    (pc : s.pc = 0x2168) (rem : s.getReg .x18 = 16)
    (input : s.getReg .x10 = 0x80500) (output : s.getReg .x11 = 0x80600)
    (table : s.getReg .x17 = 0xfff800 ∨ s.getReg .x17 = 0xfffc00) :
    OrdinarySteps GroupedBalancedSignImage67Byte.image
      s 144 (copyLoop s 16) ∧
    (copyLoop s 16).pc = 0x218c ∧
    (copyLoop s 16).getReg .x10 = 0x80510 ∧
    (copyLoop s 16).getReg .x11 = 0x80640 ∧
    (copyLoop s 16).getReg .x18 = 0 ∧
    (copyLoop s 16).getReg .x17 = s.getReg .x17 := by
  constructor
  · simpa using copyLoop_steps s pc rem input output table 16 (by decide)
  constructor
  · rw [copyLoop_exit_pc_add s rem, pc]
    decide
  constructor
  · rw [copyLoop_input_pointer, input]
    decide
  constructor
  · rw [copyLoop_output_pointer, output]
    decide
  constructor
  · rw [copyLoop_remaining, rem]
    decide
  · exact copyLoop_table_pointer s 16

#print axioms copyLoop_steps
#print axioms copyLoop_interface_control

end SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopyLoop67
