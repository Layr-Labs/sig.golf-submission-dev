import SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteSumLoop67
import SigGolfCandidate.Hypertree.GroupedBalancedSignImage67Byte
import SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteInterface67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteSumLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteInterface67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteLoop67
private theorem word1094 : GroupedBalancedSignImage67Byte.code[1094]? =
    some 0x00034983 := by decide
private theorem word1095 : GroupedBalancedSignImage67Byte.code[1095]? =
    some 0x01388a33 := by decide
private theorem word1096 : GroupedBalancedSignImage67Byte.code[1096]? =
    some 0x000a4a03 := by decide
private theorem word1097 : GroupedBalancedSignImage67Byte.code[1097]? =
    some 0x01470733 := by decide
private theorem word1098 : GroupedBalancedSignImage67Byte.code[1098]? =
    some 0x00130313 := by decide
private theorem word1099 : GroupedBalancedSignImage67Byte.code[1099]? =
    some 0xfff90913 := by decide
private theorem word1100 : GroupedBalancedSignImage67Byte.code[1100]? =
    some 0xfe0914e3 := by decide

theorem sumBody_block_fast (s : MachineState) (pc : s.pc = 0x2118)
    (validInput : accessValid (s.getReg .x6) 1 = true)
    (validTable : accessValid
      ((execInstrBr (execInstrBr s (.LBU .x19 .x6 0))
        (.ADD .x20 .x17 .x19)).getReg .x20) 1 = true) :
    OrdinarySteps GroupedBalancedSignImage67Byte.image s 7 (sumBody s) := by
  let s1 := execInstrBr s (.LBU .x19 .x6 0)
  let s2 := execInstrBr s1 (.ADD .x20 .x17 .x19)
  let s3 := execInstrBr s2 (.LBU .x20 .x20 0)
  let s4 := execInstrBr s3 (.ADD .x14 .x14 .x20)
  let s5 := execInstrBr s4 (.ADDI .x6 .x6 1)
  let s6 := execInstrBr s5 (.ADDI .x18 .x18 (-1))
  let s7 := execInstrBr s6 (.BNE .x18 .x0 (-24))
  change OrdinarySteps GroupedBalancedSignImage67Byte.image s 7 s7
  apply OrdinarySteps.step s s1 _ (.base (.LBU .x19 .x6 0)) 6
  · simp [fetch, pc, GroupedBalancedSignImage67Byte.image, word1094]; rfl
  · simp [ordinaryStep, memoryArgumentsValid, signExtend12, validInput, s1]
  apply OrdinarySteps.step s1 s2 _ (.base (.ADD .x20 .x17 .x19)) 5
  · have hp : s1.pc = 0x211c := by simp [s1, execInstrBr, pc]; rfl
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1095]; rfl
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LBU .x20 .x20 0)) 4
  · have hp : s2.pc = 0x2120 := by simp [s1, s2, execInstrBr, pc]; rfl
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1096]; rfl
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, signExtend12]
    exact validTable
  apply OrdinarySteps.step s3 s4 _ (.base (.ADD .x14 .x14 .x20)) 3
  · have hp : s3.pc = 0x2124 := by simp [s1, s2, s3, execInstrBr, pc]; rfl
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1097]; rfl
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x6 .x6 1)) 2
  · have hp : s4.pc = 0x2128 := by simp [s1, s2, s3, s4, execInstrBr, pc]; rfl
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1098]; rfl
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x18 .x18 (-1))) 1
  · have hp : s5.pc = 0x212c := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]; rfl
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1099]; rfl
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.BNE .x18 .x0 (-24))) 0
  · have hp : s6.pc = 0x2130 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc]; rfl
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1100]; rfl
  · rfl
  exact OrdinarySteps.refl _


theorem sumLoop_steps_fast (s : MachineState)
    (pc : s.pc = 0x2118) (rem : s.getReg .x18 = 16)
    (input : s.getReg .x6 = 0x80500) (table : s.getReg .x17 = 0xfff700)
    (n : Nat) (hn : n ≤ 16) :
    OrdinarySteps GroupedBalancedSignImage67Byte.image s (7*n) (sumLoop s n) := by
  induction n with
  | zero => simpa [sumLoop] using OrdinarySteps.refl (image := GroupedBalancedSignImage67Byte.image) s
  | succ n ih =>
    have hn0 : n ≤ 16 := by omega
    have hn1 : n < 16 := by omega
    have initial := ih hn0
    have hpc : (sumLoop s n).pc = 0x2118 := by
      rw [sumLoop_pc_same s rem n hn1, pc]
    have hinput : accessValid ((sumLoop s n).getReg .x6) 1 = true := by
      rw [sumLoop_input_pointer]
      exact valid_input_address s n hn1 input
    have htable : accessValid
        ((execInstrBr (execInstrBr (sumLoop s n) (.LBU .x19 .x6 0))
          (.ADD .x20 .x17 .x19)).getReg .x20) 1 = true := by
      rw [body_table_address]
      exact valid_table_address (sumLoop s n) (by rw [sumLoop_table_pointer]; exact table)
    have one := sumBody_block_fast (sumLoop s n) hpc hinput htable
    have both := steps_comp initial one
    simpa only [sumLoop, Nat.mul_succ, Nat.add_comm] using both


theorem sumLoop_interface_fast (s : MachineState) (message : BitVec 128)
    (pc : s.pc = 0x2118) (rem : s.getReg .x18 = 16)
    (input : s.getReg .x6 = 0x80500) (table : s.getReg .x17 = 0xfff700)
    (total : s.getReg .x14 = 0)
    (hmsg : ∀ j : Fin 16, s.getByte
      (s.getReg .x6 + BitVec.ofNat 64 j.val) = message.extractLsb' (8*j.val) 8)
    (htable : ∀ entry : Fin 256, s.getByte
      (s.getReg .x17 + BitVec.ofNat 64 entry.val) =
        BitVec.ofNat 8 (GroupedBalancedDecoderByte67.byteSum entry.val)) :
    OrdinarySteps GroupedBalancedSignImage67Byte.image
      s 112 (sumLoop s 16) ∧
    (sumLoop s 16).pc = 0x2134 ∧
    (sumLoop s 16).getReg .x14 =
      BitVec.ofNat 64 (GroupedBalancedQuaternary.rawSum message) := by
  constructor
  · simpa using sumLoop_steps_fast s pc rem input table 16 (by decide)
  constructor
  · rw [sumLoop_exit_pc_add s rem, pc]
    decide
  · rw [sumLoop_total, total, tableTotal_eq_rawSum s message hmsg htable]
    simp

#print axioms sumLoop_steps_fast
#print axioms sumLoop_interface_fast

end SigGolfCandidate.Hypertree.GroupedBalancedSignByteLoop67
