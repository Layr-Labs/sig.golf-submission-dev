import SigGolfCandidate.Hypertree.GroupedBalancedSignByteBranch67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteBranch67
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteSumLoop67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteBranchSteps67

private theorem word1110 : GroupedBalancedSignImage67Byte.code[1110]? =
    some 0x10010893 := by decide
private theorem word1111 : GroupedBalancedSignImage67Byte.code[1111]? =
    some 0x00a81a13 := by decide
private theorem word1112 : GroupedBalancedSignImage67Byte.code[1112]? =
    some 0x014888b3 := by decide
private theorem word1113 : GroupedBalancedSignImage67Byte.code[1113]? =
    some 0x01000913 := by decide

theorem commonBranch_steps (s : MachineState) (pc : s.pc = 0x2158) :
    OrdinarySteps GroupedBalancedSignImage67Byte.image s 4 (commonBranch s) := by
  let s1 := execInstrBr s (.ADDI .x17 .x2 256)
  let s2 := execInstrBr s1 (.SLLI .x20 .x16 10)
  let s3 := execInstrBr s2 (.ADD .x17 .x17 .x20)
  let s4 := execInstrBr s3 (.ADDI .x18 .x0 16)
  change OrdinarySteps GroupedBalancedSignImage67Byte.image s 4 s4
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x17 .x2 256)) 3
  · simp [fetch, pc, GroupedBalancedSignImage67Byte.image, word1110]; rfl
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.SLLI .x20 .x16 10)) 2
  · have hp : s1.pc = 0x215c := by simp [s1, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1111]; rfl
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADD .x17 .x17 .x20)) 1
  · have hp : s2.pc = 0x2160 := by simp [s1, s2, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1112]; rfl
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x18 .x0 16)) 0
  · have hp : s3.pc = 0x2164 := by simp [s1, s2, s3, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1113]; rfl
  · rfl
  exact OrdinarySteps.refl _

#print axioms commonBranch_steps

private theorem word1101 : GroupedBalancedSignImage67Byte.code[1101]? =
    some 0x06073813 := by decide
private theorem word1102 : GroupedBalancedSignImage67Byte.code[1102]? =
    some 0x00080863 := by decide
private theorem word1103 : GroupedBalancedSignImage67Byte.code[1103]? =
    some 0x04058023 := by decide
private theorem word1104 : GroupedBalancedSignImage67Byte.code[1104]? =
    some 0x00370b93 := by decide
private theorem word1105 : GroupedBalancedSignImage67Byte.code[1105]? =
    some 0x0140006f := by decide

theorem smallBranch_steps (s : MachineState) (n : Nat)
    (pc : s.pc = 0x2134) (sum : s.getReg .x14 = BitVec.ofNat 64 n)
    (nsmall : n < 96)
    (validFlag : accessValid (s.getReg .x11 + 64) 1 = true) :
    OrdinarySteps GroupedBalancedSignImage67Byte.image s 9 (smallBranch s) := by
  have hcond : (s.getReg .x14).ult (96 : Word) = true := by
    rw [sum]
    simp only [BitVec.ult, BitVec.toNat_ofNat,
      show (96 : Word).toNat = 96 by decide]
    rw [Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]
    exact decide_eq_true_eq.mpr nsmall
  have hse : signExtend12 (96 : BitVec 12) = (96 : Word) := by decide
  let s1 := execInstrBr s (.SLTIU .x16 .x14 96)
  let s2 := execInstrBr s1 (.BEQ .x16 .x0 16)
  let s3 := execInstrBr s2 (.SB .x11 .x0 64)
  let s4 := execInstrBr s3 (.ADDI .x23 .x14 3)
  let s5 := execInstrBr s4 (.JAL .x0 20)
  have hcond12 : (s.getReg .x14).ult (signExtend12 (96 : BitVec 12)) = true := by
    rw [hse]
    exact hcond
  have hx16 : s1.getReg .x16 = 1 := by
    simp [s1, execInstrBr, MachineState.getReg_setReg_eq]
    exact hcond12
  have hpc1 : s1.pc = 0x2138 := by simp [s1, execInstrBr, pc]
  have hpc2 : s2.pc = 0x213c := by
    simp [s2, execInstrBr, hx16, hpc1]
  have hflagaddr : s2.getReg .x11 = s.getReg .x11 := by
    simp [s1, s2, execInstrBr, MachineState.getReg_setReg_ne]
  have hvalid : accessValid (s2.getReg .x11 + signExtend12 (64 : BitVec 12)) 1 = true := by
    rw [hflagaddr]
    simpa [signExtend12] using validFlag
  have hpref : OrdinarySteps GroupedBalancedSignImage67Byte.image s 5 s5 := by
    apply OrdinarySteps.step s s1 _ (.base (.SLTIU .x16 .x14 96)) 4
    · simp [fetch, pc, GroupedBalancedSignImage67Byte.image, word1101]; rfl
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.BEQ .x16 .x0 16)) 3
    · have hp : s1.pc = 0x2138 := by simp [s1, execInstrBr, pc]
      simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1102]; rfl
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.SB .x11 .x0 64)) 2
    · simp [fetch, hpc2, GroupedBalancedSignImage67Byte.image, word1103]; rfl
    · change (if accessValid (s2.getReg .x11 + signExtend12 (64 : BitVec 12)) 1 = true
        then some s3 else none) = some s3
      rw [hvalid]
      rfl
    apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x23 .x14 3)) 1
    · have hp : s3.pc = 0x2140 := by simp [s3, execInstrBr, hpc2]
      simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1104]; rfl
    · rfl
    apply OrdinarySteps.step s4 s5 _ (.base (.JAL .x0 20)) 0
    · have hp : s4.pc = 0x2144 := by simp [s4, execInstrBr, s3, hpc2]
      simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1105]; rfl
    · rfl
    exact OrdinarySteps.refl _
  have hpc5 : s5.pc = 0x2158 := by
    simp [s5, s4, s3, execInstrBr, hpc2, signExtend21]
  have rest := commonBranch_steps s5 hpc5
  simpa only [smallBranch, branchPrefix, s1, s2, s3, s4, s5] using
    steps_comp hpref rest

#print axioms smallBranch_steps

private theorem word1106 : GroupedBalancedSignImage67Byte.code[1106]? =
    some 0x00300c13 := by decide
private theorem word1107 : GroupedBalancedSignImage67Byte.code[1107]? =
    some 0x05858023 := by decide
private theorem word1108 : GroupedBalancedSignImage67Byte.code[1108]? =
    some 0x0c000b93 := by decide
private theorem word1109 : GroupedBalancedSignImage67Byte.code[1109]? =
    some 0x40eb8bb3 := by decide

theorem largeBranch_steps (s : MachineState) (n : Nat)
    (pc : s.pc = 0x2134) (sum : s.getReg .x14 = BitVec.ofNat 64 n)
    (nbig : 96 ≤ n) (nmax : n ≤ 192)
    (validFlag : accessValid (s.getReg .x11 + 64) 1 = true) :
    OrdinarySteps GroupedBalancedSignImage67Byte.image s 10 (largeBranch s) := by
  have hcond : (s.getReg .x14).ult (96 : Word) = false := by
    rw [sum]
    simp only [BitVec.ult, BitVec.toNat_ofNat,
      show (96 : Word).toNat = 96 by decide]
    rw [Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]
    exact decide_eq_false_iff_not.mpr (by omega)
  have hse : signExtend12 (96 : BitVec 12) = (96 : Word) := by decide
  let s1 := execInstrBr s (.SLTIU .x16 .x14 96)
  let s2 := execInstrBr s1 (.BEQ .x16 .x0 16)
  let s3 := execInstrBr s2 (.ADDI .x24 .x0 3)
  let s4 := execInstrBr s3 (.SB .x11 .x24 64)
  let s5 := execInstrBr s4 (.ADDI .x23 .x0 192)
  let s6 := execInstrBr s5 (.SUB .x23 .x23 .x14)
  have hcond12 : (s.getReg .x14).ult (signExtend12 (96 : BitVec 12)) = false := by
    rw [hse]
    exact hcond
  have hx16 : s1.getReg .x16 = 0 := by
    simp [s1, execInstrBr, MachineState.getReg_setReg_eq]
    exact hcond12
  have hpc1 : s1.pc = 0x2138 := by simp [s1, execInstrBr, pc]
  have hpc2 : s2.pc = 0x2148 := by
    simp [s2, execInstrBr, hx16, hpc1, signExtend13]
  have hflagaddr : s3.getReg .x11 = s.getReg .x11 := by
    simp [s1, s2, s3, execInstrBr, MachineState.getReg_setReg_ne]
  have hvalid : accessValid (s3.getReg .x11 + signExtend12 (64 : BitVec 12)) 1 = true := by
    rw [hflagaddr]
    simpa [signExtend12] using validFlag
  have hpref : OrdinarySteps GroupedBalancedSignImage67Byte.image s 6 s6 := by
    apply OrdinarySteps.step s s1 _ (.base (.SLTIU .x16 .x14 96)) 5
    · simp [fetch, pc, GroupedBalancedSignImage67Byte.image, word1101]; rfl
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.BEQ .x16 .x0 16)) 4
    · simp [fetch, hpc1, GroupedBalancedSignImage67Byte.image, word1102]; rfl
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x24 .x0 3)) 3
    · simp [fetch, hpc2, GroupedBalancedSignImage67Byte.image, word1106]; rfl
    · rfl
    apply OrdinarySteps.step s3 s4 _ (.base (.SB .x11 .x24 64)) 2
    · have hp : s3.pc = 0x214c := by simp [s3, execInstrBr, hpc2]
      simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1107]; rfl
    · change (if accessValid (s3.getReg .x11 + signExtend12 (64 : BitVec 12)) 1 = true
        then some s4 else none) = some s4
      rw [hvalid]
      rfl
    apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x23 .x0 192)) 1
    · have hp : s4.pc = 0x2150 := by simp [s4, s3, execInstrBr, hpc2]
      simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1108]; rfl
    · rfl
    apply OrdinarySteps.step s5 s6 _ (.base (.SUB .x23 .x23 .x14)) 0
    · have hp : s5.pc = 0x2154 := by simp [s5, s4, s3, execInstrBr, hpc2]
      simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word1109]; rfl
    · rfl
    exact OrdinarySteps.refl _
  have hpc6 : s6.pc = 0x2158 := by
    simp [s6, s5, s4, s3, execInstrBr, hpc2]
  have rest := commonBranch_steps s6 hpc6
  simpa only [largeBranch, branchPrefix, s1, s2, s3, s4, s5, s6] using
    steps_comp hpref rest

#print axioms largeBranch_steps

end SigGolfCandidate.Hypertree.GroupedBalancedSignByteBranchSteps67
