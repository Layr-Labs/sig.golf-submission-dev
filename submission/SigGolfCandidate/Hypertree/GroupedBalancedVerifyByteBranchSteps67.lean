import SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteBranch67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteBranch67
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteSumLoop67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteBranchSteps67

private theorem word683 : GroupedBalancedVerifyImage67Fast2Byte.code[683]? =
    some 0x10010893 := by decide
private theorem word684 : GroupedBalancedVerifyImage67Fast2Byte.code[684]? =
    some 0x00a81a13 := by decide
private theorem word685 : GroupedBalancedVerifyImage67Fast2Byte.code[685]? =
    some 0x014888b3 := by decide
private theorem word686 : GroupedBalancedVerifyImage67Fast2Byte.code[686]? =
    some 0x01000913 := by decide

theorem commonBranch_steps (s : MachineState) (pc : s.pc = 0x1aac) :
    OrdinarySteps GroupedBalancedVerifyImage67Fast2Byte.image s 4 (commonBranch s) := by
  let s1 := execInstrBr s (.ADDI .x17 .x2 256)
  let s2 := execInstrBr s1 (.SLLI .x20 .x16 10)
  let s3 := execInstrBr s2 (.ADD .x17 .x17 .x20)
  let s4 := execInstrBr s3 (.ADDI .x18 .x0 16)
  change OrdinarySteps GroupedBalancedVerifyImage67Fast2Byte.image s 4 s4
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x17 .x2 256)) 3
  · simp [fetch, pc, GroupedBalancedVerifyImage67Fast2Byte.image, word683]; rfl
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.SLLI .x20 .x16 10)) 2
  · have hp : s1.pc = 0x1ab0 := by simp [s1, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word684]; rfl
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADD .x17 .x17 .x20)) 1
  · have hp : s2.pc = 0x1ab4 := by simp [s1, s2, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word685]; rfl
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x18 .x0 16)) 0
  · have hp : s3.pc = 0x1ab8 := by simp [s1, s2, s3, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word686]; rfl
  · rfl
  exact OrdinarySteps.refl _

#print axioms commonBranch_steps

private theorem word674 : GroupedBalancedVerifyImage67Fast2Byte.code[674]? =
    some 0x06073813 := by decide
private theorem word675 : GroupedBalancedVerifyImage67Fast2Byte.code[675]? =
    some 0x00080863 := by decide
private theorem word676 : GroupedBalancedVerifyImage67Fast2Byte.code[676]? =
    some 0x04058023 := by decide
private theorem word677 : GroupedBalancedVerifyImage67Fast2Byte.code[677]? =
    some 0x00370b93 := by decide
private theorem word678 : GroupedBalancedVerifyImage67Fast2Byte.code[678]? =
    some 0x0140006f := by decide

theorem smallBranch_steps (s : MachineState) (n : Nat)
    (pc : s.pc = 0x1a88) (sum : s.getReg .x14 = BitVec.ofNat 64 n)
    (nsmall : n < 96)
    (validFlag : accessValid (s.getReg .x11 + 64) 1 = true) :
    OrdinarySteps GroupedBalancedVerifyImage67Fast2Byte.image s 9 (smallBranch s) := by
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
  have hpc1 : s1.pc = 0x1a8c := by simp [s1, execInstrBr, pc]
  have hpc2 : s2.pc = 0x1a90 := by
    simp [s2, execInstrBr, hx16, hpc1]
  have hflagaddr : s2.getReg .x11 = s.getReg .x11 := by
    simp [s1, s2, execInstrBr, MachineState.getReg_setReg_ne]
  have hvalid : accessValid (s2.getReg .x11 + signExtend12 (64 : BitVec 12)) 1 = true := by
    rw [hflagaddr]
    simpa [signExtend12] using validFlag
  have hpref : OrdinarySteps GroupedBalancedVerifyImage67Fast2Byte.image s 5 s5 := by
    apply OrdinarySteps.step s s1 _ (.base (.SLTIU .x16 .x14 96)) 4
    · simp [fetch, pc, GroupedBalancedVerifyImage67Fast2Byte.image, word674]; rfl
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.BEQ .x16 .x0 16)) 3
    · have hp : s1.pc = 0x1a8c := by simp [s1, execInstrBr, pc]
      simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word675]; rfl
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.SB .x11 .x0 64)) 2
    · simp [fetch, hpc2, GroupedBalancedVerifyImage67Fast2Byte.image, word676]; rfl
    · change (if accessValid (s2.getReg .x11 + signExtend12 (64 : BitVec 12)) 1 = true
        then some s3 else none) = some s3
      rw [hvalid]
      rfl
    apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x23 .x14 3)) 1
    · have hp : s3.pc = 0x1a94 := by simp [s3, execInstrBr, hpc2]
      simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word677]; rfl
    · rfl
    apply OrdinarySteps.step s4 s5 _ (.base (.JAL .x0 20)) 0
    · have hp : s4.pc = 0x1a98 := by simp [s4, execInstrBr, s3, hpc2]
      simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word678]; rfl
    · rfl
    exact OrdinarySteps.refl _
  have hpc5 : s5.pc = 0x1aac := by
    simp [s5, s4, s3, execInstrBr, hpc2, signExtend21]
  have rest := commonBranch_steps s5 hpc5
  simpa only [smallBranch, branchPrefix, s1, s2, s3, s4, s5] using
    steps_comp hpref rest

#print axioms smallBranch_steps

private theorem word679 : GroupedBalancedVerifyImage67Fast2Byte.code[679]? =
    some 0x00300c13 := by decide
private theorem word680 : GroupedBalancedVerifyImage67Fast2Byte.code[680]? =
    some 0x05858023 := by decide
private theorem word681 : GroupedBalancedVerifyImage67Fast2Byte.code[681]? =
    some 0x0c000b93 := by decide
private theorem word682 : GroupedBalancedVerifyImage67Fast2Byte.code[682]? =
    some 0x40eb8bb3 := by decide

theorem largeBranch_steps (s : MachineState) (n : Nat)
    (pc : s.pc = 0x1a88) (sum : s.getReg .x14 = BitVec.ofNat 64 n)
    (nbig : 96 ≤ n) (nmax : n ≤ 192)
    (validFlag : accessValid (s.getReg .x11 + 64) 1 = true) :
    OrdinarySteps GroupedBalancedVerifyImage67Fast2Byte.image s 10 (largeBranch s) := by
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
  have hpc1 : s1.pc = 0x1a8c := by simp [s1, execInstrBr, pc]
  have hpc2 : s2.pc = 0x1a9c := by
    simp [s2, execInstrBr, hx16, hpc1, signExtend13]
  have hflagaddr : s3.getReg .x11 = s.getReg .x11 := by
    simp [s1, s2, s3, execInstrBr, MachineState.getReg_setReg_ne]
  have hvalid : accessValid (s3.getReg .x11 + signExtend12 (64 : BitVec 12)) 1 = true := by
    rw [hflagaddr]
    simpa [signExtend12] using validFlag
  have hpref : OrdinarySteps GroupedBalancedVerifyImage67Fast2Byte.image s 6 s6 := by
    apply OrdinarySteps.step s s1 _ (.base (.SLTIU .x16 .x14 96)) 5
    · simp [fetch, pc, GroupedBalancedVerifyImage67Fast2Byte.image, word674]; rfl
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.BEQ .x16 .x0 16)) 4
    · simp [fetch, hpc1, GroupedBalancedVerifyImage67Fast2Byte.image, word675]; rfl
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x24 .x0 3)) 3
    · simp [fetch, hpc2, GroupedBalancedVerifyImage67Fast2Byte.image, word679]; rfl
    · rfl
    apply OrdinarySteps.step s3 s4 _ (.base (.SB .x11 .x24 64)) 2
    · have hp : s3.pc = 0x1aa0 := by simp [s3, execInstrBr, hpc2]
      simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word680]; rfl
    · change (if accessValid (s3.getReg .x11 + signExtend12 (64 : BitVec 12)) 1 = true
        then some s4 else none) = some s4
      rw [hvalid]
      rfl
    apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x23 .x0 192)) 1
    · have hp : s4.pc = 0x1aa4 := by simp [s4, s3, execInstrBr, hpc2]
      simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word681]; rfl
    · rfl
    apply OrdinarySteps.step s5 s6 _ (.base (.SUB .x23 .x23 .x14)) 0
    · have hp : s5.pc = 0x1aa8 := by simp [s5, s4, s3, execInstrBr, hpc2]
      simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word682]; rfl
    · rfl
    exact OrdinarySteps.refl _
  have hpc6 : s6.pc = 0x1aac := by
    simp [s6, s5, s4, s3, execInstrBr, hpc2]
  have rest := commonBranch_steps s6 hpc6
  simpa only [largeBranch, branchPrefix, s1, s2, s3, s4, s5, s6] using
    steps_comp hpref rest

#print axioms largeBranch_steps

end SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteBranchSteps67
