import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperDecoded67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafInit67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafEntry67. -/
section
/-! Reset the upper group's leaf counter after decoding the WOTS message. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafInit67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

def initState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xe0)
  execInstrBr s (.SD .x28 .x6 0)

private theorem word464 : GroupedBalancedSignImage67Byte.code[464]? =
    some 0x00000313 := by decide
private theorem word465 : GroupedBalancedSignImage67Byte.code[465]? =
    some 0x00081e37 := by decide
private theorem word466 : GroupedBalancedSignImage67Byte.code[466]? =
    some 0x0e0e0e13 := by decide
private theorem word467 : GroupedBalancedSignImage67Byte.code[467]? =
    some 0x006e3023 := by decide

theorem init_steps (s : MachineState) (pc : s.pc = 0x1740) :
    OrdinarySteps image s 4 (initState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0xe0)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  change OrdinarySteps image s 4 s4
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0)) 3
  · simp [fetch, pc, GroupedBalancedSignImage67Byte.image, word464]; rfl
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s1.pc = 0x1744 := by simp [s1, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word465]; rfl
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0xe0)) 1
  · have hp : s2.pc = 0x1748 := by simp [s1, s2, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word466]; rfl
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s3.pc = 0x174c := by simp [s1, s2, s3, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word467]; rfl
  · have haddr : s3.getReg .x28 = 0x810e0 := by
      simp [s1,s2,s3,execInstrBr,MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne,signExtend12]
    simp [ordinaryStep,memoryArgumentsValid,s4,haddr,signExtend12,
      accessValid,rangeValid,MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem init_pc (s : MachineState) (pc : s.pc = 0x1740) :
    (initState s).pc = 0x1750 := by
  simp [initState, execInstrBr, pc]

theorem init_count (s : MachineState) :
    (initState s).getMem 0x810e0 = 0 := by
  simp [initState, execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, signExtend12]

theorem init_frame (s : MachineState) (a : Word) (ha : a ≠ 0x810e0) :
    (initState s).getMem a = s.getMem a := by
  simp [initState, execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, signExtend12]
  intro h
  exact False.elim (ha h)

theorem init_byte (s : MachineState) (a : Word)
    (ha : alignToDword a ≠ 0x810e0) :
    (initState s).getByte a = s.getByte a := by
  simp only [MachineState.getByte,init_frame s (alignToDword a) ha]

theorem init_digit_byte (s : MachineState) (i : Fin 67) :
    (initState s).getByte (BitVec.ofNat 64 (0x80600+i.val)) =
      s.getByte (BitVec.ofNat 64 (0x80600+i.val)) := by
  apply init_byte
  have hi := i.isLt
  have hbit : (BitVec.ofNat 64 (0x80600+i.val)).getLsbD 12 = false := by
    rw [BitVec.getLsbD_ofNat]
    simp only [show decide (12 < 64) = true by decide, Bool.true_and]
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have hdiv : (0x80600+i.val) / 2^12 = 128 := by omega
    rw [hdiv]
    decide
  have halign : (alignToDword (BitVec.ofNat 64 (0x80600+i.val))).getLsbD 12 =
      false := by simpa [alignToDword] using hbit
  intro h
  have hc := congrArg (fun v : Word => v.getLsbD 12) h
  rw [halign] at hc
  have target : (0x810e0 : Word).getLsbD 12 = true := by decide
  rw [target] at hc
  cases hc

theorem init_table_byte (s : MachineState) (i : Nat) (hi : i < 2304) :
    (initState s).getByte (BitVec.ofNat 64 (0xfff700+i)) =
      s.getByte (BitVec.ofNat 64 (0xfff700+i)) := by
  apply init_byte
  intro h
  have hinput : (BitVec.ofNat 64 (0xfff700+i)).getLsbD 20 = true := by
    rw [BitVec.getLsbD_ofNat]
    simp only [show decide (20 < 64) = true by decide, Bool.true_and]
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have hdiv : (0xfff700+i) / 2^20 = 15 := by omega
    rw [hdiv]
    decide
  have halign : (alignToDword (BitVec.ofNat 64 (0xfff700+i))).getLsbD 20 =
      true := by simpa [alignToDword] using hinput
  rw [h] at halign
  contradiction

#print axioms init_steps
#print axioms init_pc
#print axioms init_count
#print axioms init_frame
#print axioms init_digit_byte
#print axioms init_table_byte
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafInit67

end

/-! One upper group reaches its first WOTS leaf with decoded message digits. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafEntry67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteContract67
open SigGolfCandidate.Hypertree.GroupedBalancedSignUpperDecoded67
open SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafInit67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

def leafEntryState (s : MachineState) (message : BitVec 128) : MachineState :=
  initState (decodedState s message)

theorem leaf_entry (s : MachineState) (message : BitVec 128)
    (pc : s.pc = 0x1720)
    (stack : s.getReg .x2 = 0xfff700)
    (hmsg : ∀ j : Fin 16,
      s.getByte (BitVec.ofNat 64 (0x80500+j.val)) =
        message.extractLsb' (8*j.val) 8)
    (tables : Tables s) :
    OrdinarySteps image s
      (8 + (8+112+(if GroupedBalancedQuaternary.rawSum message < 96 then 9 else 10)+144+6) + 4)
      (leafEntryState s message) ∧
    (leafEntryState s message).pc = 0x1750 ∧
    (leafEntryState s message).getMem 0x810e0 = 0 ∧
    (∀ chain : Fin 67,
      (leafEntryState s message).getByte
        (BitVec.ofNat 64 (0x80600+chain.val)) =
      BitVec.ofNat 8 (GroupedBalancedChecksum67.digit message chain).val) ∧
    Tables (leafEntryState s message) := by
  obtain ⟨decoded,pcDecoded,digits,tablesDecoded⟩ :=
    decode_group s message pc stack hmsg tables
  have initialized := init_steps (decodedState s message) pcDecoded
  refine ⟨?_,init_pc _ pcDecoded,init_count _,?_,?_⟩
  · exact GroupedBalancedDecoderByteSumLoop67.steps_comp decoded initialized
  · intro chain
    rw [leafEntryState,init_digit_byte]
    exact digits chain
  · intro i hi
    rw [leafEntryState,init_table_byte _ i hi]
    exact tablesDecoded i hi

#print axioms leaf_entry
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafEntry67
