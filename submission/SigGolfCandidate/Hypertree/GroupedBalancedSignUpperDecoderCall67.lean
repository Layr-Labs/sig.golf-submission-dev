import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperChoose67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCopyStack67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperBaseH367; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperDecoderCall67. -/
section
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperBaseH367
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def Outside (a : Word) : Prop :=
  a ≠ 0x810d0 ∧ a ≠ 0x810e8 ∧ a ≠ 0x810a8 ∧
  (∀ i : Nat, i < 2 → a ≠ Signing.wordAddress 0x810b0 i) ∧
  (∀ i : Nat, i < 3 → a ≠ Signing.wordAddress 0x81008 i)

theorem setup (s : MachineState)
    (pc : s.pc = 0x15e0) (height : s.getMem 0x81060 = 3) :
    ∃ finish : MachineState,
      OrdinarySteps image s 61 finish ∧
      finish.pc = 0x1720 ∧
      finish.getMem 0x810d0 = 8 ∧
      finish.getMem 0x810e8 = (s.getMem 0x81090 &&& 7#64) ∧
      finish.getMem 0x810a8 =
        (s.getMem 0x81090 &&& 18446744073709551608#64) ∧
      (∀ i : Nat, i < 2 →
        finish.getMem (Signing.wordAddress 0x810b0 i) =
          s.getMem (Signing.wordAddress 0x81098 i)) ∧
      (∀ i : Nat, i < 3 →
        finish.getMem (Signing.wordAddress 0x81008 i) =
          finish.getMem (Signing.wordAddress 0x810a8 i)) ∧
      (∀ a : Word, Outside a → finish.getMem a = s.getMem a) ∧
      finish.getReg .x2=s.getReg .x2 := by
  let chosen := GroupedBalancedSignUpperChoose67.chooseState s
  have chooseTrace := GroupedBalancedSignUpperChoose67.choose_steps s pc
  have chosenPc : chosen.pc = 0x15f4 := by
    have hh : s.getMem (528480#64) = (3#64) := height
    simpa [hh] using GroupedBalancedSignUpperChoose67.choose_pc s pc
  let entered := GroupedBalancedSignUpperEntryH367.entryState chosen
  have enterTrace := GroupedBalancedSignUpperEntryH367.entry_steps chosen chosenPc
  have enteredPc := GroupedBalancedSignUpperEntryH367.entry_pc chosen chosenPc
  obtain ⟨upper,upperTrace,upperPc,upperWords,upperFrame⟩ :=
    GroupedBalancedSignUpperCopiesH367.upper_copy entered enteredPc
  obtain ⟨base,baseTrace,basePc,baseWords,baseFrame⟩ :=
    GroupedBalancedSignUpperCopiesH367.base_copy upper upperPc
  let finish := GroupedBalancedSignUpperTailH367.tailState base
  have tailTrace := GroupedBalancedSignUpperTailH367.tail_steps base basePc
  have finishPc := GroupedBalancedSignUpperTailH367.tail_pc base basePc
  have trace : OrdinarySteps image s 61 finish := by
    simpa [finish,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      Keygen.ordinary_trans image s base finish 56 5
        (Keygen.ordinary_trans image s upper base 33 23
          (Keygen.ordinary_trans image s entered upper 16 17
            (Keygen.ordinary_trans image s chosen entered 5 11 chooseTrace enterTrace)
            upperTrace) baseTrace) tailTrace
  have target : finish.getMem 0x810e8 = (s.getMem 0x81090 &&& 7#64) := by
    rw [GroupedBalancedSignUpperTailH367.tail_frame base 0x810e8 (by decide)]
    rw [baseFrame 0x810e8 (by intro i hi; interval_cases i <;> decide)]
    rw [upperFrame 0x810e8 (by intro i hi; interval_cases i <;> decide)]
    rw [GroupedBalancedSignUpperEntryH367.entry_selected chosen]
    rw [GroupedBalancedSignUpperChoose67.choose_frame s 0x81090]
  have rounded : finish.getMem 0x810a8 =
      (s.getMem 0x81090 &&& 18446744073709551608#64) := by
    rw [GroupedBalancedSignUpperTailH367.tail_frame base 0x810a8 (by decide)]
    rw [baseFrame 0x810a8 (by intro i hi; interval_cases i <;> decide)]
    rw [upperFrame 0x810a8 (by intro i hi; interval_cases i <;> decide)]
    rw [GroupedBalancedSignUpperEntryH367.entry_rounded chosen]
    rw [GroupedBalancedSignUpperChoose67.choose_frame s 0x81090]
  have upperRest : ∀ i : Nat, i < 2 →
      finish.getMem (Signing.wordAddress 0x810b0 i) =
        s.getMem (Signing.wordAddress 0x81098 i) := by
    intro i hi
    rw [GroupedBalancedSignUpperTailH367.tail_frame base _
      (by interval_cases i <;> decide)]
    rw [baseFrame _ (by intro j hj; interval_cases i <;> interval_cases j <;> decide)]
    rw [upperWords i hi]
    rw [GroupedBalancedSignUpperEntryH367.entry_frame chosen _
      (by interval_cases i <;> decide) (by interval_cases i <;> decide)]
    rw [GroupedBalancedSignUpperChoose67.choose_frame s _]
  have baseRest : ∀ i : Nat, i < 3 →
      finish.getMem (Signing.wordAddress 0x81008 i) =
        finish.getMem (Signing.wordAddress 0x810a8 i) := by
    intro i hi
    rw [GroupedBalancedSignUpperTailH367.tail_frame base _
      (by interval_cases i <;> decide)]
    rw [baseWords i hi]
    rw [GroupedBalancedSignUpperTailH367.tail_frame base _
      (by interval_cases i <;> decide)]
    rw [baseFrame _ (by intro j hj; interval_cases i <;> interval_cases j <;> decide)]
  have frame : ∀ a : Word, Outside a → finish.getMem a = s.getMem a := by
    intro a ha
    rw [GroupedBalancedSignUpperTailH367.tail_frame base a ha.1,
      baseFrame a ha.2.2.2.2,
      upperFrame a ha.2.2.2.1,
      GroupedBalancedSignUpperEntryH367.entry_frame chosen a ha.2.1 ha.2.2.1,
      GroupedBalancedSignUpperChoose67.choose_frame s a]
  have chooseSp : chosen.getReg .x2=s.getReg .x2 := by
    simp [chosen,GroupedBalancedSignUpperChoose67.chooseState,
      execInstrBr,MachineState.getReg_setReg_ne]
  have entrySp : entered.getReg .x2=chosen.getReg .x2 := by
    simp [entered,GroupedBalancedSignUpperEntryH367.entryState,
      execInstrBr,MachineState.getReg_setReg_ne]
  have upperSp : upper.getReg .x2=entered.getReg .x2 :=
    GroupedBalancedSignUpperCopyStack67.upper_h3_sp entered upper
      enteredPc upperTrace
  have baseSp : base.getReg .x2=upper.getReg .x2 :=
    GroupedBalancedSignUpperCopyStack67.base_h3_sp upper base
      upperPc baseTrace
  have tailSp : finish.getReg .x2=base.getReg .x2 := by
    simp [finish,GroupedBalancedSignUpperTailH367.tailState,
      execInstrBr,MachineState.getReg_setReg_ne]
  exact ⟨finish,trace,finishPc,GroupedBalancedSignUpperTailH367.tail_count base,
    target,rounded,upperRest,baseRest,frame,
    tailSp.trans (baseSp.trans (upperSp.trans (entrySp.trans chooseSp)))⟩

#print axioms setup
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperBaseH367

end

/-! Enter the relocated byte-table decoder from an upper signing group. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperDecoderCall67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

def callState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xf0)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1072)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xf8)
  let s := execInstrBr s (.SD .x28 .x6 0)
  execInstrBr s (.JAL .x1 0x9bc)

private theorem word456 : GroupedBalancedSignImage67Byte.code[456]? =
    some 0x00081e37 := by decide
private theorem word457 : GroupedBalancedSignImage67Byte.code[457]? =
    some 0x0f0e0e13 := by decide
private theorem word458 : GroupedBalancedSignImage67Byte.code[458]? =
    some 0x000e3303 := by decide
private theorem word459 : GroupedBalancedSignImage67Byte.code[459]? =
    some 0x43030313 := by decide
private theorem word460 : GroupedBalancedSignImage67Byte.code[460]? =
    some 0x00081e37 := by decide
private theorem word461 : GroupedBalancedSignImage67Byte.code[461]? =
    some 0x0f8e0e13 := by decide
private theorem word462 : GroupedBalancedSignImage67Byte.code[462]? =
    some 0x006e3023 := by decide
private theorem word463 : GroupedBalancedSignImage67Byte.code[463]? =
    some 0x1bd000ef := by decide

theorem call_steps (s : MachineState) (pc : s.pc = 0x1720)
    (valid : accessValid (0x810f0 : Word) 8 = true) :
    OrdinarySteps image s 8 (callState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0xf0)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 1072)
  let s5 := execInstrBr s4 (.LUI .x28 0x81)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 0xf8)
  let s7 := execInstrBr s6 (.SD .x28 .x6 0)
  let s8 := execInstrBr s7 (.JAL .x1 0x9bc)
  change OrdinarySteps image s 8 s8
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 7
  · simp [fetch, pc, GroupedBalancedSignImage67Byte.image, word456]; rfl
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0xf0)) 6
  · have hp : s1.pc = 0x1724 := by simp [s1, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word457]; rfl
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 5
  · have hp : s2.pc = 0x1728 := by simp [s1, s2, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word458]; rfl
  · change (if accessValid (s2.getReg .x28 + signExtend12 (0 : BitVec 12)) 8
      then some s3 else none) = some s3
    have haddr : s2.getReg .x28 = 0x810f0 := by
      simp [s1, s2, execInstrBr, MachineState.getReg_setReg_eq, signExtend12]
    simpa [haddr, signExtend12] using valid
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 1072)) 4
  · have hp : s3.pc = 0x172c := by simp [s1, s2, s3, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word459]; rfl
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x81)) 3
  · have hp : s4.pc = 0x1730 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word460]; rfl
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 0xf8)) 2
  · have hp : s5.pc = 0x1734 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word461]; rfl
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x6 0)) 1
  · have hp : s6.pc = 0x1738 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word462]; rfl
  · change (if accessValid (s6.getReg .x28 + signExtend12 (0 : BitVec 12)) 8
      then some s7 else none) = some s7
    have haddr : s6.getReg .x28 = 0x810f8 := by
      simp [s5, s6, execInstrBr, MachineState.getReg_setReg_eq, signExtend12]
    simp [haddr, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s7 s8 _ (.base (.JAL .x1 0x9bc)) 0
  · have hp : s7.pc = 0x173c := by
      simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedSignImage67Byte.image, word463]; rfl
  · rfl
  exact OrdinarySteps.refl _

theorem call_pc (s : MachineState) (pc : s.pc = 0x1720) :
    (callState s).pc = 0x20f8 := by
  simp [callState, execInstrBr, pc, signExtend21]

theorem call_link (s : MachineState) (pc : s.pc = 0x1720) :
    (callState s).getReg .x1 = 0x1740 := by
  simp [callState, execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, pc]

theorem call_path (s : MachineState) :
    (callState s).getMem 0x810f8 = s.getMem 0x810f0 + 1072 := by
  simp [callState, execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, signExtend12]

theorem call_stack (s : MachineState) :
    (callState s).getReg .x2 = s.getReg .x2 := by
  simp [callState, execInstrBr, MachineState.getReg_setReg_ne]

theorem call_mem_other (s : MachineState) (a : Word) (ha : a ≠ 0x810f8) :
    (callState s).getMem a = s.getMem a := by
  simp [callState, execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, signExtend12]
  intro h
  exact False.elim (ha h)

theorem call_byte (s : MachineState) (a : Word)
    (ha : alignToDword a ≠ 0x810f8) :
    (callState s).getByte a = s.getByte a := by
  simp only [MachineState.getByte, call_mem_other s (alignToDword a) ha]

theorem call_digest_byte (s : MachineState) (j : Fin 16) :
    (callState s).getByte (BitVec.ofNat 64 (0x80500+j.val)) =
      s.getByte (BitVec.ofNat 64 (0x80500+j.val)) := by
  apply call_byte
  fin_cases j <;> decide

private theorem table_bit20 (i : Nat) (hi : i < 2304) :
    (BitVec.ofNat 64 (0xfff700+i)).getLsbD 20 = true := by
  rw [BitVec.getLsbD_ofNat]
  simp only [show decide (20 < 64) = true by decide, Bool.true_and]
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hdiv : (0xfff700+i) / 2^20 = 15 := by omega
  rw [hdiv]
  decide

theorem call_table_byte (s : MachineState) (i : Nat) (hi : i < 2304) :
    (callState s).getByte (BitVec.ofNat 64 (0xfff700+i)) =
      s.getByte (BitVec.ofNat 64 (0xfff700+i)) := by
  apply call_byte
  intro heq
  have hbit := table_bit20 i hi
  have halign : (alignToDword (BitVec.ofNat 64 (0xfff700+i))).getLsbD 20 =
      true := by simpa [alignToDword] using hbit
  rw [heq] at halign
  contradiction

#print axioms call_steps
#print axioms call_pc
#print axioms call_link
#print axioms call_path
#print axioms call_stack
#print axioms call_mem_other
#print axioms call_byte
#print axioms call_digest_byte
#print axioms call_table_byte
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperDecoderCall67
