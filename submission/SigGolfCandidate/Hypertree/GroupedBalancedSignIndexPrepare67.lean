import SigGolfCandidate.Hypertree.SignIndexPrepare
import SigGolfCandidate.Hypertree.GroupedBalancedSignRandomizerLoaded67

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignIndexPrepare67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
open SigGolfCandidate.Hypertree.Signing
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
def image : Image := GroupedBalancedSignImage67.image

def slotCopyState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x20)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x28)
  execInstrBr s (.SD .x28 .x6 0)

theorem slotCopyState_block (s : MachineState) (pc : s.pc = 0x10d8) :
    OrdinarySteps image s 8 (slotCopyState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x80)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0x20)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.ADDI .x6 .x0 0)
  let s6 := execInstrBr s5 (.LUI .x28 0x80)
  let s7 := execInstrBr s6 (.ADDI .x28 .x28 0x28)
  let s8 := execInstrBr s7 (.SD .x28 .x6 0)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0)) 7
  · simp only [fetch,pc,image,GroupedBalancedSignImage67.image]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x80)) 6
  · have hp : s1.pc = 0x10dc := by simp [s1,execInstrBr,pc]
    simp only [fetch,hp,image,GroupedBalancedSignImage67.image]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0x20)) 5
  · have hp : s2.pc = 0x10e0 := by simp [s1,s2,execInstrBr,pc]
    simp only [fetch,hp,image,GroupedBalancedSignImage67.image]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 4
  · have hp : s3.pc = 0x10e4 := by simp [s1,s2,s3,execInstrBr,pc]
    simp only [fetch,hp,image,GroupedBalancedSignImage67.image]; decide
  · simp [s1,s2,s3,s4,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x6 .x0 0)) 3
  · have hp : s4.pc = 0x10e8 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simp only [fetch,hp,image,GroupedBalancedSignImage67.image]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 0x80)) 2
  · have hp : s5.pc = 0x10ec := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simp only [fetch,hp,image,GroupedBalancedSignImage67.image]; decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 0x28)) 1
  · have hp : s6.pc = 0x10f0 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simp only [fetch,hp,image,GroupedBalancedSignImage67.image]; decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s7.pc = 0x10f4 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simp only [fetch,hp,image,GroupedBalancedSignImage67.image]; decide
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,
      ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  simpa [s8,s7,s6,s5,s4,s3,s2,s1,slotCopyState] using
    (OrdinarySteps.refl s8 : OrdinarySteps image s8 0 s8)

def indexMessageCopyState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x30)
  execInstrBr s (.ADDI .x10 .x0 4)

theorem indexMessageCopyState_block (s : MachineState) (pc : s.pc = 0x10f8) :
    OrdinarySteps image s 4 (indexMessageCopyState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x7 0x80)
  let s3 := execInstrBr s2 (.ADDI .x7 .x7 0x30)
  let s4 := execInstrBr s3 (.ADDI .x10 .x0 4)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0)) 3
  · have hp : s.pc = 0x10f8 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s1.pc = 0x10fc := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x7 .x7 0x30)) 1
  · have hp : s2.pc = 0x1100 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x10 .x0 4)) 0
  · have hp : s3.pc = 0x1104 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  exact OrdinarySteps.refl _

def inputRandomizerCopyState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x20)
  let s := execInstrBr s (.ADDI .x6 .x6 0x60)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x50)
  execInstrBr s (.ADDI .x10 .x0 4)

theorem inputRandomizerCopyState_block (s : MachineState) (pc : s.pc = 0x1120) :
    OrdinarySteps image s 5 (inputRandomizerCopyState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x20)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x60)
  let s3 := execInstrBr s2 (.LUI .x7 0x80)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0x50)
  let s5 := execInstrBr s4 (.ADDI .x10 .x0 4)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x20)) 4
  · have hp : s.pc = 0x1120 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x60)) 3
  · have hp : s1.pc = 0x1124 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s2.pc = 0x1128 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0x50)) 1
  · have hp : s3.pc = 0x112c := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x10 .x0 4)) 0
  · have hp : s4.pc = 0x1130 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  exact OrdinarySteps.refl _

def indexHeaderState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x10 .x0 5)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.SD .x28 .x10 0)
  let s := execInstrBr s (.ADDI .x11 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.ADDI .x11 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.ADDI .x11 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  execInstrBr s (.SD .x28 .x11 0)

theorem indexHeaderState_block (s : MachineState) (pc : s.pc = 0x114c) :
    OrdinarySteps image s 16 (indexHeaderState s) := by
  let s1 := execInstrBr s (.ADDI .x10 .x0 5)
  let s2 := execInstrBr s1 (.LUI .x28 0x80)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0)
  let s4 := execInstrBr s3 (.SD .x28 .x10 0)
  let s5 := execInstrBr s4 (.ADDI .x11 .x0 0)
  let s6 := execInstrBr s5 (.LUI .x28 0x80)
  let s7 := execInstrBr s6 (.ADDI .x28 .x28 8)
  let s8 := execInstrBr s7 (.SD .x28 .x11 0)
  let s9 := execInstrBr s8 (.ADDI .x11 .x0 0)
  let s10 := execInstrBr s9 (.LUI .x28 0x80)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 16)
  let s12 := execInstrBr s11 (.SD .x28 .x11 0)
  let s13 := execInstrBr s12 (.ADDI .x11 .x0 0)
  let s14 := execInstrBr s13 (.LUI .x28 0x80)
  let s15 := execInstrBr s14 (.ADDI .x28 .x28 24)
  let s16 := execInstrBr s15 (.SD .x28 .x11 0)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x10 .x0 5)) 15
  · have hp : s.pc = 0x114c := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x80)) 14
  · have hp : s1.pc = 0x1150 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 13
  · have hp : s2.pc = 0x1154 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x10 0)) 12
  · have hp : s3.pc = 0x1158 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x11 .x0 0)) 11
  · have hp : s4.pc = 0x115c := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 0x80)) 10
  · have hp : s5.pc = 0x1160 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 8)) 9
  · have hp : s6.pc = 0x1164 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x11 0)) 8
  · have hp : s7.pc = 0x1168 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x11 .x0 0)) 7
  · have hp : s8.pc = 0x116c := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 0x80)) 6
  · have hp : s9.pc = 0x1170 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 16)) 5
  · have hp : s10.pc = 0x1174 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.SD .x28 .x11 0)) 4
  · have hp : s11.pc = 0x1178 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x11 .x0 0)) 3
  · have hp : s12.pc = 0x117c := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.LUI .x28 0x80)) 2
  · have hp : s13.pc = 0x1180 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.ADDI .x28 .x28 24)) 1
  · have hp : s14.pc = 0x1184 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.SD .x28 .x11 0)) 0
  · have hp : s15.pc = 0x1188 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem slotCopyState_mem (s : MachineState) (a : Word) :
    (slotCopyState s).getMem a =
      if a = 0x80028 then 0 else if a = 0x80020 then 0 else s.getMem a := by
  simp [slotCopyState,execInstrBr,signExtend12,Expansion.mem_setMem,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem slotCopyState_pc (s : MachineState) :
    (slotCopyState s).pc = s.pc + 32 := by
  simp [slotCopyState,execInstrBr,BitVec.add_assoc]

theorem slotCopyState_frame (s : MachineState) (a : Word)
    (h20 : a ≠ 0x80020) (h28 : a ≠ 0x80028) :
    (slotCopyState s).getMem a = s.getMem a := by
  rw [slotCopyState_mem,if_neg h28,if_neg h20]

theorem indexMessageCopyState_mem (s : MachineState) (a : Word) :
    (indexMessageCopyState s).getMem a = s.getMem a := by simp [indexMessageCopyState, execInstrBr]

theorem indexMessageCopyState_invariant (s : MachineState) (pc : s.pc = 0x10f8) :
    CopyInvariant 0x1108 0x0 0x80030 4 4 (indexMessageCopyState s) := by
  simp [CopyInvariant, indexMessageCopyState, execInstrBr, signExtend12, pc,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem inputRandomizerCopyState_mem (s : MachineState) (a : Word) :
    (inputRandomizerCopyState s).getMem a = s.getMem a := by simp [inputRandomizerCopyState, execInstrBr]

theorem inputRandomizerCopyState_invariant (s : MachineState) (pc : s.pc = 0x1120) :
    CopyInvariant 0x1134 0x20060 0x80050 4 4 (inputRandomizerCopyState s) := by
  simp [CopyInvariant, inputRandomizerCopyState, execInstrBr, signExtend12, pc,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem indexHeaderState_pc (s : MachineState) : (indexHeaderState s).pc = s.pc + 64 := by
  simp [indexHeaderState, execInstrBr, BitVec.add_assoc]

theorem indexHeaderState_mem (s : MachineState) (a : Word) :
    (indexHeaderState s).getMem a =
      if a = 0x80018 then 0 else if a = 0x80010 then 0 else
        if a = 0x80008 then 0 else if a = 0x80000 then 5 else s.getMem a := by
  simp [indexHeaderState, execInstrBr, signExtend12, Expansion.mem_setMem,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

def indexInputWord (s : MachineState) (i : Fin 14) : Word :=
  if i.val = 0 then 5 else if i.val < 4 then 0 else
    if i.val < 6 then 0
    else if i.val < 10 then s.getMem (wordAddress 0 (i.val - 6))
    else s.getMem (wordAddress 0x20060 (i.val - 10))

/-- Preparation of the complete tag5/zero-slot/message/randomizer input. -/
theorem index_prepare (s : MachineState) (pc : s.pc = 0x10d8) :
    ∃ ready, OrdinarySteps image s 81 ready ∧ ready.pc = 0x118c ∧
      (∀ i : Fin 14, ready.getMem (wordAddress 0x80000 i.val) = indexInputWord s i) ∧
      (∀ a, (∀ i : Fin 14, a ≠ wordAddress 0x80000 i.val) → ready.getMem a = s.getMem a) := by
  let slot := slotCopyState s
  have slotLoop : OrdinarySteps image s 8 slot := slotCopyState_block s pc
  have slotpc : slot.pc = 0x10f8 := by simp [slot,slotCopyState_pc,pc]
  have slotOutput (i : Fin 2) :
      slot.getMem (wordAddress 0x80020 i.val) = 0 := by
    fin_cases i <;> simp [slot,slotCopyState_mem,wordAddress]
  have slotFrame (a : Word)
      (outside : ∀ i, i < 2 → a ≠ wordAddress 0x80020 i) :
      slot.getMem a = s.getMem a := by
    apply slotCopyState_frame
    · exact outside 0 (by decide)
    · exact outside 1 (by decide)
  obtain ⟨msg, msgLoop, msgInv, msgOutput, msgFrame⟩ := copy_all image 0x1108 (by decide)
    0 0x80030 4 (indexMessageCopyState slot) (indexMessageCopyState_invariant slot slotpc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have msgpc : msg.pc = 0x1120 := by simpa [CopyInvariant] using msgInv.2.2.1
  obtain ⟨rand, randLoop, randInv, randOutput, randFrame⟩ := copy_all image 0x1134 (by decide)
    0x20060 0x80050 4 (inputRandomizerCopyState msg) (inputRandomizerCopyState_invariant msg msgpc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have randpc : rand.pc = 0x114c := by simpa [CopyInvariant] using randInv.2.2.1
  have slotPreserved (i : Fin 2) :
      rand.getMem (wordAddress 0x80020 i.val) = (0 : Word) := by
    rw [randFrame, inputRandomizerCopyState_mem, msgFrame, indexMessageCopyState_mem,
      slotOutput i]
    · intro j hj
      apply outside_copy_word (0x80020 + 8 * i.val) 0x80030 4 j
      · have := i.isLt; omega
      · decide
      · exact hj
      · have := i.isLt; left; omega
    · intro j hj
      apply outside_copy_word (0x80020 + 8 * i.val) 0x80050 4 j
      · have := i.isLt; omega
      · decide
      · exact hj
      · have := i.isLt; left; omega
  have messagePreserved (i : Fin 4) :
      rand.getMem (wordAddress 0x80030 i.val) = s.getMem (wordAddress 0 i.val) := by
    rw [randFrame, inputRandomizerCopyState_mem, msgOutput i.val i.isLt,
      indexMessageCopyState_mem, slotFrame]
    · intro j hj
      apply outside_copy_word (0 + 8 * i.val) 0x80020 2 j
      · have := i.isLt; omega
      · decide
      · exact hj
      · have := i.isLt; left; omega
    · intro j hj
      apply outside_copy_word (0x80030 + 8 * i.val) 0x80050 4 j
      · have := i.isLt; omega
      · decide
      · exact hj
      · have := i.isLt; left; omega
  have randomizerCopied (i : Fin 4) :
      rand.getMem (wordAddress 0x80050 i.val) = s.getMem (wordAddress 0x20060 i.val) := by
    rw [randOutput i.val i.isLt, inputRandomizerCopyState_mem, msgFrame,
      indexMessageCopyState_mem, slotFrame]
    · intro j hj
      apply outside_copy_word (0x20060 + 8 * i.val) 0x80020 2 j
      · have := i.isLt; omega
      · decide
      · exact hj
      · have := i.isLt; left; omega
    · intro j hj
      apply outside_copy_word (0x20060 + 8 * i.val) 0x80030 4 j
      · have := i.isLt; omega
      · decide
      · exact hj
      · have := i.isLt; left; omega
  refine ⟨indexHeaderState rand, ?_, ?_, ?_, ?_⟩
  · exact ordinary_trans image s _ _ 8 73 slotLoop
      (ordinary_trans image slot _ _ 28 45
        (ordinary_trans image slot _ _ 4 24 (indexMessageCopyState_block slot slotpc) msgLoop)
        (ordinary_trans image msg _ _ 29 16
          (ordinary_trans image msg _ _ 5 24 (inputRandomizerCopyState_block msg msgpc) randLoop)
          (indexHeaderState_block rand randpc)))
  · simp [indexHeaderState_pc, randpc]
  · intro i
    fin_cases i <;> simp only [indexHeaderState_mem]
    all_goals simp only [wordAddress, indexInputWord, Fin.val_zero, Fin.val_one, Nat.mul_zero,
      Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff,
      ↓reduceIte]
    all_goals first | rfl | simpa [wordAddress] using slotPreserved 0 | simpa [wordAddress] using slotPreserved 1 |
      simpa [wordAddress] using messagePreserved 0 | simpa [wordAddress] using messagePreserved 1 |
      simpa [wordAddress] using messagePreserved 2 | simpa [wordAddress] using messagePreserved 3 |
      simpa [wordAddress] using randomizerCopied 0 | simpa [wordAddress] using randomizerCopied 1 |
      simpa [wordAddress] using randomizerCopied 2 | simpa [wordAddress] using randomizerCopied 3
  · intro a outside
    have h0 : a ≠ 0x80000 := by simpa [wordAddress] using outside 0
    have h1 : a ≠ 0x80008 := by simpa [wordAddress] using outside 1
    have h2 : a ≠ 0x80010 := by simpa [wordAddress] using outside 2
    have h3 : a ≠ 0x80018 := by simpa [wordAddress] using outside 3
    rw [indexHeaderState_mem, if_neg h3, if_neg h2, if_neg h1, if_neg h0,
      randFrame, inputRandomizerCopyState_mem, msgFrame, indexMessageCopyState_mem, slotFrame]
    · intro j hj
      have eq : wordAddress 0x80020 j = wordAddress 0x80000 (j + 4) := by
        unfold wordAddress; congr 1; omega
      rw [eq]; exact outside ⟨j + 4, by omega⟩
    · intro j hj
      have eq : wordAddress 0x80030 j = wordAddress 0x80000 (j + 6) := by
        unfold wordAddress; congr 1; omega
      rw [eq]; exact outside ⟨j + 6, by omega⟩
    · intro j hj
      have eq : wordAddress 0x80050 j = wordAddress 0x80000 (j + 10) := by
        unfold wordAddress; congr 1; omega
      rw [eq]; exact outside ⟨j + 10, by omega⟩

#print axioms index_prepare

end SigGolfCandidate.Hypertree.GroupedBalancedSignIndexPrepare67
