import SigGolfCandidate.Hypertree.GroupedBalancedKeygenChainsFold67
import SigGolfCandidate.Hypertree.KeygenCopyX19

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafCopy67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafHeader67. -/
section
/-! The 67 endpoint words are copied into the H3 leaf input buffer. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafCopy67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

def setupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x81)
  let s := execInstrBr s (.ADDI .x6 .x6 (-2048))
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 32)
  execInstrBr s (.ADDI .x10 .x0 134)

private theorem setup_code :
    Keygen.instructionAt image 0x131c = some (.base (.LUI .x6 0x81)) ∧
    Keygen.instructionAt image 0x1320 = some (.base (.ADDI .x6 .x6 (-2048))) ∧
    Keygen.instructionAt image 0x1324 = some (.base (.LUI .x7 0x80)) ∧
    Keygen.instructionAt image 0x1328 = some (.base (.ADDI .x7 .x7 32)) ∧
    Keygen.instructionAt image 0x132c = some (.base (.ADDI .x10 .x0 134)) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide

theorem setup_steps (s : MachineState) (pc : s.pc = 0x131c) :
    OrdinarySteps image s 5 (setupState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x81)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 (-2048))
  let s3 := execInstrBr s2 (.LUI .x7 0x80)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 32)
  obtain ⟨c0,c1,c2,c3,c4⟩ := setup_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x81)) 4
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 (-2048))) 3
  · have hp : s1.pc = 0x1320 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s2.pc = 0x1324 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 32)) 1
  · have hp : s3.pc = 0x1328 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 (setupState s) _ (.base (.ADDI .x10 .x0 134)) 0
  · have hp : s4.pc = 0x132c := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem setup_fields (s : MachineState) (pc : s.pc = 0x131c) :
    (setupState s).pc = 0x1330 ∧
    (setupState s).getReg .x6 = 0x80800 ∧
    (setupState s).getReg .x7 = 0x80020 ∧
    (setupState s).getReg .x10 = 134 := by
  simp [setupState,execInstrBr,signExtend12,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem setup_mem (s : MachineState) (a : Word) :
    (setupState s).getMem a = s.getMem a := by
  simp [setupState,execInstrBr]

private theorem copy_code : Keygen.CopyCode image 0x1330 := by
  unfold Keygen.CopyCode image GroupedBalancedKeygenImage67.image
  decide

theorem copy_leaf_words (s : MachineState) (pc : s.pc = 0x131c) :
    ∃ final,
      OrdinarySteps image s 809 final ∧
      final.pc = 0x1348 ∧
      (∀ i, i < 134 → final.getMem (Signing.wordAddress 0x80020 i) =
        s.getMem (Signing.wordAddress 0x80800 i)) ∧
      (∀ a, (∀ i, i < 134 →
        a ≠ Signing.wordAddress 0x80020 i) → final.getMem a = s.getMem a) := by
  let ready := setupState s
  obtain ⟨readyPC,readySrc,readyDst,readyCount⟩ := setup_fields s pc
  have inv : Keygen.CopyInvariant 0x1330 0x80800 0x80020 134 134 ready := by
    refine ⟨by decide,by decide,?_,readySrc,readyDst,readyCount⟩
    simpa [ready] using readyPC
  obtain ⟨final,copied,done,words,frame,_⟩ :=
    KeygenCopyX19.copy_all_x19 image 0x1330 copy_code
      0x80800 0x80020 134 ready inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using
      Keygen.ordinary_trans image s ready final 5 (6*134)
        (setup_steps s pc) copied
  · simpa [Keygen.CopyInvariant] using done.2.2.1
  · intro i hi
    rw [words i hi,setup_mem]
  · intro a h
    rw [frame a h,setup_mem]

#print axioms copy_leaf_words

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafCopy67

end

/-! The direct67 H3 leaf header, through its oracle call. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafHeader67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
private abbrev image := GroupedBalancedKeygenImage67.image
def headerState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x10 .x0 3)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SLLI .x11 .x11 8)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.SD .x28 .x10 0)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.LUI .x10 128)
  let s := execInstrBr s (.ADDI .x10 .x10 0)
  let s := execInstrBr s (.LUI .x11 2)
  let s := execInstrBr s (.ADDI .x11 .x11 640)
  let s := execInstrBr s (.LUI .x12 128)
  let s := execInstrBr s (.ADDI .x12 .x12 768)
  execInstrBr s (.ADDI .x5 .x0 1)
private theorem header_code :
    Keygen.instructionAt image 0x1348 = some (.base (.ADDI .x10 .x0 3)) ∧
    Keygen.instructionAt image 0x134c = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1350 = some (.base (.ADDI .x28 .x28 0)) ∧
    Keygen.instructionAt image 0x1354 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x1358 = some (.base (.SLLI .x11 .x11 8)) ∧
    Keygen.instructionAt image 0x135c = some (.base (.ADD .x10 .x10 .x11)) ∧
    Keygen.instructionAt image 0x1360 = some (.base (.LUI .x28 128)) ∧
    Keygen.instructionAt image 0x1364 = some (.base (.ADDI .x28 .x28 0)) ∧
    Keygen.instructionAt image 0x1368 = some (.base (.SD .x28 .x10 0)) ∧
    Keygen.instructionAt image 0x136c = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1370 = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x1374 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x1378 = some (.base (.LUI .x28 128)) ∧
    Keygen.instructionAt image 0x137c = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x1380 = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 0x1384 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1388 = some (.base (.ADDI .x28 .x28 16)) ∧
    Keygen.instructionAt image 0x138c = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x1390 = some (.base (.LUI .x28 128)) ∧
    Keygen.instructionAt image 0x1394 = some (.base (.ADDI .x28 .x28 16)) ∧
    Keygen.instructionAt image 0x1398 = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 0x139c = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x13a0 = some (.base (.ADDI .x28 .x28 24)) ∧
    Keygen.instructionAt image 0x13a4 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x13a8 = some (.base (.LUI .x28 128)) ∧
    Keygen.instructionAt image 0x13ac = some (.base (.ADDI .x28 .x28 24)) ∧
    Keygen.instructionAt image 0x13b0 = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 0x13b4 = some (.base (.LUI .x10 128)) ∧
    Keygen.instructionAt image 0x13b8 = some (.base (.ADDI .x10 .x10 0)) ∧
    Keygen.instructionAt image 0x13bc = some (.base (.LUI .x11 2)) ∧
    Keygen.instructionAt image 0x13c0 = some (.base (.ADDI .x11 .x11 640)) ∧
    Keygen.instructionAt image 0x13c4 = some (.base (.LUI .x12 128)) ∧
    Keygen.instructionAt image 0x13c8 = some (.base (.ADDI .x12 .x12 768)) ∧
    Keygen.instructionAt image 0x13cc = some (.base (.ADDI .x5 .x0 1))
    := by
  unfold image GroupedBalancedKeygenImage67.image
  decide
theorem header_steps (s : MachineState) (pc : s.pc = 0x1348) :
    OrdinarySteps image s 34 (headerState s) := by
  let s1 := execInstrBr s (.ADDI .x10 .x0 3)
  let s2 := execInstrBr s1 (.LUI .x28 129)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0)
  let s4 := execInstrBr s3 (.LD .x11 .x28 0)
  let s5 := execInstrBr s4 (.SLLI .x11 .x11 8)
  let s6 := execInstrBr s5 (.ADD .x10 .x10 .x11)
  let s7 := execInstrBr s6 (.LUI .x28 128)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 0)
  let s9 := execInstrBr s8 (.SD .x28 .x10 0)
  let s10 := execInstrBr s9 (.LUI .x28 129)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 8)
  let s12 := execInstrBr s11 (.LD .x11 .x28 0)
  let s13 := execInstrBr s12 (.LUI .x28 128)
  let s14 := execInstrBr s13 (.ADDI .x28 .x28 8)
  let s15 := execInstrBr s14 (.SD .x28 .x11 0)
  let s16 := execInstrBr s15 (.LUI .x28 129)
  let s17 := execInstrBr s16 (.ADDI .x28 .x28 16)
  let s18 := execInstrBr s17 (.LD .x11 .x28 0)
  let s19 := execInstrBr s18 (.LUI .x28 128)
  let s20 := execInstrBr s19 (.ADDI .x28 .x28 16)
  let s21 := execInstrBr s20 (.SD .x28 .x11 0)
  let s22 := execInstrBr s21 (.LUI .x28 129)
  let s23 := execInstrBr s22 (.ADDI .x28 .x28 24)
  let s24 := execInstrBr s23 (.LD .x11 .x28 0)
  let s25 := execInstrBr s24 (.LUI .x28 128)
  let s26 := execInstrBr s25 (.ADDI .x28 .x28 24)
  let s27 := execInstrBr s26 (.SD .x28 .x11 0)
  let s28 := execInstrBr s27 (.LUI .x10 128)
  let s29 := execInstrBr s28 (.ADDI .x10 .x10 0)
  let s30 := execInstrBr s29 (.LUI .x11 2)
  let s31 := execInstrBr s30 (.ADDI .x11 .x11 640)
  let s32 := execInstrBr s31 (.LUI .x12 128)
  let s33 := execInstrBr s32 (.ADDI .x12 .x12 768)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33⟩ := header_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x10 .x0 3)) 33
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 129)) 32
  · have hp : s1.pc = 0x134c := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 31
  · have hp : s2.pc = 0x1350 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x11 .x28 0)) 30
  · have hp : s3.pc = 0x1354 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [s1,s2,s3,s4,headerState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.SLLI .x11 .x11 8)) 29
  · have hp : s4.pc = 0x1358 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADD .x10 .x10 .x11)) 28
  · have hp : s5.pc = 0x135c := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 128)) 27
  · have hp : s6.pc = 0x1360 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 0)) 26
  · have hp : s7.pc = 0x1364 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.SD .x28 .x10 0)) 25
  · have hp : s8.pc = 0x1368 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,headerState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 129)) 24
  · have hp : s9.pc = 0x136c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 8)) 23
  · have hp : s10.pc = 0x1370 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.LD .x11 .x28 0)) 22
  · have hp : s11.pc = 0x1374 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,headerState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.LUI .x28 128)) 21
  · have hp : s12.pc = 0x1378 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.ADDI .x28 .x28 8)) 20
  · have hp : s13.pc = 0x137c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.SD .x28 .x11 0)) 19
  · have hp : s14.pc = 0x1380 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,headerState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s15 s16 _ (.base (.LUI .x28 129)) 18
  · have hp : s15.pc = 0x1384 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.ADDI .x28 .x28 16)) 17
  · have hp : s16.pc = 0x1388 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.LD .x11 .x28 0)) 16
  · have hp : s17.pc = 0x138c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,headerState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s18 s19 _ (.base (.LUI .x28 128)) 15
  · have hp : s18.pc = 0x1390 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · rfl
  apply OrdinarySteps.step s19 s20 _ (.base (.ADDI .x28 .x28 16)) 14
  · have hp : s19.pc = 0x1394 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · rfl
  apply OrdinarySteps.step s20 s21 _ (.base (.SD .x28 .x11 0)) 13
  · have hp : s20.pc = 0x1398 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,headerState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s21 s22 _ (.base (.LUI .x28 129)) 12
  · have hp : s21.pc = 0x139c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c21
  · rfl
  apply OrdinarySteps.step s22 s23 _ (.base (.ADDI .x28 .x28 24)) 11
  · have hp : s22.pc = 0x13a0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c22
  · rfl
  apply OrdinarySteps.step s23 s24 _ (.base (.LD .x11 .x28 0)) 10
  · have hp : s23.pc = 0x13a4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c23
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,headerState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s24 s25 _ (.base (.LUI .x28 128)) 9
  · have hp : s24.pc = 0x13a8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c24
  · rfl
  apply OrdinarySteps.step s25 s26 _ (.base (.ADDI .x28 .x28 24)) 8
  · have hp : s25.pc = 0x13ac := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c25
  · rfl
  apply OrdinarySteps.step s26 s27 _ (.base (.SD .x28 .x11 0)) 7
  · have hp : s26.pc = 0x13b0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c26
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,headerState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s27 s28 _ (.base (.LUI .x10 128)) 6
  · have hp : s27.pc = 0x13b4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c27
  · rfl
  apply OrdinarySteps.step s28 s29 _ (.base (.ADDI .x10 .x10 0)) 5
  · have hp : s28.pc = 0x13b8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c28
  · rfl
  apply OrdinarySteps.step s29 s30 _ (.base (.LUI .x11 2)) 4
  · have hp : s29.pc = 0x13bc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c29
  · rfl
  apply OrdinarySteps.step s30 s31 _ (.base (.ADDI .x11 .x11 640)) 3
  · have hp : s30.pc = 0x13c0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c30
  · rfl
  apply OrdinarySteps.step s31 s32 _ (.base (.LUI .x12 128)) 2
  · have hp : s31.pc = 0x13c4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c31
  · rfl
  apply OrdinarySteps.step s32 s33 _ (.base (.ADDI .x12 .x12 768)) 1
  · have hp : s32.pc = 0x13c8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c32
  · rfl
  apply OrdinarySteps.step s33 (headerState s) _ (.base (.ADDI .x5 .x0 1)) 0
  · have hp : s33.pc = 0x13cc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c33
  · rfl
  exact OrdinarySteps.refl _
theorem header_pc (s : MachineState) (pc : s.pc = 0x1348) :
    (headerState s).pc = 0x13d0 := by
  simp [headerState,execInstrBr,pc]

theorem header_regs (s : MachineState) :
    (headerState s).getReg .x5 = 1 ∧
    (headerState s).getReg .x10 = 0x80000 ∧
    (headerState s).getReg .x11 = 8832 ∧
    (headerState s).getReg .x12 = 0x80300 := by
  simp [headerState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem header_high_frame (s : MachineState) (a : Word)
    (high : 0x81000 ≤ a.toNat) :
    (headerState s).getMem a = s.getMem a := by
  have h0 : a ≠ 0x80000#64 := by
    intro eq
    rw [eq] at high
    norm_num at high
  have h8 : a ≠ 0x80008#64 := by
    intro eq
    rw [eq] at high
    norm_num at high
  have h10 : a ≠ 0x80010#64 := by
    intro eq
    rw [eq] at high
    norm_num at high
  have h18 : a ≠ 0x80018#64 := by
    intro eq
    rw [eq] at high
    norm_num at high
  simp [headerState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    h0,h8,h10,h18]

#print axioms header_steps
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafHeader67
