import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Answer67

/-! Exact pointer/count update at the end of a verifier H4 tree round. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Tail67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def image : Image := GroupedBalancedVerifyImage67Fast2Byte.image

def UpdateCode (image : Image) : Prop :=
  Keygen.instructionAt image 0x1498 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x149c = some (.base (.ADDI .x28 .x28 0x48)) ∧
  Keygen.instructionAt image 0x14a0 = some (.base (.LD .x6 .x28 0)) ∧
  Keygen.instructionAt image 0x14a4 = some (.base (.ADDI .x6 .x6 16)) ∧
  Keygen.instructionAt image 0x14a8 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x14ac = some (.base (.ADDI .x28 .x28 0x48)) ∧
  Keygen.instructionAt image 0x14b0 = some (.base (.SD .x28 .x6 0)) ∧
  Keygen.instructionAt image 0x14b4 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x14b8 = some (.base (.ADDI .x28 .x28 0)) ∧
  Keygen.instructionAt image 0x14bc = some (.base (.LD .x6 .x28 0)) ∧
  Keygen.instructionAt image 0x14c0 = some (.base (.ADDI .x6 .x6 1)) ∧
  Keygen.instructionAt image 0x14c4 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x14c8 = some (.base (.ADDI .x28 .x28 0)) ∧
  Keygen.instructionAt image 0x14cc = some (.base (.SD .x28 .x6 0)) ∧
  Keygen.instructionAt image 0x14d0 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x14d4 = some (.base (.ADDI .x28 .x28 80)) ∧
  Keygen.instructionAt image 0x14d8 = some (.base (.LD .x6 .x28 0)) ∧
  Keygen.instructionAt image 0x14dc = some (.base (.ADDI .x6 .x6 1)) ∧
  Keygen.instructionAt image 0x14e0 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x14e4 = some (.base (.ADDI .x28 .x28 80)) ∧
  Keygen.instructionAt image 0x14e8 = some (.base (.SD .x28 .x6 0)) ∧
  Keygen.instructionAt image 0x14ec = some (.base (.ADDI .x7 .x0 10)) ∧
  Keygen.instructionAt image 0x14f0 = some (.base (.BNE .x6 .x7 (-608)))

theorem concrete_code : UpdateCode image := by
  unfold UpdateCode image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

def updateState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x48)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 16)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x48)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 80)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 80)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x7 .x0 10)
  execInstrBr s (.BNE .x6 .x7 (-608))

theorem update_block (s : MachineState) (pc : s.pc = 0x1498) :
    OrdinarySteps image s 23 (updateState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x48)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 16)
  let s5 := execInstrBr s4 (.LUI .x28 0x81)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 0x48)
  let s7 := execInstrBr s6 (.SD .x28 .x6 0)
  let s8 := execInstrBr s7 (.LUI .x28 0x81)
  let s9 := execInstrBr s8 (.ADDI .x28 .x28 0)
  let s10 := execInstrBr s9 (.LD .x6 .x28 0)
  let s11 := execInstrBr s10 (.ADDI .x6 .x6 1)
  let s12 := execInstrBr s11 (.LUI .x28 0x81)
  let s13 := execInstrBr s12 (.ADDI .x28 .x28 0)
  let s14 := execInstrBr s13 (.SD .x28 .x6 0)
  let s15 := execInstrBr s14 (.LUI .x28 0x81)
  let s16 := execInstrBr s15 (.ADDI .x28 .x28 80)
  let s17 := execInstrBr s16 (.LD .x6 .x28 0)
  let s18 := execInstrBr s17 (.ADDI .x6 .x6 1)
  let s19 := execInstrBr s18 (.LUI .x28 0x81)
  let s20 := execInstrBr s19 (.ADDI .x28 .x28 80)
  let s21 := execInstrBr s20 (.SD .x28 .x6 0)
  let s22 := execInstrBr s21 (.ADDI .x7 .x0 10)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22⟩ := concrete_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 22
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x48)) 21
  · have hp : s1.pc = 0x149c := by
      simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 20
  · have hp : s2.pc = 0x14a0 := by
      simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 16)) 19
  · have hp : s3.pc = 0x14a4 := by
      simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x81)) 18
  · have hp : s4.pc = 0x14a8 := by
      simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 0x48)) 17
  · have hp : s5.pc = 0x14ac := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x6 0)) 16
  · have hp : s6.pc = 0x14b0 := by
      simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · simp [s1,s2,s3,s4,s5,s6,s7,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x28 0x81)) 15
  · have hp : s7.pc = 0x14b4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x28 .x28 0)) 14
  · have hp : s8.pc = 0x14b8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LD .x6 .x28 0)) 13
  · have hp : s9.pc = 0x14bc := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x6 .x6 1)) 12
  · have hp : s10.pc = 0x14c0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.LUI .x28 0x81)) 11
  · have hp : s11.pc = 0x14c4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x28 .x28 0)) 10
  · have hp : s12.pc = 0x14c8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.SD .x28 .x6 0)) 9
  · have hp : s13.pc = 0x14cc := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s14 s15 _ (.base (.LUI .x28 0x81)) 8
  · have hp : s14.pc = 0x14d0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.ADDI .x28 .x28 80)) 7
  · have hp : s15.pc = 0x14d4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.LD .x6 .x28 0)) 6
  · have hp : s16.pc = 0x14d8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s17 s18 _ (.base (.ADDI .x6 .x6 1)) 5
  · have hp : s17.pc = 0x14dc := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.LUI .x28 0x81)) 4
  · have hp : s18.pc = 0x14e0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · rfl
  apply OrdinarySteps.step s19 s20 _ (.base (.ADDI .x28 .x28 80)) 3
  · have hp : s19.pc = 0x14e4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · rfl
  apply OrdinarySteps.step s20 s21 _ (.base (.SD .x28 .x6 0)) 2
  · have hp : s20.pc = 0x14e8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s21 s22 _ (.base (.ADDI .x7 .x0 10)) 1
  · have hp : s21.pc = 0x14ec := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c21
  · rfl
  apply OrdinarySteps.step s22 _ _ (.base (.BNE .x6 .x7 (-608))) 0
  · have hp : s22.pc = 0x14f0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c22
  · rfl
  exact OrdinarySteps.refl _

theorem update_pc (s : MachineState) (pc : s.pc = 0x1498) :
    (updateState s).pc =
      if (updateState s).getReg .x6 ≠ (updateState s).getReg .x7
      then 0x1290 else 0x14f4 := by
  simp [updateState,execInstrBr,pc,signExtend13,
    MachineState.getReg_setReg_ne]

theorem update_pointer (s : MachineState) :
    (updateState s).getMem 0x81048 = s.getMem 0x81048 + 16 := by
  simp [updateState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem update_round_count (s : MachineState) :
    (updateState s).getMem 0x81050 = s.getMem 0x81050 + 1 := by
  simp [updateState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem update_reg_count (s : MachineState) :
    (updateState s).getReg .x6 = s.getMem 0x81050 + 1 := by
  simp [updateState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem update_reg_limit (s : MachineState) :
    (updateState s).getReg .x7 = 10 := by
  simp [updateState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem update_pc_count (s : MachineState) (pc : s.pc = 0x1498) :
    (updateState s).pc =
      if s.getMem 0x81050 + 1 ≠ (10 : Word) then 0x1290 else 0x14f4 := by
  rw [update_pc s pc, update_reg_count, update_reg_limit]

theorem update_mem (s : MachineState) (a : Word)
    (hptr : a ≠ 0x81048) (hedge : a ≠ 0x81000)
    (hlevel : a ≠ 0x81050) :
    (updateState s).getMem a = s.getMem a := by
  simp [updateState,execInstrBr,signExtend12,
    Expansion.mem_setMem,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]
  split_ifs with e1 e2 e3
  · exact False.elim (hlevel e1)
  · exact False.elim (hedge e2)
  · exact False.elim (hptr e3)
  · rfl

theorem update_safe (s : MachineState) :
    GroupedBalancedVerifyTreeHighFrame67.SafeFrame s (updateState s) := by
  constructor
  · intro a ha
    apply update_mem s a
    all_goals
      intro eq
      have hn := congrArg BitVec.toNat eq
      simp at hn
      omega
  · simp [updateState,execInstrBr,MachineState.getReg_setReg_ne]

private abbrev program := GroupedBalancedProgram67Byte.submission

theorem loaded_first_round (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial n before final,
      initialState program .verify input = some initial ∧
      (n = 380 ∨ n = 381) ∧
      Trace hash image initial n (n+29) 3 4 final ∧
      before.pc = 0x1498 ∧
      OrdinarySteps image before 23 final ∧
      final.pc =
        (if before.getMem 0x81050 + 1 ≠ (10 : Word) then 0x1290 else 0x14f4) ∧
      final.getMem 0x81048 = 0x2c740 := by
  obtain ⟨initial,n,before,loaded,ncases,beforeRun,beforePC,pointer⟩ :=
    GroupedBalancedVerifyTreeH4Answer67.loaded_answer hash input
  let final := updateState before
  have tailRun := update_block before beforePC
  refine ⟨initial,n+23,before,final,loaded,?_,?_,beforePC,tailRun,
    update_pc_count before beforePC,?_⟩
  · rcases ncases with h | h <;> simp [h]
  · have run := beforeRun.trans tailRun.trace
    simpa [image,final,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using run
  · rw [update_pointer,pointer]
    decide

#print axioms update_block
#print axioms loaded_first_round
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Tail67
