import SigGolfCandidate.Hypertree.GroupedBalancedVerifyFirstCopy67

/-! The verifier's second copy loads the first four witness words into H5 scratch. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifySecondCopy67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

def setupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x2c)
  let s := execInstrBr s (.ADDI .x6 .x6 0x700)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x50)
  execInstrBr s (.ADDI .x10 .x0 4)

private theorem setup_code :
    Keygen.instructionAt image 0x108c = some (.base (.LUI .x6 0x2c)) ∧
    Keygen.instructionAt image 0x1090 = some (.base (.ADDI .x6 .x6 0x700)) ∧
    Keygen.instructionAt image 0x1094 = some (.base (.LUI .x7 0x80)) ∧
    Keygen.instructionAt image 0x1098 = some (.base (.ADDI .x7 .x7 0x50)) ∧
    Keygen.instructionAt image 0x109c = some (.base (.ADDI .x10 .x0 4)) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

theorem setup_steps (s : MachineState) (pc : s.pc = 0x108c) :
    OrdinarySteps image s 5 (setupState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x2c)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x700)
  let s3 := execInstrBr s2 (.LUI .x7 0x80)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0x50)
  obtain ⟨c0,c1,c2,c3,c4⟩ := setup_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x2c)) 4
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x700)) 3
  · have hp : s1.pc = 0x1090 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s2.pc = 0x1094 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0x50)) 1
  · have hp : s3.pc = 0x1098 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 (setupState s) _ (.base (.ADDI .x10 .x0 4)) 0
  · have hp : s4.pc = 0x109c := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem setup_pc (s : MachineState) (pc : s.pc = 0x108c) :
    (setupState s).pc = 0x10a0 := by
  simp [setupState,execInstrBr,pc]

theorem setup_regs (s : MachineState) :
    (setupState s).getReg .x6 = 0x2c700 ∧
    (setupState s).getReg .x7 = 0x80050 ∧
    (setupState s).getReg .x10 = 4 := by
  simp [setupState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem setup_mem (s : MachineState) (a : Word) :
    (setupState s).getMem a = s.getMem a := by
  simp [setupState,execInstrBr]

private theorem copy_code : Keygen.CopyCode image 0x10a0 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

theorem from_first (s : MachineState) (pc : s.pc = 0x108c) :
    ∃ final, OrdinarySteps image s 29 final ∧ final.pc = 0x10b8 ∧
      (∀ i, i < 4 → final.getMem (Signing.wordAddress 0x80050 i) =
        (setupState s).getMem (Signing.wordAddress 0x2c700 i)) ∧
      final.getReg .x2 = s.getReg .x2 ∧
      final.getMem 0x81048 = s.getMem 0x81048 := by
  let setup := setupState s
  have setupRun := setup_steps s pc
  obtain ⟨src,dst,count⟩ := setup_regs s
  have inv : Keygen.CopyInvariant 0x10a0 0x2c700 0x80050 4 4 setup := by
    simp [Keygen.CopyInvariant,setup,setup_pc s pc,src,dst,count]
  obtain ⟨final,copyRun,done,words,frame,_,sp⟩ :=
    Keygen.copy_all_frame image 0x10a0 copy_code 0x2c700 0x80050 4 setup inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_,_,endPC,_,_,_⟩ := done
  refine ⟨final,?_,by simpa using endPC,words,?_,?_⟩
  · simpa only [Nat.reduceAdd] using Keygen.ordinary_trans image s setup final
      5 24 setupRun copyRun
  · have setupSp : setup.getReg .x2 = s.getReg .x2 := by
      simp [setup,setupState,execInstrBr,MachineState.getReg_setReg_ne]
    exact sp.trans setupSp
  · have outside : ∀ i, i < 4 → (0x81048 : Word) ≠
        Signing.wordAddress 0x80050 i := by
      intro i hi
      interval_cases i <;> decide
    exact (frame 0x81048 outside).trans (setup_mem s 0x81048)

theorem from_loaded (hash : Hash)
    (input : Input GroupedBalancedProgram67Byte.submission.sizes .verify) :
    ∃ initial final,
      initialState GroupedBalancedProgram67Byte.submission .verify input = some initial ∧
      Trace hash image initial 82 82 0 0 final ∧ final.pc = 0x10b8 ∧
      final.getMem 0x81048 = 0x2c720 := by
  obtain ⟨initial,before,loaded,firstTrace,firstPC,_,pointer⟩ :=
    GroupedBalancedVerifyFirstCopy67.from_loaded hash input
  obtain ⟨final,secondRun,finalPC,_,_,frame⟩ := from_first before firstPC
  refine ⟨initial,final,loaded,?_,finalPC,frame.trans pointer⟩
  simpa only [Nat.reduceAdd] using firstTrace.trans secondRun.trace

#print axioms from_loaded
end SigGolfCandidate.Hypertree.GroupedBalancedVerifySecondCopy67
