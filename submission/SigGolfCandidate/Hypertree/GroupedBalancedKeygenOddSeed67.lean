import SigGolfCandidate.Hypertree.GroupedBalancedKeygenChainStep67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenBranch67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstLeaf67
import SigGolfCandidate.Hypertree.KeygenCopyX19

/-! Keygen's odd-chain path reuses the cached upper half of the paired H1 seed. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenOddSeed67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image
private abbrev branch := GroupedBalancedKeygenBranch67.branchState

theorem branch_odd_pc (s : MachineState) (pc : s.pc = 0x1050)
    (odd : s.getMem 0x81030 &&& 1 ≠ 0) :
    (branch s).pc = 0x1064 := by
  simp [branch,GroupedBalancedKeygenBranch67.branchState,
    execInstrBr,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact odd

theorem branch_x19 (s : MachineState) :
    (branch s).getReg .x19 = s.getMem 0x81030 := by
  simp [branch,GroupedBalancedKeygenBranch67.branchState,
    execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

def jumpState (s : MachineState) : MachineState :=
  execInstrBr s (.JAL .x0 0x110)

theorem jump_steps (s : MachineState) (pc : s.pc = 0x1064) :
    OrdinarySteps image s 1 (jumpState s) := by
  have code : Keygen.instructionAt image 0x1064 =
      some (.base (.JAL .x0 0x110)) := by
    unfold image GroupedBalancedKeygenImage67.image
    decide
  apply OrdinarySteps.step s (jumpState s) _ (.base (.JAL .x0 0x110)) 0
  · simpa only [Keygen.fetch_at,pc] using code
  · rfl
  exact OrdinarySteps.refl _

theorem jump_pc (s : MachineState) (pc : s.pc = 0x1064) :
    (jumpState s).pc = 0x1174 := by
  simp [jumpState,execInstrBr,signExtend21,pc]

theorem jump_x19 (s : MachineState) :
    (jumpState s).getReg .x19 = s.getReg .x19 := by
  simp [jumpState,execInstrBr,MachineState.getReg_setReg_ne]

theorem jump_mem (s : MachineState) (a : Word) :
    (jumpState s).getMem a = s.getMem a := by
  simp [jumpState,execInstrBr]

private abbrev leafBranch := GroupedBalancedKeygenFirstLeaf67.branchState

theorem leaf_odd_pc (s : MachineState) (pc : s.pc = 0x1174)
    (odd : s.getReg .x19 &&& 1 ≠ 0) :
    (leafBranch s).pc = 0x117c := by
  simp [leafBranch,GroupedBalancedKeygenFirstLeaf67.branchState,
    execInstrBr,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact odd

theorem leaf_x19 (s : MachineState) :
    (leafBranch s).getReg .x19 = s.getReg .x19 := by
  simp [leafBranch,GroupedBalancedKeygenFirstLeaf67.branchState,
    execInstrBr,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

def setupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x81)
  let s := execInstrBr s (.ADDI .x6 .x6 0xd10)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 32)
  execInstrBr s (.ADDI .x10 .x0 2)

private theorem setup_code :
    Keygen.instructionAt image 0x117c = some (.base (.LUI .x6 0x81)) ∧
    Keygen.instructionAt image 0x1180 = some (.base (.ADDI .x6 .x6 0xd10)) ∧
    Keygen.instructionAt image 0x1184 = some (.base (.LUI .x7 0x80)) ∧
    Keygen.instructionAt image 0x1188 = some (.base (.ADDI .x7 .x7 32)) ∧
    Keygen.instructionAt image 0x118c = some (.base (.ADDI .x10 .x0 2)) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide

theorem setup_steps (s : MachineState) (pc : s.pc = 0x117c) :
    OrdinarySteps image s 5 (setupState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x81)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0xd10)
  let s3 := execInstrBr s2 (.LUI .x7 0x80)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 32)
  obtain ⟨c0,c1,c2,c3,c4⟩ := setup_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x81)) 4
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0xd10)) 3
  · have hp : s1.pc = 0x1180 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s2.pc = 0x1184 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 32)) 1
  · have hp : s3.pc = 0x1188 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 (setupState s) _ (.base (.ADDI .x10 .x0 2)) 0
  · have hp : s4.pc = 0x118c := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem setup_fields (s : MachineState) (pc : s.pc = 0x117c) :
    (setupState s).pc = 0x1190 ∧
    (setupState s).getReg .x6 = 0x80d10 ∧
    (setupState s).getReg .x7 = 0x80020 ∧
    (setupState s).getReg .x10 = 2 ∧
    (setupState s).getReg .x19 = s.getReg .x19 := by
  simp [setupState,execInstrBr,signExtend12,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem setup_mem (s : MachineState) (a : Word) :
    (setupState s).getMem a = s.getMem a := by
  simp [setupState,execInstrBr]

theorem copy_code : Keygen.CopyCode image 0x1190 := by
  unfold Keygen.CopyCode image GroupedBalancedKeygenImage67.image
  decide

def finishState (s : MachineState) : MachineState :=
  execInstrBr s (.JAL .x0 0x30)

theorem finish_steps (s : MachineState) (pc : s.pc = 0x11a8) :
    OrdinarySteps image s 1 (finishState s) := by
  have code : Keygen.instructionAt image 0x11a8 =
      some (.base (.JAL .x0 0x30)) := by
    unfold image GroupedBalancedKeygenImage67.image
    decide
  apply OrdinarySteps.step s (finishState s) _ (.base (.JAL .x0 0x30)) 0
  · simpa only [Keygen.fetch_at,pc] using code
  · rfl
  exact OrdinarySteps.refl _

theorem finish_pc (s : MachineState) (pc : s.pc = 0x11a8) :
    (finishState s).pc = 0x11d8 := by
  simp [finishState,execInstrBr,signExtend21,pc]

theorem finish_x19 (s : MachineState) :
    (finishState s).getReg .x19 = s.getReg .x19 := by
  simp [finishState,execInstrBr,MachineState.getReg_setReg_ne]

theorem finish_mem (s : MachineState) (a : Word) :
    (finishState s).getMem a = s.getMem a := by
  simp [finishState,execInstrBr]

theorem odd_seed_from_entry (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1050)
    (odd : s.getMem 0x81030 &&& 1 ≠ 0) :
    ∃ final,
      Trace hash image s 26 26 0 0 final ∧
      final.pc = 0x11d8 ∧
      final.getReg .x19 = s.getMem 0x81030 ∧
      final.getMem 0x81030 = s.getMem 0x81030 ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      final.getMem 0x81008 = s.getMem 0x81008 := by
  let selected := branch s
  have first := GroupedBalancedKeygenBranch67.branch_steps s pc
  have selectedPC := branch_odd_pc s pc odd
  let jumped := jumpState selected
  have second := jump_steps selected selectedPC
  have jumpedPC := jump_pc selected selectedPC
  have jumpedOdd : jumped.getReg .x19 &&& 1 ≠ 0 := by
    rw [jump_x19,branch_x19]
    exact odd
  let leaf := leafBranch jumped
  have third := GroupedBalancedKeygenFirstLeaf67.branch_steps jumped jumpedPC
  have leafPC := leaf_odd_pc jumped jumpedPC jumpedOdd
  let ready := setupState leaf
  have fourth := setup_steps leaf leafPC
  obtain ⟨readyPC,readySrc,readyDst,readyCount,readyX19⟩ :=
    setup_fields leaf leafPC
  have inv : Keygen.CopyInvariant 0x1190 0x80d10 0x80020 2 2 ready := by
    refine ⟨by decide,by decide,?_,readySrc,readyDst,readyCount⟩
    simpa [ready] using readyPC
  obtain ⟨copied,fifth,done,_,frame,copyX19⟩ :=
    KeygenCopyX19.copy_all_x19 image 0x1190 copy_code
      0x80d10 0x80020 2 ready inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have copiedPC : copied.pc = 0x11a8 := by
    simpa [Keygen.CopyInvariant] using done.2.2.1
  let final := finishState copied
  have sixth := finish_steps copied copiedPC
  have finalPC := finish_pc copied copiedPC
  have finalX19 : final.getReg .x19 = s.getMem 0x81030 := by
    rw [finish_x19,copyX19,readyX19,leaf_x19,jump_x19,branch_x19]
  have finalCounter : final.getMem 0x81030 = s.getMem 0x81030 := by
    rw [finish_mem,frame 0x81030 (by intro i hi; interval_cases i <;> decide),
      setup_mem,GroupedBalancedKeygenFirstLeaf67.branch_mem,
      jump_mem,GroupedBalancedKeygenBranch67.branch_mem]
  have finalLevel : final.getMem 0x81000 = s.getMem 0x81000 := by
    rw [finish_mem,frame 0x81000 (by intro i hi; interval_cases i <;> decide),
      setup_mem,GroupedBalancedKeygenFirstLeaf67.branch_mem,
      jump_mem,GroupedBalancedKeygenBranch67.branch_mem]
  have finalLeaf : final.getMem 0x81008 = s.getMem 0x81008 := by
    rw [finish_mem,frame 0x81008 (by intro i hi; interval_cases i <;> decide),
      setup_mem,GroupedBalancedKeygenFirstLeaf67.branch_mem,
      jump_mem,GroupedBalancedKeygenBranch67.branch_mem]
  have path0 : OrdinarySteps image s 6 jumped :=
    Keygen.ordinary_trans image s selected jumped 5 1 first second
  have path1 : OrdinarySteps image s 8 leaf :=
    Keygen.ordinary_trans image s jumped leaf 6 2 path0 third
  have path2 : OrdinarySteps image s 13 ready :=
    Keygen.ordinary_trans image s leaf ready 8 5 path1 fourth
  have path3 : OrdinarySteps image s 25 copied :=
    Keygen.ordinary_trans image s ready copied 13 12 path2 fifth
  have path4 : OrdinarySteps image s 26 final :=
    Keygen.ordinary_trans image s copied final 25 1 path3 sixth
  exact ⟨final,path4.trace (hash := hash),finalPC,finalX19,
    finalCounter,finalLevel,finalLeaf⟩

#print axioms branch_odd_pc
#print axioms setup_steps
#print axioms finish_steps
#print axioms odd_seed_from_entry

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenOddSeed67
