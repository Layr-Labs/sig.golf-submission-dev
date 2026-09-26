import SigGolfCandidate.Hypertree.GroupedBalancedByteFastPrologue67

/-! Fast2's special-radix selector for chains 65 and 66. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastLimit67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.Keygen
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixLoop67
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

def SelectCode (image : Image) : Prop :=
  instructionAt image 0x1660 = some (.base (.ADDI .x7 .x0 65)) ∧
  instructionAt image 0x1664 = some (.base (.BEQ .x23 .x7 16)) ∧
  instructionAt image 0x1668 = some (.base (.ADDI .x7 .x0 66)) ∧
  instructionAt image 0x166c = some (.base (.BEQ .x23 .x7 16)) ∧
  instructionAt image 0x1674 = some (.base (.ADDI .x20 .x0 8)) ∧
  instructionAt image 0x1678 = some (.base (.JAL .x0 (-112))) ∧
  instructionAt image 0x167c = some (.base (.ADDI .x20 .x0 10)) ∧
  instructionAt image 0x1680 = some (.base (.JAL .x0 (-120)))

theorem concrete_code : SelectCode image := by
  unfold SelectCode image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

def select65State (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x7 .x0 65)
  let s := execInstrBr s (.BEQ .x23 .x7 16)
  let s := execInstrBr s (.ADDI .x20 .x0 8)
  execInstrBr s (.JAL .x0 (-112))

def select66State (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x7 .x0 65)
  let s := execInstrBr s (.BEQ .x23 .x7 16)
  let s := execInstrBr s (.ADDI .x7 .x0 66)
  let s := execInstrBr s (.BEQ .x23 .x7 16)
  let s := execInstrBr s (.ADDI .x20 .x0 10)
  execInstrBr s (.JAL .x0 (-120))

theorem select65_block (s : MachineState)
    (pc : s.pc = 0x1660) (chain : s.getReg .x23 = 65) :
    OrdinarySteps image s 4 (select65State s) := by
  let s1 := execInstrBr s (.ADDI .x7 .x0 65)
  let s2 := execInstrBr s1 (.BEQ .x23 .x7 16)
  let s3 := execInstrBr s2 (.ADDI .x20 .x0 8)
  change OrdinarySteps image s 4 (execInstrBr s3 (.JAL .x0 (-112)))
  rcases concrete_code with ⟨c0,c1,_,_,c4,c5,_,_⟩
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x7 .x0 65)) 3
  · simpa only [fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.BEQ .x23 .x7 16)) 2
  · have hp : s1.pc = 0x1664 := by simp [s1,execInstrBr,pc]
    simpa only [fetch_at,hp] using c1
  · rfl
  have cmp : s1.getReg .x23 = s1.getReg .x7 := by
    simp [s1,execInstrBr,signExtend12,chain,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  have hp2 : s2.pc = 0x1674 := by
    simp [s2,execInstrBr,cmp,signExtend13,
      show s1.pc = 0x1664 by simp [s1,execInstrBr,pc]]
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x20 .x0 8)) 1
  · simpa only [fetch_at,hp2] using c4
  · rfl
  apply OrdinarySteps.step s3 (execInstrBr s3 (.JAL .x0 (-112))) _
    (.base (.JAL .x0 (-112))) 0
  · have hp : s3.pc = 0x1678 := by simp [s3,execInstrBr,hp2]
    simpa only [fetch_at,hp] using c5
  · rfl
  exact OrdinarySteps.refl _

theorem select65_pc (s : MachineState) (pc : s.pc = 0x1660)
    (chain : s.getReg .x23 = 65) :
    (select65State s).pc = 0x1608 := by
  simp [select65State,execInstrBr,pc,chain,signExtend12,signExtend13,
    signExtend21,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem select65_limit (s : MachineState) :
    (select65State s).getReg .x20 = 8 := by
  simp [select65State,execInstrBr,
    signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem select66_block (s : MachineState)
    (pc : s.pc = 0x1660) (chain : s.getReg .x23 = 66) :
    OrdinarySteps image s 6 (select66State s) := by
  let s1 := execInstrBr s (.ADDI .x7 .x0 65)
  let s2 := execInstrBr s1 (.BEQ .x23 .x7 16)
  let s3 := execInstrBr s2 (.ADDI .x7 .x0 66)
  let s4 := execInstrBr s3 (.BEQ .x23 .x7 16)
  let s5 := execInstrBr s4 (.ADDI .x20 .x0 10)
  change OrdinarySteps image s 6 (execInstrBr s5 (.JAL .x0 (-120)))
  rcases concrete_code with ⟨c0,c1,c2,c3,_,_,c6,c7⟩
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x7 .x0 65)) 5
  · simpa only [fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.BEQ .x23 .x7 16)) 4
  · have hp : s1.pc = 0x1664 := by simp [s1,execInstrBr,pc]
    simpa only [fetch_at,hp] using c1
  · rfl
  have notCmp : s1.getReg .x23 ≠ s1.getReg .x7 := by
    simp [s1,execInstrBr,signExtend12,chain,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  have hp2 : s2.pc = 0x1668 := by
    simp [s2,execInstrBr,notCmp,
      show s1.pc = 0x1664 by simp [s1,execInstrBr,pc]]
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x7 .x0 66)) 3
  · simpa only [fetch_at,hp2] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.BEQ .x23 .x7 16)) 2
  · have hp : s3.pc = 0x166c := by simp [s3,execInstrBr,hp2]
    simpa only [fetch_at,hp] using c3
  · rfl
  have cmp : s3.getReg .x23 = s3.getReg .x7 := by
    simp [s1,s2,s3,execInstrBr,signExtend12,chain,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  have hp4 : s4.pc = 0x167c := by
    simp [s4,execInstrBr,cmp,signExtend13,
      show s3.pc = 0x166c by simp [s3,execInstrBr,hp2]]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x20 .x0 10)) 1
  · simpa only [fetch_at,hp4] using c6
  · rfl
  apply OrdinarySteps.step s5 (execInstrBr s5 (.JAL .x0 (-120))) _
    (.base (.JAL .x0 (-120))) 0
  · have hp : s5.pc = 0x1680 := by simp [s5,execInstrBr,hp4]
    simpa only [fetch_at,hp] using c7
  · rfl
  exact OrdinarySteps.refl _

theorem select66_pc (s : MachineState) (pc : s.pc = 0x1660)
    (chain : s.getReg .x23 = 66) :
    (select66State s).pc = 0x1608 := by
  simp [select66State,execInstrBr,pc,chain,signExtend12,signExtend13,
    signExtend21,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem select66_limit (s : MachineState) :
    (select66State s).getReg .x20 = 10 := by
  simp [select66State,execInstrBr,
    signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

def AdvanceCode (image : Image) : Prop :=
  instructionAt image 0x1654 = some (.base (.ADDI .x23 .x23 1)) ∧
  instructionAt image 0x1658 = some (.base (.SLTIU .x7 .x23 65)) ∧
  instructionAt image 0x165c = some (.base (.BNE .x7 .x0 (-84)))

theorem concrete_advance_code : AdvanceCode image := by
  unfold AdvanceCode image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

def advanceState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x23 .x23 1)
  let s := execInstrBr s (.SLTIU .x7 .x23 65)
  execInstrBr s (.BNE .x7 .x0 (-84))

theorem advance_block (s : MachineState) (pc : s.pc = 0x1654) :
    OrdinarySteps image s 3 (advanceState s) := by
  let s1 := execInstrBr s (.ADDI .x23 .x23 1)
  let s2 := execInstrBr s1 (.SLTIU .x7 .x23 65)
  change OrdinarySteps image s 3 (execInstrBr s2 (.BNE .x7 .x0 (-84)))
  obtain ⟨c0,c1,c2⟩ := concrete_advance_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x23 .x23 1)) 2
  · simpa only [fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.SLTIU .x7 .x23 65)) 1
  · have hp : s1.pc = 0x1658 := by simp [s1,execInstrBr,pc]
    simpa only [fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 (execInstrBr s2 (.BNE .x7 .x0 (-84))) _
    (.base (.BNE .x7 .x0 (-84))) 0
  · have hp : s2.pc = 0x165c := by simp [s1,s2,execInstrBr,pc]
    simpa only [fetch_at,hp] using c2
  · rfl
  exact OrdinarySteps.refl _

theorem advance_chain (s : MachineState) (chain : Nat)
    (reg : s.getReg .x23 = BitVec.ofNat 64 chain) :
    (advanceState s).getReg .x23 = BitVec.ofNat 64 (chain + 1) := by
  simp [advanceState,execInstrBr,reg,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact (BitVec.ofNat_add chain 1).symm

theorem advance_limit (s : MachineState) :
    (advanceState s).getReg .x20 = s.getReg .x20 := by
  simp [advanceState,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem advance_reg_stable (s : MachineState) (r : Reg)
    (h23 : r ≠ .x23) (h7 : r ≠ .x7) :
    (advanceState s).getReg r = s.getReg r := by
  have n23 : .x23 ≠ r := Ne.symm h23
  have n7 : .x7 ≠ r := Ne.symm h7
  simp [advanceState,execInstrBr,MachineState.getReg_setReg_ne,
    n23,n7]

theorem advance_short_pc (s : MachineState) (chain : Nat)
    (pc : s.pc = 0x1654)
    (reg : s.getReg .x23 = BitVec.ofNat 64 chain)
    (bound : chain < 64) :
    (advanceState s).pc = 0x1608 := by
  simp [advanceState,execInstrBr,pc,reg,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq]
  interval_cases chain <;> decide

theorem advance_special_pc (s : MachineState) (chain : Nat)
    (pc : s.pc = 0x1654)
    (reg : s.getReg .x23 = BitVec.ofNat 64 chain)
    (special : chain = 64 ∨ chain = 65) :
    (advanceState s).pc = 0x1660 := by
  rcases special with rfl | rfl <;>
    simp [advanceState,execInstrBr,pc,reg,signExtend12,
      MachineState.getReg_setReg_eq]

theorem advance_mem (s : MachineState) (a : Word) :
    (advanceState s).getMem a = s.getMem a := by
  simp [advanceState,execInstrBr]

theorem select65_mem (s : MachineState) (a : Word) :
    (select65State s).getMem a = s.getMem a := by
  simp [select65State,execInstrBr]

theorem select66_mem (s : MachineState) (a : Word) :
    (select66State s).getMem a = s.getMem a := by
  simp [select66State,execInstrBr]

theorem select65_chain (s : MachineState) :
    (select65State s).getReg .x23 = s.getReg .x23 := by
  simp [select65State,execInstrBr,MachineState.getReg_setReg_ne]

theorem select66_chain (s : MachineState) :
    (select66State s).getReg .x23 = s.getReg .x23 := by
  simp [select66State,execInstrBr,MachineState.getReg_setReg_ne]

theorem select65_reg_stable (s : MachineState) (r : Reg)
    (h7 : r ≠ .x7) (h20 : r ≠ .x20) (h0 : r ≠ .x0) :
    (select65State s).getReg r = s.getReg r := by
  have n7 : .x7 ≠ r := Ne.symm h7
  have n20 : .x20 ≠ r := Ne.symm h20
  have n0 : .x0 ≠ r := Ne.symm h0
  simp [select65State,execInstrBr,MachineState.getReg_setReg_ne,
    n7,n20,n0]

theorem select66_reg_stable (s : MachineState) (r : Reg)
    (h7 : r ≠ .x7) (h20 : r ≠ .x20) (h0 : r ≠ .x0) :
    (select66State s).getReg r = s.getReg r := by
  have n7 : .x7 ≠ r := Ne.symm h7
  have n20 : .x20 ≠ r := Ne.symm h20
  have n0 : .x0 ≠ r := Ne.symm h0
  simp [select66State,execInstrBr,MachineState.getReg_setReg_ne,
    n7,n20,n0]

def next65State (s : MachineState) : MachineState :=
  select65State (advanceState s)

def next66State (s : MachineState) : MachineState :=
  select66State (advanceState s)

theorem next65_block (s : MachineState)
    (pc : s.pc = 0x1654) (chain : s.getReg .x23 = 64) :
    OrdinarySteps image s 7 (next65State s) := by
  have first := advance_block s pc
  have midPC : (advanceState s).pc = 0x1660 :=
    advance_special_pc s 64 pc chain (Or.inl rfl)
  have midChain : (advanceState s).getReg .x23 = 65 := by
    simpa using advance_chain s 64 chain
  have second := select65_block (advanceState s) midPC midChain
  simpa [next65State] using ordinary_trans image s (advanceState s)
    (select65State (advanceState s)) 3 4 first second

theorem next65_pc (s : MachineState)
    (pc : s.pc = 0x1654) (chain : s.getReg .x23 = 64) :
    (next65State s).pc = 0x1608 := by
  have midPC := advance_special_pc s 64 pc chain (Or.inl rfl)
  have midChain : (advanceState s).getReg .x23 = 65 := by
    simpa using advance_chain s 64 chain
  exact select65_pc (advanceState s) midPC midChain

theorem next65_limit (s : MachineState) :
    (next65State s).getReg .x20 =
      BitVec.ofNat 64 (GroupedBalancedChecksum67.maxDigit (65 : Fin 67)) := by
  simpa [next65State,GroupedBalancedChecksum67.maxDigit] using
    select65_limit (advanceState s)

theorem next65_chain (s : MachineState) (chain : s.getReg .x23 = 64) :
    (next65State s).getReg .x23 = 65 := by
  rw [next65State,select65_chain]
  simpa using advance_chain s 64 chain

theorem next65_reg_stable (s : MachineState) (r : Reg)
    (h23 : r ≠ .x23) (h7 : r ≠ .x7) (h20 : r ≠ .x20)
    (h0 : r ≠ .x0) :
    (next65State s).getReg r = s.getReg r := by
  rw [next65State,select65_reg_stable _ r h7 h20 h0,
    advance_reg_stable _ r h23 h7]

theorem next65_mem (s : MachineState) (a : Word) :
    (next65State s).getMem a = s.getMem a := by
  rw [next65State,select65_mem,advance_mem]

theorem next66_block (s : MachineState)
    (pc : s.pc = 0x1654) (chain : s.getReg .x23 = 65) :
    OrdinarySteps image s 9 (next66State s) := by
  have first := advance_block s pc
  have midPC : (advanceState s).pc = 0x1660 :=
    advance_special_pc s 65 pc chain (Or.inr rfl)
  have midChain : (advanceState s).getReg .x23 = 66 := by
    simpa using advance_chain s 65 chain
  have second := select66_block (advanceState s) midPC midChain
  simpa [next66State] using ordinary_trans image s (advanceState s)
    (select66State (advanceState s)) 3 6 first second

theorem next66_pc (s : MachineState)
    (pc : s.pc = 0x1654) (chain : s.getReg .x23 = 65) :
    (next66State s).pc = 0x1608 := by
  have midPC := advance_special_pc s 65 pc chain (Or.inr rfl)
  have midChain : (advanceState s).getReg .x23 = 66 := by
    simpa using advance_chain s 65 chain
  exact select66_pc (advanceState s) midPC midChain

theorem next66_limit (s : MachineState) :
    (next66State s).getReg .x20 =
      BitVec.ofNat 64 (GroupedBalancedChecksum67.maxDigit (66 : Fin 67)) := by
  simpa [next66State,GroupedBalancedChecksum67.maxDigit] using
    select66_limit (advanceState s)

theorem next66_chain (s : MachineState) (chain : s.getReg .x23 = 65) :
    (next66State s).getReg .x23 = 66 := by
  rw [next66State,select66_chain]
  simpa using advance_chain s 65 chain

theorem next66_reg_stable (s : MachineState) (r : Reg)
    (h23 : r ≠ .x23) (h7 : r ≠ .x7) (h20 : r ≠ .x20)
    (h0 : r ≠ .x0) :
    (next66State s).getReg r = s.getReg r := by
  rw [next66State,select66_reg_stable _ r h7 h20 h0,
    advance_reg_stable _ r h23 h7]

theorem next66_mem (s : MachineState) (a : Word) :
    (next66State s).getMem a = s.getMem a := by
  rw [next66State,select66_mem,advance_mem]

def selectDoneState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x7 .x0 65)
  let s := execInstrBr s (.BEQ .x23 .x7 16)
  let s := execInstrBr s (.ADDI .x7 .x0 66)
  let s := execInstrBr s (.BEQ .x23 .x7 16)
  execInstrBr s (.JAL .x0 20)

theorem select_done_code :
    instructionAt image 0x1670 = some (.base (.JAL .x0 20)) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

theorem select_done_block (s : MachineState)
    (pc : s.pc = 0x1660) (chain : s.getReg .x23 = 67) :
    OrdinarySteps image s 5 (selectDoneState s) := by
  let s1 := execInstrBr s (.ADDI .x7 .x0 65)
  let s2 := execInstrBr s1 (.BEQ .x23 .x7 16)
  let s3 := execInstrBr s2 (.ADDI .x7 .x0 66)
  let s4 := execInstrBr s3 (.BEQ .x23 .x7 16)
  change OrdinarySteps image s 5 (execInstrBr s4 (.JAL .x0 20))
  rcases concrete_code with ⟨c0,c1,c2,c3,_,_,_,_⟩
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x7 .x0 65)) 4
  · simpa only [fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.BEQ .x23 .x7 16)) 3
  · have hp : s1.pc = 0x1664 := by simp [s1,execInstrBr,pc]
    simpa only [fetch_at,hp] using c1
  · rfl
  have not65 : s1.getReg .x23 ≠ s1.getReg .x7 := by
    simp [s1,execInstrBr,signExtend12,chain,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  have hp2 : s2.pc = 0x1668 := by
    simp [s2,execInstrBr,not65,
      show s1.pc = 0x1664 by simp [s1,execInstrBr,pc]]
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x7 .x0 66)) 2
  · simpa only [fetch_at,hp2] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.BEQ .x23 .x7 16)) 1
  · have hp : s3.pc = 0x166c := by simp [s3,execInstrBr,hp2]
    simpa only [fetch_at,hp] using c3
  · rfl
  have not66 : s3.getReg .x23 ≠ s3.getReg .x7 := by
    simp [s1,s2,s3,execInstrBr,signExtend12,chain,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  have hp4 : s4.pc = 0x1670 := by
    simp [s4,execInstrBr,not66,
      show s3.pc = 0x166c by simp [s3,execInstrBr,hp2]]
  apply OrdinarySteps.step s4 (execInstrBr s4 (.JAL .x0 20)) _
    (.base (.JAL .x0 20)) 0
  · simpa only [fetch_at,hp4] using select_done_code
  · rfl
  exact OrdinarySteps.refl _

theorem select_done_pc (s : MachineState) (pc : s.pc = 0x1660)
    (chain : s.getReg .x23 = 67) :
    (selectDoneState s).pc = 0x1684 := by
  simp [selectDoneState,execInstrBr,pc,chain,signExtend12,
    signExtend21,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem select_done_mem (s : MachineState) (a : Word) :
    (selectDoneState s).getMem a = s.getMem a := by
  simp [selectDoneState,execInstrBr]

theorem select_done_chain (s : MachineState) :
    (selectDoneState s).getReg .x23 = s.getReg .x23 := by
  simp [selectDoneState,execInstrBr,MachineState.getReg_setReg_ne]

theorem select_done_reg_stable (s : MachineState) (r : Reg)
    (h7 : r ≠ .x7) (h0 : r ≠ .x0) :
    (selectDoneState s).getReg r = s.getReg r := by
  have n7 : .x7 ≠ r := Ne.symm h7
  have n0 : .x0 ≠ r := Ne.symm h0
  simp [selectDoneState,execInstrBr,MachineState.getReg_setReg_ne,
    n7,n0]

def nextDoneState (s : MachineState) : MachineState :=
  selectDoneState (advanceState s)

theorem next_done_block (s : MachineState)
    (pc : s.pc = 0x1654) (chain : s.getReg .x23 = 66) :
    OrdinarySteps image s 8 (nextDoneState s) := by
  have first := advance_block s pc
  have midPC : (advanceState s).pc = 0x1660 := by
    simp [advanceState,execInstrBr,pc,chain,signExtend12,
      MachineState.getReg_setReg_eq]
  have midChain : (advanceState s).getReg .x23 = 67 := by
    simpa using advance_chain s 66 chain
  have second := select_done_block (advanceState s) midPC midChain
  simpa [nextDoneState] using ordinary_trans image s (advanceState s)
    (selectDoneState (advanceState s)) 3 5 first second

theorem next_done_pc (s : MachineState)
    (pc : s.pc = 0x1654) (chain : s.getReg .x23 = 66) :
    (nextDoneState s).pc = 0x1684 := by
  have midPC : (advanceState s).pc = 0x1660 := by
    simp [advanceState,execInstrBr,pc,chain,signExtend12,
      MachineState.getReg_setReg_eq]
  have midChain : (advanceState s).getReg .x23 = 67 := by
    simpa using advance_chain s 66 chain
  exact select_done_pc (advanceState s) midPC midChain

theorem next_done_mem (s : MachineState) (a : Word) :
    (nextDoneState s).getMem a = s.getMem a := by
  rw [nextDoneState,select_done_mem,advance_mem]

theorem next_done_chain (s : MachineState)
    (chain : s.getReg .x23 = 66) :
    (nextDoneState s).getReg .x23 = 67 := by
  rw [nextDoneState,select_done_chain]
  simpa using advance_chain s 66 chain

theorem next_done_reg_stable (s : MachineState) (r : Reg)
    (h23 : r ≠ .x23) (h7 : r ≠ .x7) (h0 : r ≠ .x0) :
    (nextDoneState s).getReg r = s.getReg r := by
  rw [nextDoneState,select_done_reg_stable _ r h7 h0,
    advance_reg_stable _ r h23 h7]

def InitialCode (image : Image) : Prop :=
  instructionAt image 0x15ec = some (.base (.ADDI .x20 .x0 3)) ∧
  instructionAt image 0x15f0 = some (.base (.LUI .x10 0x90)) ∧
  instructionAt image 0x15f4 = some (.base (.ADDI .x10 .x10 0)) ∧
  instructionAt image 0x15f8 = some (.base (.ADDI .x11 .x0 384)) ∧
  instructionAt image 0x15fc = some (.base (.LUI .x12 0x90)) ∧
  instructionAt image 0x1600 = some (.base (.ADDI .x12 .x12 32)) ∧
  instructionAt image 0x1604 = some (.base (.ADDI .x5 .x0 1))

theorem concrete_initial_code : InitialCode image := by
  unfold InitialCode image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

def initialState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x20 .x0 3)
  let s := execInstrBr s (.LUI .x10 0x90)
  let s := execInstrBr s (.ADDI .x10 .x10 0)
  let s := execInstrBr s (.ADDI .x11 .x0 384)
  let s := execInstrBr s (.LUI .x12 0x90)
  let s := execInstrBr s (.ADDI .x12 .x12 32)
  execInstrBr s (.ADDI .x5 .x0 1)

theorem initial_block (s : MachineState) (pc : s.pc = 0x15ec) :
    OrdinarySteps image s 7 (initialState s) := by
  let s1 := execInstrBr s (.ADDI .x20 .x0 3)
  let s2 := execInstrBr s1 (.LUI .x10 0x90)
  let s3 := execInstrBr s2 (.ADDI .x10 .x10 0)
  let s4 := execInstrBr s3 (.ADDI .x11 .x0 384)
  let s5 := execInstrBr s4 (.LUI .x12 0x90)
  let s6 := execInstrBr s5 (.ADDI .x12 .x12 32)
  change OrdinarySteps image s 7 (execInstrBr s6 (.ADDI .x5 .x0 1))
  obtain ⟨c0,c1,c2,c3,c4,c5,c6⟩ := concrete_initial_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x20 .x0 3)) 6
  · simpa only [fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x10 0x90)) 5
  · have hp : s1.pc = 0x15f0 := by simp [s1,execInstrBr,pc]
    simpa only [fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x10 .x10 0)) 4
  · have hp : s2.pc = 0x15f4 := by simp [s1,s2,execInstrBr,pc]
    simpa only [fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x11 .x0 384)) 3
  · have hp : s3.pc = 0x15f8 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x12 0x90)) 2
  · have hp : s4.pc = 0x15fc := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x12 .x12 32)) 1
  · have hp : s5.pc = 0x1600 := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 (execInstrBr s6 (.ADDI .x5 .x0 1)) _
    (.base (.ADDI .x5 .x0 1)) 0
  · have hp : s6.pc = 0x1604 := by
      simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [fetch_at,hp] using c6
  · rfl
  exact OrdinarySteps.refl _

theorem initial_pc (s : MachineState) (pc : s.pc = 0x15ec) :
    (initialState s).pc = 0x1608 := by
  simp [initialState,execInstrBr,pc]

theorem initial_fields (s : MachineState) :
    (initialState s).getReg .x20 = 3 ∧
    (initialState s).getReg .x10 = 0x90000 ∧
    (initialState s).getReg .x11 = 384 ∧
    (initialState s).getReg .x12 = 0x90020 ∧
    (initialState s).getReg .x5 = 1 := by
  simp [initialState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem initial_mem (s : MachineState) (a : Word) :
    (initialState s).getMem a = s.getMem a := by
  simp [initialState,execInstrBr]

theorem initial_chain_digit_ptr (s : MachineState) :
    (initialState s).getReg .x23 = s.getReg .x23 ∧
    (initialState s).getReg .x25 = s.getReg .x25 := by
  simp [initialState,execInstrBr,MachineState.getReg_setReg_ne]

def PointerCode (image : Image) : Prop :=
  instructionAt image 0x15d8 = some (.base (.ADDI .x23 .x0 0)) ∧
  instructionAt image 0x15dc = some (.base (.LUI .x24 0x80)) ∧
  instructionAt image 0x15e0 = some (.base (.ADDI .x24 .x24 32)) ∧
  instructionAt image 0x15e4 = some (.base (.LUI .x25 0x80)) ∧
  instructionAt image 0x15e8 = some (.base (.ADDI .x25 .x25 0x600))

theorem concrete_pointer_code : PointerCode image := by
  unfold PointerCode image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

def pointerState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x23 .x0 0)
  let s := execInstrBr s (.LUI .x24 0x80)
  let s := execInstrBr s (.ADDI .x24 .x24 32)
  let s := execInstrBr s (.LUI .x25 0x80)
  execInstrBr s (.ADDI .x25 .x25 0x600)

theorem pointer_block (s : MachineState) (pc : s.pc = 0x15d8) :
    OrdinarySteps image s 5 (pointerState s) := by
  let s1 := execInstrBr s (.ADDI .x23 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x24 0x80)
  let s3 := execInstrBr s2 (.ADDI .x24 .x24 32)
  let s4 := execInstrBr s3 (.LUI .x25 0x80)
  change OrdinarySteps image s 5
    (execInstrBr s4 (.ADDI .x25 .x25 0x600))
  obtain ⟨c0,c1,c2,c3,c4⟩ := concrete_pointer_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x23 .x0 0)) 4
  · simpa only [fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x24 0x80)) 3
  · have hp : s1.pc = 0x15dc := by simp [s1,execInstrBr,pc]
    simpa only [fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x24 .x24 32)) 2
  · have hp : s2.pc = 0x15e0 := by simp [s1,s2,execInstrBr,pc]
    simpa only [fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x25 0x80)) 1
  · have hp : s3.pc = 0x15e4 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4
    (execInstrBr s4 (.ADDI .x25 .x25 0x600)) _
    (.base (.ADDI .x25 .x25 0x600)) 0
  · have hp : s4.pc = 0x15e8 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [fetch_at,hp] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem pointer_pc (s : MachineState) (pc : s.pc = 0x15d8) :
    (pointerState s).pc = 0x15ec := by
  simp [pointerState,execInstrBr,pc]

theorem pointer_fields (s : MachineState) :
    (pointerState s).getReg .x23 = 0 ∧
    (pointerState s).getReg .x24 = 0x80020 ∧
    (pointerState s).getReg .x25 = 0x80600 := by
  simp [pointerState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem pointer_mem (s : MachineState) (a : Word) :
    (pointerState s).getMem a = s.getMem a := by
  simp [pointerState,execInstrBr]

def initialChainState (s : MachineState) : MachineState :=
  initialState (pointerState s)

theorem initial_chain_block (s : MachineState) (pc : s.pc = 0x15d8) :
    OrdinarySteps image s 12 (initialChainState s) := by
  have first := pointer_block s pc
  have second := initial_block (pointerState s) (pointer_pc s pc)
  simpa [initialChainState] using ordinary_trans image s
    (pointerState s) (initialState (pointerState s)) 5 7 first second

theorem initial_chain_pc (s : MachineState) (pc : s.pc = 0x15d8) :
    (initialChainState s).pc = 0x1608 :=
  initial_pc (pointerState s) (pointer_pc s pc)

theorem initial_chain_fields (s : MachineState) :
    (initialChainState s).getReg .x23 = 0 ∧
    (initialChainState s).getReg .x24 = 0x80020 ∧
    (initialChainState s).getReg .x25 = 0x80600 ∧
    (initialChainState s).getReg .x20 = 3 ∧
    (initialChainState s).getReg .x10 = 0x90000 ∧
    (initialChainState s).getReg .x11 = 384 ∧
    (initialChainState s).getReg .x12 = 0x90020 ∧
    (initialChainState s).getReg .x5 = 1 := by
  obtain ⟨chain,_,ptr⟩ := pointer_fields s
  obtain ⟨limit,src,len,dst,service⟩ := initial_fields (pointerState s)
  have p24 : (initialState (pointerState s)).getReg .x24 =
      (pointerState s).getReg .x24 := by
    simp [initialState,execInstrBr,MachineState.getReg_setReg_ne]
  simp only [initialChainState]
  exact ⟨(initial_chain_digit_ptr (pointerState s)).1.trans chain,
    p24.trans (pointer_fields s).2.1,
    (initial_chain_digit_ptr (pointerState s)).2.trans ptr,
    limit,src,len,dst,service⟩

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastLimit67
