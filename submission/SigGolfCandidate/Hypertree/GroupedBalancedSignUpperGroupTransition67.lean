import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedAdvance67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedFold67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperGroupTransition67. -/
section
/-! Shift the 192-bit selected index by the upper group's height. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67Byte.image

def Outside (a : Word) : Prop :=
  a ≠ 0x81090 ∧ a ≠ 0x81098 ∧ a ≠ 0x810a0 ∧ a ≠ 0x81100

def Inv (index : BitVec 192) (height i : Nat) (s : MachineState) : Prop :=
  i ≤ height ∧
  s.pc = (if i < height then 0x1c94 else 0x1d24) ∧
  s.getMem 0x81100 = BitVec.ofNat 64 i ∧
  s.getMem 0x81060 = BitVec.ofNat 64 height ∧
  (∀ w : Fin 3,
    s.getMem (Signing.wordAddress 0x81090 w.val) =
      (index >>> i).extractLsb' (64*w.val) 64)

private theorem count_add (i : Nat) :
    (BitVec.ofNat 64 i : Word) + 1 = BitVec.ofNat 64 (i+1) := by
  simp [BitVec.ofNat_add]

private theorem count_limit (i height : Nat)
    (hi : i < height) (hh : height = 3 ∨ height = 4) :
    ((BitVec.ofNat 64 i : Word) + 1 = BitVec.ofNat 64 height) ↔
      i+1=height := by
  rcases hh with rfl | rfl
  · interval_cases i <;> decide
  · interval_cases i <;> decide

theorem one_step (index : BitVec 192) (height i : Nat) (s : MachineState)
    (hh : height = 3 ∨ height = 4)
    (inv : Inv index height i s) (hi : i < height) :
    ∃ next : MachineState,
      OrdinarySteps image s 36 next ∧ Inv index height (i+1) next ∧
      (∀ a : Word, Outside a → next.getMem a = s.getMem a) := by
  obtain ⟨ibound,spc,scount,slimit,swords⟩ := inv
  have startPc : s.pc = 0x1c94 := by simpa [hi] using spc
  let mid := GroupedBalancedSignUpperSelectedData67.fullState s
  let next := GroupedBalancedSignUpperSelectedAdvance67.advanceState mid
  have a := GroupedBalancedSignUpperSelectedData67.full_steps s startPc
  have midPc := GroupedBalancedSignUpperSelectedData67.full_pc s startPc
  have b := GroupedBalancedSignUpperSelectedAdvance67.advance_steps mid midPc
  have run : OrdinarySteps image s 36 next := by
    simpa [mid,next] using Keygen.ordinary_trans image s mid next 25 11 a b
  have midCount : mid.getMem 0x81100 = BitVec.ofNat 64 i := by
    rw [GroupedBalancedSignUpperSelectedData67.shift_frame s 0x81100
      (by decide) (by decide) (by decide)]
    exact scount
  have midLimit : mid.getMem 0x81060 = BitVec.ofNat 64 height := by
    rw [GroupedBalancedSignUpperSelectedData67.shift_frame s 0x81060
      (by decide) (by decide) (by decide)]
    exact slimit
  have nextCount : next.getMem 0x81100 = BitVec.ofNat 64 (i+1) := by
    rw [GroupedBalancedSignUpperSelectedAdvance67.advance_count,midCount,count_add]
  have nextLimit : next.getMem 0x81060 = BitVec.ofNat 64 height := by
    rw [GroupedBalancedSignUpperSelectedAdvance67.advance_frame mid 0x81060
      (by decide)]
    exact midLimit
  have nextWords : ∀ w : Fin 3,
      next.getMem (Signing.wordAddress 0x81090 w.val) =
        (index >>> (i+1)).extractLsb' (64*w.val) 64 := by
    intro w
    rw [GroupedBalancedSignUpperSelectedAdvance67.advance_frame mid _
      (by fin_cases w <;> decide)]
    rw [GroupedBalancedSignUpperSelectedData67.shifted_index s
      (index >>> i) swords w]
    rw [BitVec.shiftRight_add]
  have nextPc : next.pc =
      (if i+1 < height then 0x1c94 else 0x1d24) := by
    rw [GroupedBalancedSignUpperSelectedAdvance67.advance_pc mid midPc,
      midCount,midLimit]
    by_cases h : i+1=height
    · have hw : (BitVec.ofNat 64 i : Word) + 1 = BitVec.ofNat 64 height :=
        (count_limit i height hi hh).2 h
      simp [h]
      simpa using hw
    · have hw : (BitVec.ofNat 64 i : Word) + 1 ≠ BitVec.ofNat 64 height := by
        intro h'; exact h ((count_limit i height hi hh).1 h')
      have hlt : i+1<height := by omega
      simp [hlt]
      simpa using hw
  have nextInv : Inv index height (i+1) next :=
    ⟨by omega,nextPc,nextCount,nextLimit,nextWords⟩
  refine ⟨next,run,nextInv,?_⟩
  intro a ha
  rw [GroupedBalancedSignUpperSelectedAdvance67.advance_frame mid a ha.2.2.2,
    GroupedBalancedSignUpperSelectedData67.shift_frame s a
      ha.1 ha.2.1 ha.2.2.1]

theorem run_prefix (index : BitVec 192) (height : Nat)
    (hh : height = 3 ∨ height = 4) (start : MachineState)
    (initial : Inv index height 0 start) :
    ∀ i : Nat, i ≤ height →
      ∃ finish : MachineState,
        OrdinarySteps image start (36*i) finish ∧
        Inv index height i finish ∧
        (∀ a : Word, Outside a → finish.getMem a = start.getMem a) := by
  intro i hi
  induction i with
  | zero =>
    exact ⟨start,by simpa using OrdinarySteps.refl start,initial,
      by intros; rfl⟩
  | succ i ih =>
    obtain ⟨middle,prefixTrace,middleInv,middleFrame⟩ := ih (by omega)
    obtain ⟨finish,tick,finishInv,tickFrame⟩ :=
      one_step index height i middle hh middleInv (by omega)
    refine ⟨finish,?_,finishInv,?_⟩
    · simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        using Keygen.ordinary_trans image start middle finish
          (36*i) 36 prefixTrace tick
    · intro a ha
      rw [tickFrame a ha,middleFrame a ha]

theorem run_all (index : BitVec 192) (height : Nat)
    (hh : height = 3 ∨ height = 4) (start : MachineState)
    (initial : Inv index height 0 start) :
    ∃ finish : MachineState,
      OrdinarySteps image start (36*height) finish ∧
      finish.pc = 0x1d24 ∧
      finish.getMem 0x81100 = BitVec.ofNat 64 height ∧
      (∀ w : Fin 3,
        finish.getMem (Signing.wordAddress 0x81090 w.val) =
          (index >>> height).extractLsb' (64*w.val) 64) ∧
      (∀ a : Word, Outside a → finish.getMem a = start.getMem a) := by
  obtain ⟨finish,trace,inv,frame⟩ :=
    run_prefix index height hh start initial height (by rfl)
  obtain ⟨ibound,pc,count,limit,words⟩ := inv
  refine ⟨finish,trace,?_,count,words,frame⟩
  simp at pc
  exact pc

#print axioms one_step
#print axioms run_prefix
#print axioms run_all
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedFold67

end

/-! Advance the upper layer after shifting its selected index. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperGroupTransition67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67Byte.image

def advanceLayer (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x58)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x58)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x7 .x0 30)
  execInstrBr s (.BNE .x6 .x7 20)

def switchHeight (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 4)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x60)
  execInstrBr s (.SD .x28 .x6 0)

def finishLayer (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x7 .x0 45)
  execInstrBr s (.BNE .x6 .x7 (-1916))

def transitionState (s : MachineState) : MachineState :=
  let advanced := advanceLayer s
  let routed := if s.getMem 0x81058 + 1 = (30 : Word) then
    switchHeight advanced else advanced
  finishLayer routed

theorem advance_count (s : MachineState) :
    (advanceLayer s).getMem 0x81058 = s.getMem 0x81058 + 1 := by
  simp [advanceLayer,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem advance_frame (s : MachineState) (a : Word) (ha : a ≠ 0x81058) :
    (advanceLayer s).getMem a = s.getMem a := by
  change a ≠ 528472#64 at ha
  simp [advanceLayer,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,ha]

theorem switch_height (s : MachineState) :
    (switchHeight s).getMem 0x81060 = 4 := by
  simp [switchHeight,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem switch_frame (s : MachineState) (a : Word) (ha : a ≠ 0x81060) :
    (switchHeight s).getMem a = s.getMem a := by
  change a ≠ 528480#64 at ha
  simp [switchHeight,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,ha]

theorem finish_frame (s : MachineState) (a : Word) :
    (finishLayer s).getMem a = s.getMem a := by
  simp [finishLayer,execInstrBr]

theorem advance_reg (s : MachineState) :
    (advanceLayer s).getReg .x6 = s.getMem 0x81058 + 1 := by
  simp [advanceLayer,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem advance_pc (s : MachineState) (pc : s.pc = 0x1d24) :
    (advanceLayer s).pc =
      if s.getMem 0x81058 + 1 = (30 : Word) then 0x1d48 else 0x1d58 := by
  have raw : (advanceLayer s).pc =
      if (advanceLayer s).getMem 0x81058 = (30 : Word)
      then 0x1d48 else 0x1d58 := by
    simp [advanceLayer,execInstrBr,signExtend12,signExtend13,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]
  rw [raw,advance_count]

theorem switch_reg (s : MachineState) :
    (switchHeight s).getReg .x6 = 4 := by
  simp [switchHeight,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem switch_pc (s : MachineState) (pc : s.pc = 0x1d48) :
    (switchHeight s).pc = 0x1d58 := by
  simp [switchHeight,execInstrBr,pc]

theorem finish_pc (s : MachineState) (pc : s.pc = 0x1d58) :
    (finishLayer s).pc =
      if s.getReg .x6 = (45 : Word) then 0x1d60 else 0x15e0 := by
  simp [finishLayer,execInstrBr,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

private theorem advance_code :
    Keygen.instructionAt image 0x1d24 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1d28 = some (.base (.ADDI .x28 .x28 0x58)) ∧
    Keygen.instructionAt image 0x1d2c = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x1d30 = some (.base (.ADDI .x6 .x6 1)) ∧
    Keygen.instructionAt image 0x1d34 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1d38 = some (.base (.ADDI .x28 .x28 0x58)) ∧
    Keygen.instructionAt image 0x1d3c = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1d40 = some (.base (.ADDI .x7 .x0 30)) ∧
    Keygen.instructionAt image 0x1d44 = some (.base (.BNE .x6 .x7 20)) := by decide

theorem advance_steps (s : MachineState) (pc : s.pc = 0x1d24) :
    OrdinarySteps image s 9 (advanceLayer s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x58)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 1)
  let s5 := execInstrBr s4 (.LUI .x28 0x81)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 0x58)
  let s7 := execInstrBr s6 (.SD .x28 .x6 0)
  let s8 := execInstrBr s7 (.ADDI .x7 .x0 30)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8⟩ := advance_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 8
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x58)) 7
  · have hp : s1.pc = 0x1d28 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 6
  · have hp : s2.pc = 0x1d2c := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simpa [s1,s2,s3,advanceLayer,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      accessValid,rangeValid,MEMORY_BYTES] using
      (by decide : accessValid (0x81058 : Word) 8 = true)
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 1)) 5
  · have hp : s3.pc = 0x1d30 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x81)) 4
  · have hp : s4.pc = 0x1d34 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 0x58)) 3
  · have hp : s5.pc = 0x1d38 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x6 0)) 2
  · have hp : s6.pc = 0x1d3c := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · simpa [s1,s2,s3,s4,s5,s6,s7,advanceLayer,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      accessValid,rangeValid,MEMORY_BYTES] using
      (by decide : accessValid (0x81058 : Word) 8 = true)
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x7 .x0 30)) 1
  · have hp : s7.pc = 0x1d40 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 (advanceLayer s) _ (.base (.BNE .x6 .x7 20)) 0
  · have hp : s8.pc = 0x1d44 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  exact OrdinarySteps.refl _

private theorem switch_code :
    Keygen.instructionAt image 0x1d48 = some (.base (.ADDI .x6 .x0 4)) ∧
    Keygen.instructionAt image 0x1d4c = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1d50 = some (.base (.ADDI .x28 .x28 0x60)) ∧
    Keygen.instructionAt image 0x1d54 = some (.base (.SD .x28 .x6 0)) := by decide

theorem switch_steps (s : MachineState) (pc : s.pc = 0x1d48) :
    OrdinarySteps image s 4 (switchHeight s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 4)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0x60)
  obtain ⟨c0,c1,c2,c3⟩ := switch_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 4)) 3
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s1.pc = 0x1d4c := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0x60)) 1
  · have hp : s2.pc = 0x1d50 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 (switchHeight s) _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s3.pc = 0x1d54 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simpa [s1,s2,s3,switchHeight,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      accessValid,rangeValid,MEMORY_BYTES] using
      (by decide : accessValid (0x81060 : Word) 8 = true)
  exact OrdinarySteps.refl _

private theorem finish_code :
    Keygen.instructionAt image 0x1d58 = some (.base (.ADDI .x7 .x0 45)) ∧
    Keygen.instructionAt image 0x1d5c = some (.base (.BNE .x6 .x7 (-1916))) := by decide

theorem finish_steps (s : MachineState) (pc : s.pc = 0x1d58) :
    OrdinarySteps image s 2 (finishLayer s) := by
  let s1 := execInstrBr s (.ADDI .x7 .x0 45)
  obtain ⟨c0,c1⟩ := finish_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x7 .x0 45)) 1
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 (finishLayer s) _ (.base (.BNE .x6 .x7 (-1916))) 0
  · have hp : s1.pc = 0x1d5c := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  exact OrdinarySteps.refl _

theorem transition_trace (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1d24) :
    Trace hash image s
      (if s.getMem 0x81058 + 1 = (30 : Word) then 15 else 11)
      (if s.getMem 0x81058 + 1 = (30 : Word) then 15 else 11)
      0 0 (transitionState s) := by
  let advanced := advanceLayer s
  have first := advance_steps s pc
  by_cases h30 : s.getMem 0x81058 + 1 = (30 : Word)
  · have apc : advanced.pc = 0x1d48 := by
      rw [advance_pc s pc,if_pos h30]
    have second := switch_steps advanced apc
    have tpc := switch_pc advanced apc
    have third := finish_steps (switchHeight advanced) tpc
    have combined : OrdinarySteps image s 15 (transitionState s) := by
      have ab := Keygen.ordinary_trans image s advanced
        (switchHeight advanced) 9 4 first second
      have abc := Keygen.ordinary_trans image s (switchHeight advanced)
        (transitionState s) 13 2 (by simpa using ab)
          (by simpa only [transitionState,if_pos h30] using third)
      simpa using abc
    simpa only [if_pos h30] using OrdinarySteps.trace (hash := hash) combined
  · have apc : advanced.pc = 0x1d58 := by
      rw [advance_pc s pc,if_neg h30]
    have second := finish_steps advanced apc
    have combined : OrdinarySteps image s 11 (transitionState s) := by
      simpa only [transitionState,if_neg h30] using
        Keygen.ordinary_trans image s advanced (finishLayer advanced) 9 2 first second
    simpa only [if_neg h30] using OrdinarySteps.trace (hash := hash) combined

theorem transition_count (s : MachineState) :
    (transitionState s).getMem 0x81058 = s.getMem 0x81058 + 1 := by
  unfold transitionState
  by_cases h30 : s.getMem 0x81058 + 1 = (30 : Word)
  · simp only [if_pos h30,finish_frame,
      switch_frame (advanceLayer s) 0x81058 (by decide),advance_count]
  · simp only [if_neg h30,finish_frame,advance_count]

theorem transition_height (s : MachineState) :
    (transitionState s).getMem 0x81060 =
      if s.getMem 0x81058 + 1 = (30 : Word) then 4 else s.getMem 0x81060 := by
  unfold transitionState
  by_cases h30 : s.getMem 0x81058 + 1 = (30 : Word)
  · simp only [if_pos h30,finish_frame,switch_height]
  · simp only [if_neg h30,finish_frame,
      advance_frame s 0x81060 (by decide)]

theorem transition_frame (s : MachineState) (a : Word)
    (h0 : a ≠ 0x81058) (h1 : a ≠ 0x81060) :
    (transitionState s).getMem a = s.getMem a := by
  unfold transitionState
  by_cases h30 : s.getMem 0x81058 + 1 = (30 : Word)
  · simp only [if_pos h30,finish_frame,
      switch_frame (advanceLayer s) a h1,advance_frame s a h0]
  · simp only [if_neg h30,finish_frame,advance_frame s a h0]

theorem transition_pc (s : MachineState) (pc : s.pc = 0x1d24) :
    (transitionState s).pc =
      if s.getMem 0x81058 + 1 = (45 : Word) then 0x1d60 else 0x15e0 := by
  unfold transitionState
  by_cases h30 : s.getMem 0x81058 + 1 = (30 : Word)
  · have apc : (advanceLayer s).pc = 0x1d48 := by
      rw [advance_pc s pc,if_pos h30]
    simp only [if_pos h30]
    rw [finish_pc (switchHeight (advanceLayer s))
      (switch_pc (advanceLayer s) apc),switch_reg]
    have h45 : s.getMem 0x81058 + 1 ≠ (45 : Word) := by
      intro eq
      exact (by decide : (30 : Word) ≠ 45) (h30.symm.trans eq)
    simp only [if_neg h45]
    decide
  · have apc : (advanceLayer s).pc = 0x1d58 := by
      rw [advance_pc s pc,if_neg h30]
    simp only [if_neg h30]
    rw [finish_pc (advanceLayer s) apc,advance_reg]

#print axioms advance_steps
#print axioms switch_steps
#print axioms finish_steps
#print axioms transition_trace
#print axioms transition_count
#print axioms transition_height
#print axioms transition_frame
#print axioms transition_pc
#print axioms advance_count
#print axioms advance_frame
#print axioms switch_height
#print axioms switch_frame
#print axioms advance_pc
#print axioms finish_pc
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperGroupTransition67
