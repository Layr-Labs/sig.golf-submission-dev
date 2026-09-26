import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedAdvance67

/-! The signer shifts its 192-bit selected address right by ten bits. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67.image

def Outside (a : Word) : Prop :=
  a ≠ 0x81090 ∧ a ≠ 0x81098 ∧ a ≠ 0x810a0 ∧ a ≠ 0x81100

private theorem count_add (i : Nat) :
    (BitVec.ofNat 64 i : Word) + 1 = BitVec.ofNat 64 (i+1) := by
  simp [BitVec.ofNat_add]

private theorem count_ten (i : Nat) (hi : i < 10) :
    ((BitVec.ofNat 64 i : Word) + 1 = 10) ↔ i+1=10 := by
  interval_cases i <;> decide

def Inv (index : BitVec 192) (i : Nat) (s : MachineState) : Prop :=
  i ≤ 10 ∧
  s.pc = (if i < 10 then 0x1524 else 0x15ac) ∧
  s.getMem 0x81100 = BitVec.ofNat 64 i ∧
  (∀ w : Fin 3,
    s.getMem (Signing.wordAddress 0x81090 w.val) =
      (index >>> i).extractLsb' (64*w.val) 64)

theorem one_step (index : BitVec 192) (i : Nat) (s : MachineState)
    (inv : Inv index i s) (hi : i < 10) :
    ∃ next : MachineState,
      OrdinarySteps image s 34 next ∧ Inv index (i+1) next ∧
      (∀ a : Word, Outside a → next.getMem a = s.getMem a) ∧
      next.getReg .x2=s.getReg .x2 := by
  obtain ⟨ibound,spc,scount,swords⟩ := inv
  have startPc : s.pc = 0x1524 := by simpa [hi] using spc
  let mid := GroupedBalancedSignBottomSelectedData67.fullState s
  let next := GroupedBalancedSignBottomSelectedAdvance67.advanceState mid
  have a := GroupedBalancedSignBottomSelectedData67.full_steps s startPc
  have midPc := GroupedBalancedSignBottomSelectedData67.full_pc s startPc
  have b := GroupedBalancedSignBottomSelectedAdvance67.advance_steps mid midPc
  have run : OrdinarySteps image s 34 next := by
    simpa [mid,next] using Keygen.ordinary_trans image s mid next 25 9 a b
  have midCount : mid.getMem 0x81100 = BitVec.ofNat 64 i := by
    rw [GroupedBalancedSignBottomSelectedData67.shift_frame s 0x81100
      (by decide) (by decide) (by decide)]
    exact scount
  have nextCount : next.getMem 0x81100 = BitVec.ofNat 64 (i+1) := by
    rw [GroupedBalancedSignBottomSelectedAdvance67.advance_count,midCount,count_add]
  have nextWords : ∀ w : Fin 3,
      next.getMem (Signing.wordAddress 0x81090 w.val) =
        (index >>> (i+1)).extractLsb' (64*w.val) 64 := by
    intro w
    rw [GroupedBalancedSignBottomSelectedAdvance67.advance_frame mid _
      (by fin_cases w <;> decide)]
    rw [GroupedBalancedSignBottomSelectedData67.shifted_index s (index >>> i) swords w]
    rw [BitVec.shiftRight_add]
  have nextPc : next.pc = (if i+1 < 10 then 0x1524 else 0x15ac) := by
    rw [GroupedBalancedSignBottomSelectedAdvance67.advance_pc mid midPc,
      midCount]
    by_cases h : i+1=10
    · have hw : (BitVec.ofNat 64 i : Word) + 1 = 10 :=
        (count_ten i hi).2 h
      simpa [h] using hw
    · have hw : (BitVec.ofNat 64 i : Word) + 1 ≠ 10 := by
        intro h'; exact h ((count_ten i hi).1 h')
      have hlt : i+1<10 := by omega
      simpa [hlt] using hw
  have nextInv : Inv index (i+1) next := ⟨by omega,nextPc,nextCount,nextWords⟩
  refine ⟨next,run,nextInv,?_,?_⟩
  · intro a ha
    rw [GroupedBalancedSignBottomSelectedAdvance67.advance_frame mid a ha.2.2.2,
      GroupedBalancedSignBottomSelectedData67.shift_frame s a
        ha.1 ha.2.1 ha.2.2.1]
  · simp [next,mid,GroupedBalancedSignBottomSelectedAdvance67.advanceState,
      GroupedBalancedSignBottomSelectedData67.fullState,
      GroupedBalancedSignBottomSelectedShift67.shiftState,
      GroupedBalancedSignBottomSelectedLoad67.loadState,execInstrBr,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem run_prefix (index : BitVec 192) (start : MachineState)
    (initial : Inv index 0 start) :
    ∀ i : Nat, i ≤ 10 →
      ∃ finish : MachineState,
        OrdinarySteps image start (34*i) finish ∧ Inv index i finish := by
  intro i hi
  induction i with
  | zero => exact ⟨start,by simpa using OrdinarySteps.refl start,initial⟩
  | succ i ih =>
      have hi : i ≤ 10 := by omega
      obtain ⟨middle,prefixTrace,middleInv⟩ := ih hi
      have hlt : i < 10 := by omega
      obtain ⟨finish,tick,finishInv,_,_⟩ := one_step index i middle middleInv hlt
      refine ⟨finish,?_,finishInv⟩
      simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        Keygen.ordinary_trans image start middle finish (34*i) 34 prefixTrace tick

theorem run_prefix_frame (index : BitVec 192) (start : MachineState)
    (initial : Inv index 0 start) :
    ∀ i : Nat, i ≤ 10 →
      ∃ finish : MachineState,
        OrdinarySteps image start (34*i) finish ∧ Inv index i finish ∧
        (∀ a : Word, Outside a → finish.getMem a = start.getMem a) ∧
        finish.getReg .x2=start.getReg .x2 := by
  intro i hi
  induction i with
  | zero =>
      exact ⟨start,by simpa using OrdinarySteps.refl start,initial,
        by intros; rfl,rfl⟩
  | succ i ih =>
      have hi : i ≤ 10 := by omega
      obtain ⟨middle,prefixTrace,middleInv,middleFrame,middleSp⟩ := ih hi
      have hlt : i < 10 := by omega
      obtain ⟨finish,tick,finishInv,tickFrame,tickSp⟩ :=
        one_step index i middle middleInv hlt
      refine ⟨finish,?_,finishInv,?_,tickSp.trans middleSp⟩
      · simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
          Keygen.ordinary_trans image start middle finish (34*i) 34 prefixTrace tick
      · intro a ha
        rw [tickFrame a ha,middleFrame a ha]

theorem run_all (index : BitVec 192) (start : MachineState)
    (initial : Inv index 0 start) :
    ∃ finish : MachineState,
      OrdinarySteps image start 340 finish ∧
      finish.pc = 0x15ac ∧
      finish.getMem 0x81100 = 10 ∧
      (∀ w : Fin 3,
        finish.getMem (Signing.wordAddress 0x81090 w.val) =
          (index >>> 10).extractLsb' (64*w.val) 64) := by
  obtain ⟨finish,trace,ibound,pc,count,words⟩ := run_prefix index start initial 10 (by decide)
  refine ⟨finish,by simpa using trace,?_,?_,words⟩
  · simpa using pc
  · simpa using count

#print axioms one_step
#print axioms run_prefix
#print axioms run_prefix_frame
#print axioms run_all
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedFold67
