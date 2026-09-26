import SigGolfCandidate.Hypertree.GroupedBalancedKeygenLevel67

/-! Reset the direct67 keygen parent-node counter for the next level. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenReset67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedKeygenImage67.image

def resetState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 64)
  execInstrBr s (.SD .x28 .x6 0)

private theorem reset_code :
    Keygen.instructionAt image 0x1470 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x1474 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1478 = some (.base (.ADDI .x28 .x28 64)) ∧
    Keygen.instructionAt image 0x147c = some (.base (.SD .x28 .x6 0)) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide

theorem reset_steps (s : MachineState) (pc : s.pc = 0x1470) :
    OrdinarySteps image s 4 (resetState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 129)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 64)
  obtain ⟨c0,c1,c2,c3⟩ := reset_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0)) 3
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 129)) 2
  · have hp : s1.pc = 0x1474 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 64)) 1
  · have hp : s2.pc = 0x1478 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 (resetState s) _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s3.pc = 0x147c := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [s1,s2,s3,resetState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem reset_pc (s : MachineState) (pc : s.pc = 0x1470) :
    (resetState s).pc = 0x1480 := by simp [resetState,execInstrBr,pc]

theorem reset_counter (s : MachineState) :
    (resetState s).getMem 0x81040#64 = 0 := by
  simp [resetState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem reset_other (s : MachineState) (a : Word) (hne : a ≠ 0x81040#64) :
    (resetState s).getMem a = s.getMem a := by
  simp [resetState,execInstrBr,signExtend12,hne,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

#print axioms reset_steps
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenReset67

/-! Execute all parent nodes in one direct67 keygen tree level. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodesFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedKeygenImage67.image

theorem nodes (hash : Hash) (s : MachineState) (n rem src dst : Nat)
    (pc : s.pc = 0x1480) (positive : 0 < rem) (bound : n+rem ≤ 8)
    (srcCase : src = 0x82000 ∨ src = 0x82100)
    (dstCase : dst = 0x82000 ∨ dst = 0x82100)
    (index : s.getMem 0x81040#64 = BitVec.ofNat 64 n)
    (count : s.getMem 0x81070#64 = BitVec.ofNat 64 (n+rem))
    (source : s.getMem 0x81078#64 = BitVec.ofNat 64 src)
    (destination : s.getMem 0x81080#64 = BitVec.ofNat 64 dst) :
    ∃ final,
      Trace hash image s (79*rem) (86*rem) rem rem final ∧
      final.pc = 0x15bc ∧
      final.getMem 0x81040#64 = BitVec.ofNat 64 (n+rem) ∧
      (∀ a : Word, 0x81000 ≤ a.toNat → a.toNat < 0x82000 →
        a ≠ 0x81008#64 → a ≠ 0x81040#64 → final.getMem a = s.getMem a) := by
  induction rem generalizing s n with
  | zero => omega
  | succ t ih =>
      obtain ⟨mid,first,midPC,midIndex,midFrame⟩ :=
        GroupedBalancedKeygenOneNode67.one_node hash s n (n+t+1) src dst
          pc (by omega) (by omega) srcCase dstCase index
          (by simpa only [Nat.add_assoc] using count) source destination
      by_cases last : t = 0
      · subst t
        refine ⟨mid,?_,?_,?_,midFrame⟩
        · simpa only [Nat.reduceMul,Nat.mul_one,Nat.reduceAdd] using first
        · simpa [midPC]
        · simpa [Nat.add_assoc] using midIndex
      · have midPC' : mid.pc = 0x1480 := by
          simpa [last] using midPC
        have midCount : mid.getMem 0x81070#64 = BitVec.ofNat 64 (n+1+t) := by
          rw [midFrame 0x81070#64 (by decide) (by decide) (by decide) (by decide)]
          simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using count
        have midSrc : mid.getMem 0x81078#64 = BitVec.ofNat 64 src := by
          rw [midFrame 0x81078#64 (by decide) (by decide) (by decide) (by decide)]
          exact source
        have midDst : mid.getMem 0x81080#64 = BitVec.ofNat 64 dst := by
          rw [midFrame 0x81080#64 (by decide) (by decide) (by decide) (by decide)]
          exact destination
        obtain ⟨final,second,finalPC,finalIndex,finalFrame⟩ :=
          ih mid (n+1) midPC' (by omega) (by omega)
            midIndex midCount midSrc midDst
        refine ⟨final,?_,finalPC,?_,?_⟩
        · simpa only [Nat.mul_succ,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
            using first.trans second
        · have arith : n+1+t = n+(t+1) := by omega
          rw [arith] at finalIndex
          exact finalIndex
        · intro a high low ne08 ne40
          rw [finalFrame a high low ne08 ne40,midFrame a high low ne08 ne40]

#print axioms nodes
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodesFold67
