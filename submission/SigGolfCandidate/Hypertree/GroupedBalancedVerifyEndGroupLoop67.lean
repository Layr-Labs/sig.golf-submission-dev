import SigGolfCandidate.Hypertree.GroupedBalancedVerifyEndGroupFinish67

/-! Ordinary group transitions loop back to the byte decoder. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyEndGroupLoop67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyEndGroup67
open GroupedBalancedVerifyEndGroupFinish67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem count_x6_nat (s : MachineState) (g : Nat)
    (group : s.getMem 0x81058 = BitVec.ofNat 64 g) :
    (countState s).getReg .x6 = BitVec.ofNat 64 (g+1) := by
  rw [count_x6,group]
  simpa using (BitVec.ofNat_add g 1).symm

theorem count_ne30 (s : MachineState) (g : Nat)
    (group : s.getMem 0x81058 = BitVec.ofNat 64 g)
    (bound : g < 44) (other : g ≠ 29) :
    (countState s).getReg .x6 ≠ (countState s).getReg .x7 := by
  rw [count_x6_nat s g group,count_x7]
  intro eq
  have natural := congrArg BitVec.toNat eq
  have small : g+1 < 2^64 := by omega
  have left : (BitVec.ofNat 64 (g+1)).toNat = g+1 := by
    change (g+1)%2^64 = g+1
    exact Nat.mod_eq_of_lt small
  have right : ((30 : Word)).toNat = 30 := by decide
  rw [left,right] at natural
  omega

theorem count_ne45 (s : MachineState) (g : Nat)
    (group : s.getMem 0x81058 = BitVec.ofNat 64 g)
    (bound : g < 44) :
    (countState s).getReg .x6 ≠ 45 := by
  rw [count_x6_nat s g group]
  intro eq
  have natural := congrArg BitVec.toNat eq
  have small : g+1 < 2^64 := by omega
  have left : (BitVec.ofNat 64 (g+1)).toNat = g+1 := by
    change (g+1)%2^64 = g+1
    exact Nat.mod_eq_of_lt small
  have right : ((45 : Word)).toNat = 45 := by decide
  rw [left,right] at natural
  omega

theorem loop_pc (s : MachineState) (pc : s.pc = 0x19c4)
    (h30 : (countState s).getReg .x6 ≠
      (countState s).getReg .x7)
    (h45 : (countState s).getReg .x6 ≠ 45) :
    (finishState s).pc = 0x1514 := by
  let s1 := execInstrBr (countState s) (.BEQ .x6 .x7 8)
  let s2 := execInstrBr s1 (.JAL .x0 20)
  let s3 := execInstrBr s2 (.ADDI .x7 .x0 45)
  have pc0 := count_pc s pc
  have pc1 : s1.pc = 0x19e8 := by
    simp [s1,execInstrBr,pc0,h30]
  have pc2 : s2.pc = 0x19fc := by
    simp [s2,execInstrBr,pc1,signExtend21]
  have pc3 : s3.pc = 0x1a00 := by
    simp [s3,execInstrBr,pc2]
  have hx6 : s3.getReg .x6 = (countState s).getReg .x6 := by
    simp [s3,s2,s1,execInstrBr,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  have hx7 : s3.getReg .x7 = 45 := by
    simp [s3,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  change (execInstrBr s3 (.BNE .x6 .x7 (-1260))).pc = 0x1514
  simp [execInstrBr,pc3,hx6,hx7,signExtend13]
  exact h45

theorem loop_group (s : MachineState) (g : Nat)
    (group : s.getMem 0x81058 = BitVec.ofNat 64 g) :
    (finishState s).getMem 0x81058 = BitVec.ofNat 64 (g+1) := by
  have frame : (finishState s).getMem 0x81058 =
      (countState s).getMem 0x81058 := by
    simp [finishState,execInstrBr]
  rw [frame,count_group,group]
  simpa using (BitVec.ofNat_add g 1).symm

theorem loop_transition (s : MachineState) (g : Nat)
    (pc : s.pc = 0x19c4)
    (group : s.getMem 0x81058 = BitVec.ofNat 64 g)
    (bound : g < 44) (other : g ≠ 29) :
    OrdinarySteps image s 12 (finishState s) ∧
    (finishState s).pc = 0x1514 ∧
    (finishState s).getMem 0x81058 = BitVec.ofNat 64 (g+1) ∧
    (finishState s).getMem 0x81060 = s.getMem 0x81060 ∧
    (∀ a : Word, a.toNat < 0x80000 →
      (finishState s).getMem a = s.getMem a) := by
  have h30 := count_ne30 s g group bound other
  have h45 := count_ne45 s g group bound
  refine ⟨Keygen.ordinary_trans image s (countState s)
    (finishState s) 8 4 (count_steps s pc)
    (finish_steps s pc h30),loop_pc s pc h30 h45,
      loop_group s g group,finish_mem s 0x81060 (by decide),?_⟩
  intro a low
  apply finish_mem s a
  intro eq
  have h := congrArg BitVec.toNat eq
  rw [eq] at low
  exact (by decide : ¬ ((0x81058 : Word).toNat < 0x80000)) low

#print axioms loop_transition
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyEndGroupLoop67
