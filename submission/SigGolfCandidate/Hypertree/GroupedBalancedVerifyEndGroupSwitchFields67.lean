import SigGolfCandidate.Hypertree.GroupedBalancedVerifyEndGroupSwitch67

/-! The group-30 boundary updates the path height and preserves the root. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyEndGroupSwitchFields67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyEndGroup67
open GroupedBalancedVerifyEndGroupSwitch67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem switch_pc (s : MachineState)
    (pc : s.pc = 0x19c4) (group : s.getMem 0x81058 = 29) :
    (switchState s).pc = 0x1514 := by
  have x6 : (countState s).getReg .x6 = 30 := by
    rw [count_x6,group]
    decide
  have x7 : (countState s).getReg .x7 = 30 := count_x7 s
  have pc0 := count_pc s pc
  simp [switchState,execInstrBr,pc0,x6,x7,
    signExtend13,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem switch_mem (s : MachineState) (a : Word)
    (ne : a ≠ 0x81060) :
    (switchState s).getMem a = (countState s).getMem a := by
  simp [switchState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_ne]
  intro eq
  exact (ne eq).elim

theorem switch_height (s : MachineState) :
    (switchState s).getMem 0x81060 = 4 := by
  simp [switchState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq]

theorem switch_group (s : MachineState)
    (group : s.getMem 0x81058 = 29) :
    (switchState s).getMem 0x81058 = 30 := by
  rw [switch_mem s 0x81058 (by decide),count_group,group]
  decide

theorem switch_transition (s : MachineState)
    (pc : s.pc = 0x19c4) (group : s.getMem 0x81058 = 29) :
    OrdinarySteps image s 15 (switchState s) ∧
    (switchState s).pc = 0x1514 ∧
    (switchState s).getMem 0x81058 = 30 ∧
    (switchState s).getMem 0x81060 = 4 ∧
    (∀ a : Word, a.toNat < 0x80000 →
      (switchState s).getMem a = s.getMem a) := by
  refine ⟨Keygen.ordinary_trans image s (countState s)
    (switchState s) 8 7 (count_steps s pc)
    (switch_steps s pc group),switch_pc s pc group,
      switch_group s group,switch_height s,?_⟩
  intro a low
  rw [switch_mem s a (by
    intro eq
    rw [eq] at low
    exact (by decide : ¬ ((0x81060 : Word).toNat < 0x80000)) low)]
  apply count_mem s a
  intro eq
  rw [eq] at low
  exact (by decide : ¬ ((0x81058 : Word).toNat < 0x80000)) low

#print axioms switch_transition
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyEndGroupSwitchFields67
