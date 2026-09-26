import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomStackBound67

/-! State facts after storing one bottom-tree leaf. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafAdvanceData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomLeafAdvance67
open GroupedBalancedSignBottomStackBound67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

theorem advance_counter (s : MachineState)
    (h : (s.getMem 0x810e0).toNat < 1024) :
    (advanceState s).getMem 0x810e0 = s.getMem 0x810e0 + 1 := by
  have ⟨ne0,ne8⟩ := below_stack (s.getMem 0x810e0) 0x810e0 h (by decide)
  simp only [stack0] at ne0 ne8
  simp [advanceState,execInstrBr,signExtend12,Expansion.mem_setMem,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    ne0,ne8]
  split_ifs with he8 he0
  · exact False.elim (ne8 he8)
  · exact False.elim (ne0 he0)
  · rfl

theorem advance_address (s : MachineState)
    (h : (s.getMem 0x810e0).toNat < 1024) :
    (advanceState s).getMem 0x81008 = s.getMem 0x81008 + 1 := by
  have ⟨ne0,ne8⟩ := below_stack (s.getMem 0x810e0) 0x81008 h (by decide)
  simp only [stack0] at ne0 ne8
  simp [advanceState,execInstrBr,signExtend12,Expansion.mem_setMem,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    ne0,ne8]
  split_ifs with he8 he0
  · exact False.elim (ne8 he8)
  · exact False.elim (ne0 he0)
  · rfl

theorem advance_pc (s : MachineState) (pc : s.pc = 0x1478)
    (h : (s.getMem 0x810e0).toNat < 1024) :
    (advanceState s).pc =
      if s.getMem 0x810e0 + 1 = (1024 : Word) then 0x14ec else 0x12cc := by
  have ⟨ne0,ne8⟩ := below_stack (s.getMem 0x810e0) 0x810e0 h (by decide)
  simp only [stack0] at ne0 ne8
  simp [advanceState,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    ne0,ne8,pc]
  have hc := advance_counter s h
  simp [advanceState,execInstrBr,signExtend12,Expansion.mem_setMem,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne] at hc
  rw [hc]

theorem advance_trace (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1478)
    (h : (s.getMem 0x810e0).toNat < 1024) :
    Trace hash GroupedBalancedSignImage67.image s 29 29 0 0 (advanceState s) ∧
    (advanceState s).getMem 0x810e0 = s.getMem 0x810e0 + 1 ∧
    (advanceState s).getMem 0x81008 = s.getMem 0x81008 + 1 ∧
    (advanceState s).pc =
      if s.getMem 0x810e0 + 1 = (1024 : Word) then 0x14ec else 0x12cc := by
  have hv := stack0_valid (s.getMem 0x810e0) h
  refine ⟨?_,advance_counter s h,advance_address s h,advance_pc s pc h⟩
  exact OrdinarySteps.trace (hash := hash)
    (advance_steps s pc (by simpa only [stack0] using hv.1)
      (by simpa only [stack0] using hv.2))

theorem advance_frame (s : MachineState)
    (h : (s.getMem 0x810e0).toNat < 1024) (a : Word)
    (h0 : a ≠ stack0 (s.getMem 0x810e0))
    (h8 : a ≠ stack0 (s.getMem 0x810e0) + 8)
    (haddr : a ≠ 0x81008) (hcount : a ≠ 0x810e0) :
    (advanceState s).getMem a = s.getMem a := by
  have ⟨cn0,cn8⟩ := below_stack (s.getMem 0x810e0) 0x810e0 h (by decide)
  have ⟨an0,an8⟩ := below_stack (s.getMem 0x810e0) 0x81008 h (by decide)
  simp only [stack0] at h0 h8 cn0 cn8 an0 an8
  simp [advanceState,execInstrBr,signExtend12,Expansion.mem_setMem,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  split
  · rename_i eq
    exact False.elim (hcount eq)
  · split
    · rename_i eq
      exact False.elim (haddr eq)
    · split
      · rename_i eq
        exact False.elim (h8 eq)
      · split
        · rename_i eq
          exact False.elim (h0 eq)
        · rfl

theorem advance_store0 (s : MachineState)
    (h : (s.getMem 0x810e0).toNat < 1024) :
    (advanceState s).getMem (stack0 (s.getMem 0x810e0)) =
      s.getMem 0x80300 := by
  have ⟨cn0,cn8⟩ := below_stack (s.getMem 0x810e0) 0x810e0 h (by decide)
  have ⟨an0,an8⟩ := below_stack (s.getMem 0x810e0) 0x81008 h (by decide)
  have ne := stack0_ne_stack8 (s.getMem 0x810e0) h
  simp only [stack0] at cn0 cn8 an0 an8 ne ⊢
  simp [advanceState,execInstrBr,signExtend12,Expansion.mem_setMem,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  split
  · rename_i eq
    exact False.elim (cn0 eq.symm)
  · split
    · rename_i eq
      exact False.elim (an0 eq.symm)
    · rfl

theorem advance_store8 (s : MachineState)
    (h : (s.getMem 0x810e0).toNat < 1024) :
    (advanceState s).getMem (stack0 (s.getMem 0x810e0) + 8) =
      s.getMem 0x80308 := by
  have ⟨cn0,cn8⟩ := below_stack (s.getMem 0x810e0) 0x810e0 h (by decide)
  have ⟨an0,an8⟩ := below_stack (s.getMem 0x810e0) 0x81008 h (by decide)
  simp only [stack0] at cn0 cn8 an0 an8 ⊢
  simp [advanceState,execInstrBr,signExtend12,Expansion.mem_setMem,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  split
  · rename_i eq
    exact False.elim (cn8 eq.symm)
  · split
    · rename_i eq
      exact False.elim (an8 eq.symm)
    · rfl

#print axioms advance_counter
#print axioms advance_address
#print axioms advance_pc
#print axioms advance_trace
#print axioms advance_frame
#print axioms advance_store0
#print axioms advance_store8
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafAdvanceData67
