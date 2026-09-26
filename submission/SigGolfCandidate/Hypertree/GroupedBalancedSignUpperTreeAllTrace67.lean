import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeTerminalTrace67

/-! Exact resource trace of all height-three and height-four upper parent levels. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeAllTrace67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeLevelTrace67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

theorem height3 (hash : Hash) (s : MachineState)
    (treeBase witnessBase : Nat)
    (ready : Ready 3 treeBase witnessBase 0 4 0x83000 0x88000 s)
    (treeBound : treeBase+3 < 2^64)
    (witnessBound : witnessBase+16*3+16 ≤ 0x80000)
    (witnessAligned : witnessBase%8=0) :
    ∃ final : MachineState,
      Trace hash image s 882 931 7 7 final ∧
      final.pc=0x20ec ∧ final.getMem 0x810c0=0x88000 ∧
      final.getReg .x2 = s.getReg .x2 ∧
      (∀ a : Word, 0x90000 ≤ a.toNat →
        final.getMem a = s.getMem a) := by
  obtain ⟨at1,trace0,ready1,sp0,mem0⟩ := height_step hash s 3 treeBase witnessBase
    0 4 0x83000 0x88000 ready (by decide) (Or.inl rfl) treeBound
    witnessBound witnessAligned (by decide) (by decide)
    (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨at2,trace1,ready2,sp1,mem1⟩ := height_step hash at1 3 treeBase
    witnessBase 1 2 0x88000 0x83000
    (by simpa only [show 4/2=2 by decide] using ready1)
    (by decide) (Or.inl rfl) treeBound witnessBound witnessAligned
    (by decide) (by decide) (Or.inr ⟨rfl,rfl⟩)
  obtain ⟨final,trace2,pc,rootPtr,sp2,mem2⟩ :=
    GroupedBalancedSignUpperTreeTerminalTrace67.terminal hash at2 3 treeBase
      witnessBase 2 0x83000 0x88000
      (by simpa only [show 2/2=1 by decide] using ready2)
      (by decide) (Or.inl rfl) treeBound witnessBound witnessAligned
      (Or.inl ⟨rfl,rfl⟩)
  refine ⟨final,?_,pc,rootPtr,sp2.trans (sp1.trans sp0),?_⟩
  have combined := (trace0.trans trace1).trans trace2
  convert combined using 1 <;> decide
  intro a high
  exact (mem2 a high).trans ((mem1 a high).trans (mem0 a high))

theorem height4 (hash : Hash) (s : MachineState)
    (treeBase witnessBase : Nat)
    (ready : Ready 4 treeBase witnessBase 0 8 0x83000 0x88000 s)
    (treeBound : treeBase+4 < 2^64)
    (witnessBound : witnessBase+16*4+16 ≤ 0x80000)
    (witnessAligned : witnessBase%8=0) :
    ∃ final : MachineState,
      Trace hash image s 1668 1773 15 15 final ∧
      final.pc=0x20ec ∧ final.getMem 0x810c0=0x83000 ∧
      final.getReg .x2 = s.getReg .x2 ∧
      (∀ a : Word, 0x90000 ≤ a.toNat →
        final.getMem a = s.getMem a) := by
  obtain ⟨at1,trace0,ready1,sp0,mem0⟩ := height_step hash s 4 treeBase witnessBase
    0 8 0x83000 0x88000 ready (by decide) (Or.inr rfl) treeBound
    witnessBound witnessAligned (by decide) (by decide)
    (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨at2,trace1,ready2,sp1,mem1⟩ := height_step hash at1 4 treeBase
    witnessBase 1 4 0x88000 0x83000
    (by simpa only [show 8/2=4 by decide] using ready1)
    (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
    (by decide) (by decide) (Or.inr ⟨rfl,rfl⟩)
  obtain ⟨at3,trace2,ready3,sp2,mem2⟩ := height_step hash at2 4 treeBase
    witnessBase 2 2 0x83000 0x88000
    (by simpa only [show 4/2=2 by decide] using ready2)
    (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
    (by decide) (by decide) (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨final,trace3,pc,rootPtr,sp3,mem3⟩ :=
    GroupedBalancedSignUpperTreeTerminalTrace67.terminal hash at3 4 treeBase
      witnessBase 3 0x88000 0x83000
      (by simpa only [show 2/2=1 by decide] using ready3)
      (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
      (Or.inr ⟨rfl,rfl⟩)
  refine ⟨final,?_,pc,rootPtr,sp3.trans (sp2.trans (sp1.trans sp0)),?_⟩
  have combined := ((trace0.trans trace1).trans trace2).trans trace3
  convert combined using 1 <;> decide
  intro a high
  exact (mem3 a high).trans ((mem2 a high).trans
    ((mem1 a high).trans (mem0 a high)))

#print axioms height3
#print axioms height4
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeAllTrace67
