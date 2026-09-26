import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeLevelTrace67

/-! Terminal one-parent upper level and return-ready root pointer. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeTerminalTrace67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeLevelTrace67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev step := GroupedBalancedSignBottomTreeLevelControl67.transitionState

theorem terminal (hash : Hash) (s : MachineState)
    (heightMax treeBase witnessBase height source target : Nat)
    (ready : Ready heightMax treeBase witnessBase height 1 source target s)
    (terminalHeight : height+1=heightMax)
    (maxBound : heightMax=3 ∨ heightMax=4)
    (treeBound : treeBase+heightMax < 2^64)
    (witnessBound : witnessBase+16*heightMax+16 ≤ 0x80000)
    (witnessAligned : witnessBase%8=0)
    (bases : (source=0x83000 ∧ target=0x88000) ∨
      (source=0x88000 ∧ target=0x83000)) :
    ∃ final : MachineState,
      Trace hash image s 150 157 1 1 final ∧
      final.pc=0x20ec ∧
      final.getMem 0x810c0=BitVec.ofNat 64 target ∧
      final.getReg .x2 = s.getReg .x2 ∧
      (∀ a : Word, 0x90000 ≤ a.toNat →
        final.getMem a = s.getMem a) := by
  have hb : height < 10 := by
    rcases maxBound with rfl | rfl <;> omega
  have hwb : witnessBase+16*height+16 ≤0x80000 := by omega
  obtain ⟨done,parentTrace,doneInv,parentFrame,parentSp,parentHigh⟩ :=
    GroupedBalancedSignUpperTreeParentTrace67.first_level hash s height
      witnessBase 1 source target ready.pc ready.levelWord ready.witness
      hb hwb witnessAligned ready.selectedBound ready.count ready.sourcePtr
      ready.targetPtr bases (by decide) (by decide)
  have stable (a : Word) (ha : 0x81000 ≤ a.toNat)
      (hb : a.toNat < 0x83000) (h08 : a ≠ 0x81008)
      (hd8 : a ≠ 0x810d8) : done.getMem a = s.getMem a :=
    parentFrame a ⟨ha,hb,h08,hd8⟩
  have levelWord : done.getMem 0x81050 = BitVec.ofNat 64 height := by
    rw [stable 0x81050 (by decide) (by decide) (by decide) (by decide)]
    exact ready.levelWord
  have treeWord : done.getMem 0x81000 = BitVec.ofNat 64 (treeBase+height) := by
    rw [stable 0x81000 (by decide) (by decide) (by decide) (by decide)]
    exact ready.treeWord
  have maxLevel : done.getMem 0x81060 = BitVec.ofNat 64 heightMax := by
    rw [stable 0x81060 (by decide) (by decide) (by decide) (by decide)]
    exact ready.maxLevel
  have witness : done.getMem 0x810f8 = BitVec.ofNat 64 witnessBase := by
    rw [stable 0x810f8 (by decide) (by decide) (by decide) (by decide)]
    exact ready.witness
  have selectedBound : (done.getMem 0x810e8).toNat < 1024 := by
    rw [stable 0x810e8 (by decide) (by decide) (by decide) (by decide)]
    exact ready.selectedBound
  have transTrace : Trace hash image done 37 37 0 0 (step done) :=
    (GroupedBalancedSignBottomTreeLevelControl67.transition_steps done
      doneInv.pc).trace
  obtain ⟨pc,_,_,_,_,_,_,sourcePtr,_⟩ :=
    transition_controls done heightMax treeBase witnessBase height 1 source
      target doneInv.pc levelWord treeWord maxLevel witness selectedBound
      doneInv.count doneInv.sourcePtr doneInv.targetPtr (by decide)
      (by omega) (by omega) maxBound
  refine ⟨step done,?_,?_,sourcePtr,?_,?_⟩
  · have combined := parentTrace.trans transTrace
    simpa only [Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub] using combined
  · rw [pc]
    simp [terminalHeight]
  · exact (GroupedBalancedSignBottomTreeLevelStack67.transition_sp done).trans
      parentSp
  · intro a high
    have frame : (step done).getMem a = done.getMem a :=
      GroupedBalancedSignBottomTreeLevelData67.frame done a
        (by intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega)
        (by intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega)
        (by intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega)
        (by intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega)
        (by intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega)
    exact frame.trans (parentHigh a high)

#print axioms terminal
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeTerminalTrace67
