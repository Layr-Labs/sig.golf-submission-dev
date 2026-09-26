import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeStepData67

/-! Final upper Merkle parent value at the dynamic root buffer. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeTerminalData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeParentData67
open GroupedBalancedSignUpperTreeFirstLevelData67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev step := GroupedBalancedSignBottomTreeLevelControl67.transitionState
private abbrev node := GroupedBalancedSignUpperTreeModel67.nodeAt

theorem terminal_root (hash : Hash) (treeBase leafBase : Nat)
    (leaves : Nat → Reference.Digest)
    (heightMax witnessBase height source target addressBase : Nat)
    (s : MachineState)
    (params : Params leafBase height 1 source target addressBase)
    (start : Start hash treeBase leafBase leaves heightMax witnessBase height
      1 source target addressBase s)
    (terminalHeight : height+1=heightMax)
    (maxBound : heightMax=3 ∨ heightMax=4)
    (treeBound : treeBase+heightMax<2^64)
    (witnessBound : witnessBase+16*heightMax+16≤0x80000)
    (witnessAligned : witnessBase%8=0) :
    ∃ final : MachineState,
      Trace hash image s 150 157 1 1 final ∧
      final.pc=0x20ec ∧
      final.getMem 0x810c0=BitVec.ofNat 64 target ∧
      (∀ i : Fin 2,
        final.getMem (BitVec.ofNat 64 (target+8*i.val))=
          (node hash treeBase leafBase leaves heightMax 0).extractLsb'
            (64*i.val) 64) := by
  have levelBound : height<10 := by
    rcases maxBound with rfl|rfl <;> omega
  have shortWitness : witnessBase+16*height+16≤0x80000 := by omega
  obtain ⟨done,levelTrace,doneInv⟩ := one_level hash treeBase leafBase leaves
    heightMax witnessBase height 1 source target addressBase s params start
    levelBound shortWitness witnessAligned
  obtain ⟨final,terminalTrace,finalPc,rootPtr,_,_⟩ :=
    GroupedBalancedSignUpperTreeTerminalTrace67.terminal hash s heightMax
      treeBase witnessBase height source target start.ready terminalHeight
      maxBound treeBound witnessBound witnessAligned params.bases
  have transition : Trace hash image done 37 37 0 0 (step done) :=
    (GroupedBalancedSignBottomTreeLevelControl67.transition_steps done
      doneInv.pc).trace
  have same : final=step done := by
    have combined : Trace hash image s 150 157 1 1 (step done) := by
      convert levelTrace.trans transition using 1 <;> decide
    exact Trace.deterministic terminalTrace combined
  have output : ∀ i : Fin 2,
      (step done).getMem (BitVec.ofNat 64 (target+8*i.val))=
        (node hash treeBase leafBase leaves heightMax 0).extractLsb'
          (64*i.val) 64 := by
    intro i
    have ne (b : Word) (low : b.toNat<0x83000) :
        BitVec.ofNat 64 (target+8*i.val)≠b := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      have range : 0x83000≤target ∧ target≤0x88000 := by
        rcases params.bases with ⟨_,rfl⟩|⟨_,rfl⟩ <;> omega
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : target+8*i.val<2^64)] at hn
      omega
    rw [GroupedBalancedSignBottomTreeLevelData67.frame done _
      (ne 0x810c0 (by decide)) (ne 0x810c8 (by decide))
      (ne 0x810d0 (by decide)) (ne 0x81000 (by decide))
      (ne 0x81050 (by decide))]
    simpa only [terminalHeight,Nat.mul_zero,Nat.add_zero] using
      doneInv.targetWords 0 (by decide) i
  exact ⟨final,terminalTrace,finalPc,rootPtr,by rw [same]; exact output⟩

#print axioms terminal_root
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeTerminalData67
