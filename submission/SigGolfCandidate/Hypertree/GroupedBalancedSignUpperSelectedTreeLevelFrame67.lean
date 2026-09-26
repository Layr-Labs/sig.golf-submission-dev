import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeParentFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeLevelTrace67

/-! Earlier WOTS signature words survive each upper parent level. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeLevelFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeLevelTrace67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev step := GroupedBalancedSignBottomTreeLevelControl67.transitionState

private theorem ne_const (witnessBase : Nat) (a : Word) (low : a.toNat<witnessBase)
    (baseUpper : witnessBase≤0x80000) (b : Nat)
    (hb : 0x80000≤b) (small : b<2^64) : a≠BitVec.ofNat 64 b := by
  intro eq
  have hn := congrArg BitVec.toNat eq
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at hn
  omega

theorem height_step_before (hash : Hash) (s next : MachineState)
    (heightMax treeBase witnessBase height limit source target : Nat)
    (ready : Ready heightMax treeBase witnessBase height limit source target s)
    (heightBound : height+1<heightMax)
    (maxBound : heightMax=3 ∨ heightMax=4)
    (witnessBound : witnessBase+16*heightMax+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (positive : 0<limit) (small : limit≤8)
    (bases : (source=0x83000 ∧ target=0x88000) ∨
      (source=0x88000 ∧ target=0x83000))
    (trace : Trace hash image s
      (113+84*(limit-1)+85) (120+91*(limit-1)+85)
      limit limit next)
    (a : Word) (low : a.toNat<witnessBase) : next.getMem a=s.getMem a := by
  have hb : height<10 := by rcases maxBound with rfl | rfl <;> omega
  have hwb : witnessBase+16*height+16≤0x80000 := by omega
  obtain ⟨done,parentTrace,doneInv,parentFrame,_,_⟩ :=
    GroupedBalancedSignUpperTreeParentTrace67.first_level hash s height
      witnessBase limit source target ready.pc ready.levelWord ready.witness
      hb hwb witnessAligned ready.selectedBound ready.count ready.sourcePtr
      ready.targetPtr bases positive small
  have doneLow := GroupedBalancedSignUpperSelectedTreeParentFrame67.first_level_before
    hash s done height witnessBase limit source target ready.pc ready.levelWord
    ready.witness hb hwb witnessAligned ready.selectedBound
    ready.count ready.sourcePtr ready.targetPtr bases positive small
    parentTrace a low
  have doneLevel : done.getMem 0x81050=BitVec.ofNat 64 height := by
    rw [parentFrame 0x81050 ⟨by decide,by decide,by decide,by decide⟩]
    exact ready.levelWord
  have doneMax : done.getMem 0x81060=BitVec.ofNat 64 heightMax := by
    rw [parentFrame 0x81060 ⟨by decide,by decide,by decide,by decide⟩]
    exact ready.maxLevel
  let shifted := step done
  have transTrace : Trace hash image done 37 37 0 0 shifted :=
    (GroupedBalancedSignBottomTreeLevelControl67.transition_steps done
      doneInv.pc).trace
  have shiftedPc : shifted.pc=0x1e04 := by
    have h := GroupedBalancedSignUpperTreeLevelTrace67.transition_pc done
      heightMax height doneInv.pc doneLevel doneMax (by omega) maxBound
    rw [h]
    simp [Nat.ne_of_lt heightBound]
  obtain ⟨built,prelude,_,preludeFrame⟩ :=
    GroupedBalancedSignUpperTreePreludeTrace67.prelude shifted shiftedPc
  have builtTrace : Trace hash image s
      (113+84*(limit-1)+85) (120+91*(limit-1)+85)
      limit limit built := by
    have combined := (parentTrace.trans transTrace).trans
      (OrdinarySteps.trace (hash := hash) prelude)
    convert combined using 1 <;> omega
  have same := Trace.deterministic trace builtTrace
  rw [same]
  have ne (b : Nat) (hb : 0x80000≤b) (small : b<2^64) :
      a≠BitVec.ofNat 64 b := ne_const witnessBase a low (by omega) b hb small
  exact (preludeFrame a
    (ne 0x81008 (by decide) (by decide))
    (ne 0x81010 (by decide) (by decide))
    (ne 0x81018 (by decide) (by decide))
    (ne 0x810a8 (by decide) (by decide))
    (ne 0x810b0 (by decide) (by decide))
    (ne 0x810b8 (by decide) (by decide))).trans
    ((GroupedBalancedSignBottomTreeLevelData67.frame done a
      (ne 0x810c0 (by decide) (by decide))
      (ne 0x810c8 (by decide) (by decide))
      (ne 0x810d0 (by decide) (by decide))
      (ne 0x81000 (by decide) (by decide))
      (ne 0x81050 (by decide) (by decide))).trans doneLow)

theorem terminal_before (hash : Hash) (s final : MachineState)
    (heightMax treeBase witnessBase height source target : Nat)
    (ready : Ready heightMax treeBase witnessBase height 1 source target s)
    (terminalHeight : height+1=heightMax)
    (maxBound : heightMax=3 ∨ heightMax=4)
    (witnessBound : witnessBase+16*heightMax+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (bases : (source=0x83000 ∧ target=0x88000) ∨
      (source=0x88000 ∧ target=0x83000))
    (trace : Trace hash image s 150 157 1 1 final)
    (a : Word) (low : a.toNat<witnessBase) : final.getMem a=s.getMem a := by
  have hb : height<10 := by rcases maxBound with rfl | rfl <;> omega
  have hwb : witnessBase+16*height+16≤0x80000 := by omega
  obtain ⟨done,parentTrace,doneInv,_,_,_⟩ :=
    GroupedBalancedSignUpperTreeParentTrace67.first_level hash s height
      witnessBase 1 source target ready.pc ready.levelWord ready.witness
      hb hwb witnessAligned ready.selectedBound ready.count ready.sourcePtr
      ready.targetPtr bases (by decide) (by decide)
  have doneLow := GroupedBalancedSignUpperSelectedTreeParentFrame67.first_level_before
    hash s done height witnessBase 1 source target ready.pc ready.levelWord
    ready.witness hb hwb witnessAligned ready.selectedBound
    ready.count ready.sourcePtr ready.targetPtr bases (by decide) (by decide)
    parentTrace a low
  let shifted := step done
  have transTrace : Trace hash image done 37 37 0 0 shifted :=
    (GroupedBalancedSignBottomTreeLevelControl67.transition_steps done
      doneInv.pc).trace
  have builtTrace : Trace hash image s 150 157 1 1 shifted := by
    have combined := parentTrace.trans transTrace
    simpa only [Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub] using combined
  have same := Trace.deterministic trace builtTrace
  rw [same]
  have ne (b : Nat) (hb : 0x80000≤b) (small : b<2^64) :
      a≠BitVec.ofNat 64 b := ne_const witnessBase a low (by omega) b hb small
  exact (GroupedBalancedSignBottomTreeLevelData67.frame done a
      (ne 0x810c0 (by decide) (by decide))
      (ne 0x810c8 (by decide) (by decide))
      (ne 0x810d0 (by decide) (by decide))
      (ne 0x81000 (by decide) (by decide))
      (ne 0x81050 (by decide) (by decide))).trans doneLow

#print axioms height_step_before
#print axioms terminal_before
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeLevelFrame67
