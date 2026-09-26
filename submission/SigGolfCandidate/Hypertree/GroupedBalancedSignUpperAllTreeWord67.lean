import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeTerminalTrace67
import SigGolfCandidate.TraceDeterminism


/-! The terminal Merkle transition advances the absolute tree level. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTerminalTreeWord67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeLevelTrace67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev step := GroupedBalancedSignBottomTreeLevelControl67.transitionState

theorem terminal (hash : Hash) (s final : MachineState)
    (heightMax treeBase witnessBase height source target : Nat)
    (ready : Ready heightMax treeBase witnessBase height 1 source target s)
    (terminalHeight : height+1=heightMax)
    (maxBound : heightMax=3 ∨ heightMax=4)
    (treeBound : treeBase+heightMax<2^64)
    (witnessBound : witnessBase+16*heightMax+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (bases : (source=0x83000 ∧ target=0x88000) ∨
      (source=0x88000 ∧ target=0x83000))
    (trace : Trace hash image s 150 157 1 1 final) :
    final.getMem 0x81000=BitVec.ofNat 64 (treeBase+heightMax) := by
  have hb : height<10 := by rcases maxBound with rfl | rfl <;> omega
  have hwb : witnessBase+16*height+16≤0x80000 := by omega
  obtain ⟨done,parentTrace,doneInv,parentFrame,_,_⟩ :=
    GroupedBalancedSignUpperTreeParentTrace67.first_level hash s height
      witnessBase 1 source target ready.pc ready.levelWord ready.witness
      hb hwb witnessAligned ready.selectedBound ready.count ready.sourcePtr
      ready.targetPtr bases (by decide) (by decide)
  have stable (a : Word) (ha : 0x81000≤a.toNat)
      (hl : a.toNat<0x83000) (h08 : a≠0x81008)
      (hd8 : a≠0x810d8) : done.getMem a=s.getMem a :=
    parentFrame a ⟨ha,hl,h08,hd8⟩
  have levelWord : done.getMem 0x81050=BitVec.ofNat 64 height := by
    rw [stable 0x81050 (by decide) (by decide) (by decide) (by decide)]
    exact ready.levelWord
  have treeWord : done.getMem 0x81000=BitVec.ofNat 64 (treeBase+height) := by
    rw [stable 0x81000 (by decide) (by decide) (by decide) (by decide)]
    exact ready.treeWord
  have maxLevel : done.getMem 0x81060=BitVec.ofNat 64 heightMax := by
    rw [stable 0x81060 (by decide) (by decide) (by decide) (by decide)]
    exact ready.maxLevel
  have witness : done.getMem 0x810f8=BitVec.ofNat 64 witnessBase := by
    rw [stable 0x810f8 (by decide) (by decide) (by decide) (by decide)]
    exact ready.witness
  have selectedBound : (done.getMem 0x810e8).toNat<1024 := by
    rw [stable 0x810e8 (by decide) (by decide) (by decide) (by decide)]
    exact ready.selectedBound
  have stepTrace : Trace hash image done 37 37 0 0 (step done) :=
    (GroupedBalancedSignBottomTreeLevelControl67.transition_steps done
      doneInv.pc).trace
  have built : Trace hash image s 150 157 1 1 (step done) := by
    have combined := parentTrace.trans stepTrace
    simpa only [Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub] using combined
  have same := Trace.deterministic trace built
  rw [same]
  have controls := transition_controls done heightMax treeBase witnessBase
    height 1 source target doneInv.pc levelWord treeWord maxLevel witness
    selectedBound doneInv.count doneInv.sourcePtr doneInv.targetPtr
    (by decide) (by omega) (by omega) maxBound
  simpa only [terminalHeight] using controls.2.2.1

#print axioms terminal
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTerminalTreeWord67


/-! Absolute tree level after every parent row of a height-three or height-four call. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperAllTreeWord67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeLevelTrace67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

theorem height3 (hash : Hash) (s final : MachineState)
    (treeBase witnessBase : Nat)
    (ready : Ready 3 treeBase witnessBase 0 4 0x83000 0x88000 s)
    (treeBound : treeBase+3<2^64)
    (witnessBound : witnessBase+16*3+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (trace : Trace hash image s 882 931 7 7 final) :
    final.getMem 0x81000=BitVec.ofNat 64 (treeBase+3) := by
  obtain ⟨at1,t0,r1,_,_⟩ := height_step hash s 3 treeBase witnessBase
    0 4 0x83000 0x88000 ready (by decide) (Or.inl rfl) treeBound
    witnessBound witnessAligned (by decide) (by decide)
    (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨at2,t1,r2,_,_⟩ := height_step hash at1 3 treeBase
    witnessBase 1 2 0x88000 0x83000
    (by simpa only [show 4/2=2 by decide] using r1)
    (by decide) (Or.inl rfl) treeBound witnessBound witnessAligned
    (by decide) (by decide) (Or.inr ⟨rfl,rfl⟩)
  obtain ⟨built,t2,_,_,_,_⟩ :=
    GroupedBalancedSignUpperTreeTerminalTrace67.terminal hash at2 3 treeBase
      witnessBase 2 0x83000 0x88000
      (by simpa only [show 2/2=1 by decide] using r2)
      (by decide) (Or.inl rfl) treeBound witnessBound witnessAligned
      (Or.inl ⟨rfl,rfl⟩)
  have full : Trace hash image s 882 931 7 7 built := by
    have combined := (t0.trans t1).trans t2
    convert combined using 1 <;> decide
  have same := Trace.deterministic trace full
  rw [same]
  exact GroupedBalancedSignUpperTerminalTreeWord67.terminal hash at2 built
    3 treeBase witnessBase 2 0x83000 0x88000
    (by simpa only [show 2/2=1 by decide] using r2)
    (by decide) (Or.inl rfl) treeBound witnessBound witnessAligned
    (Or.inl ⟨rfl,rfl⟩) t2

theorem height4 (hash : Hash) (s final : MachineState)
    (treeBase witnessBase : Nat)
    (ready : Ready 4 treeBase witnessBase 0 8 0x83000 0x88000 s)
    (treeBound : treeBase+4<2^64)
    (witnessBound : witnessBase+16*4+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (trace : Trace hash image s 1668 1773 15 15 final) :
    final.getMem 0x81000=BitVec.ofNat 64 (treeBase+4) := by
  obtain ⟨at1,t0,r1,_,_⟩ := height_step hash s 4 treeBase witnessBase
    0 8 0x83000 0x88000 ready (by decide) (Or.inr rfl) treeBound
    witnessBound witnessAligned (by decide) (by decide)
    (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨at2,t1,r2,_,_⟩ := height_step hash at1 4 treeBase
    witnessBase 1 4 0x88000 0x83000
    (by simpa only [show 8/2=4 by decide] using r1)
    (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
    (by decide) (by decide) (Or.inr ⟨rfl,rfl⟩)
  obtain ⟨at3,t2,r3,_,_⟩ := height_step hash at2 4 treeBase
    witnessBase 2 2 0x83000 0x88000
    (by simpa only [show 4/2=2 by decide] using r2)
    (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
    (by decide) (by decide) (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨built,t3,_,_,_,_⟩ :=
    GroupedBalancedSignUpperTreeTerminalTrace67.terminal hash at3 4 treeBase
      witnessBase 3 0x88000 0x83000
      (by simpa only [show 2/2=1 by decide] using r3)
      (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
      (Or.inr ⟨rfl,rfl⟩)
  have full : Trace hash image s 1668 1773 15 15 built := by
    have combined := ((t0.trans t1).trans t2).trans t3
    convert combined using 1 <;> decide
  have same := Trace.deterministic trace full
  rw [same]
  exact GroupedBalancedSignUpperTerminalTreeWord67.terminal hash at3 built
    4 treeBase witnessBase 3 0x88000 0x83000
    (by simpa only [show 2/2=1 by decide] using r3)
    (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
    (Or.inr ⟨rfl,rfl⟩) t3

#print axioms height3
#print axioms height4
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperAllTreeWord67
