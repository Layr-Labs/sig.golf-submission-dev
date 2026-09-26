import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeLevelFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeAllTrace67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeByteCallee67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeParentsFrame67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeCalleeFrame67. -/
section
/-! Earlier WOTS signature words across the complete h3/h4 parent loops. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeParentsFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeLevelTrace67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

theorem height3_before (hash : Hash) (s final : MachineState)
    (treeBase witnessBase : Nat)
    (ready : Ready 3 treeBase witnessBase 0 4 0x83000 0x88000 s)
    (treeBound : treeBase+3<2^64)
    (witnessBound : witnessBase+16*3+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (trace : Trace hash image s 882 931 7 7 final)
    (a : Word) (low : a.toNat<witnessBase) : final.getMem a=s.getMem a := by
  obtain ⟨at1,t0,r1,_,_⟩ := height_step hash s 3 treeBase witnessBase
    0 4 0x83000 0x88000 ready (by decide) (Or.inl rfl) treeBound
    witnessBound witnessAligned (by decide) (by decide)
    (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨at2,t1,r2,_,_⟩ := height_step hash at1 3 treeBase witnessBase
    1 2 0x88000 0x83000
    (by simpa only [show 4/2=2 by decide] using r1)
    (by decide) (Or.inl rfl) treeBound witnessBound witnessAligned
    (by decide) (by decide) (Or.inr ⟨rfl,rfl⟩)
  obtain ⟨built,t2,_,_,_,_⟩ :=
    GroupedBalancedSignUpperTreeTerminalTrace67.terminal hash at2 3 treeBase
      witnessBase 2 0x83000 0x88000
      (by simpa only [show 2/2=1 by decide] using r2)
      (by decide) (Or.inl rfl) treeBound witnessBound witnessAligned
      (Or.inl ⟨rfl,rfl⟩)
  have builtTrace : Trace hash image s 882 931 7 7 built := by
    have combined := (t0.trans t1).trans t2
    convert combined using 1 <;> decide
  have same := Trace.deterministic trace builtTrace
  rw [same]
  have f0 := GroupedBalancedSignUpperSelectedTreeLevelFrame67.height_step_before hash
    s at1 3 treeBase witnessBase 0 4 0x83000 0x88000 ready
    (by decide) (Or.inl rfl) witnessBound witnessAligned
    (by decide) (by decide) (Or.inl ⟨rfl,rfl⟩) t0 a low
  have f1 := GroupedBalancedSignUpperSelectedTreeLevelFrame67.height_step_before hash
    at1 at2 3 treeBase witnessBase 1 2 0x88000 0x83000
    (by simpa only [show 4/2=2 by decide] using r1)
    (by decide) (Or.inl rfl) witnessBound witnessAligned
    (by decide) (by decide) (Or.inr ⟨rfl,rfl⟩) t1 a low
  have f2 := GroupedBalancedSignUpperSelectedTreeLevelFrame67.terminal_before hash
    at2 built 3 treeBase witnessBase 2 0x83000 0x88000
    (by simpa only [show 2/2=1 by decide] using r2)
    (by decide) (Or.inl rfl) witnessBound witnessAligned
    (Or.inl ⟨rfl,rfl⟩) t2 a low
  exact f2.trans (f1.trans f0)

theorem height4_before (hash : Hash) (s final : MachineState)
    (treeBase witnessBase : Nat)
    (ready : Ready 4 treeBase witnessBase 0 8 0x83000 0x88000 s)
    (treeBound : treeBase+4<2^64)
    (witnessBound : witnessBase+16*4+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (trace : Trace hash image s 1668 1773 15 15 final)
    (a : Word) (low : a.toNat<witnessBase) : final.getMem a=s.getMem a := by
  obtain ⟨at1,t0,r1,_,_⟩ := height_step hash s 4 treeBase witnessBase
    0 8 0x83000 0x88000 ready (by decide) (Or.inr rfl) treeBound
    witnessBound witnessAligned (by decide) (by decide)
    (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨at2,t1,r2,_,_⟩ := height_step hash at1 4 treeBase witnessBase
    1 4 0x88000 0x83000
    (by simpa only [show 8/2=4 by decide] using r1)
    (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
    (by decide) (by decide) (Or.inr ⟨rfl,rfl⟩)
  obtain ⟨at3,t2,r3,_,_⟩ := height_step hash at2 4 treeBase witnessBase
    2 2 0x83000 0x88000
    (by simpa only [show 4/2=2 by decide] using r2)
    (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
    (by decide) (by decide) (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨built,t3,_,_,_,_⟩ :=
    GroupedBalancedSignUpperTreeTerminalTrace67.terminal hash at3 4 treeBase
      witnessBase 3 0x88000 0x83000
      (by simpa only [show 2/2=1 by decide] using r3)
      (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
      (Or.inr ⟨rfl,rfl⟩)
  have builtTrace : Trace hash image s 1668 1773 15 15 built := by
    have combined := ((t0.trans t1).trans t2).trans t3
    convert combined using 1 <;> decide
  have same := Trace.deterministic trace builtTrace
  rw [same]
  have f0 := GroupedBalancedSignUpperSelectedTreeLevelFrame67.height_step_before hash
    s at1 4 treeBase witnessBase 0 8 0x83000 0x88000 ready
    (by decide) (Or.inr rfl) witnessBound witnessAligned
    (by decide) (by decide) (Or.inl ⟨rfl,rfl⟩) t0 a low
  have f1 := GroupedBalancedSignUpperSelectedTreeLevelFrame67.height_step_before hash
    at1 at2 4 treeBase witnessBase 1 4 0x88000 0x83000
    (by simpa only [show 8/2=4 by decide] using r1)
    (by decide) (Or.inr rfl) witnessBound witnessAligned
    (by decide) (by decide) (Or.inr ⟨rfl,rfl⟩) t1 a low
  have f2 := GroupedBalancedSignUpperSelectedTreeLevelFrame67.height_step_before hash
    at2 at3 4 treeBase witnessBase 2 2 0x83000 0x88000
    (by simpa only [show 4/2=2 by decide] using r2)
    (by decide) (Or.inr rfl) witnessBound witnessAligned
    (by decide) (by decide) (Or.inl ⟨rfl,rfl⟩) t2 a low
  have f3 := GroupedBalancedSignUpperSelectedTreeLevelFrame67.terminal_before hash
    at3 built 4 treeBase witnessBase 3 0x88000 0x83000
    (by simpa only [show 2/2=1 by decide] using r3)
    (by decide) (Or.inr rfl) witnessBound witnessAligned
    (Or.inr ⟨rfl,rfl⟩) t3 a low
  exact f3.trans (f2.trans (f1.trans f0))

#print axioms height3_before
#print axioms height4_before
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeParentsFrame67

end

/-! Final ByteSign upper Merkle callee preserves earlier WOTS signature words. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeCalleeFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev oldImage := GroupedBalancedSignImage67.image

private theorem ne_static (a : Word) (low : a.toNat<0x80000) (b : Nat)
    (hb : 0x80000≤b) (small : b<2^64) : a≠BitVec.ofNat 64 b := by
  intro eq
  have hn := congrArg BitVec.toNat eq
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at hn
  omega

theorem start_before (hash : Hash) (s ready : MachineState)
    (pc : s.pc=0x1c30)
    (sp : s.getReg .x2=0xfff7e0 ∨ s.getReg .x2=0xfff700)
    (trace : Trace hash oldImage s 72 72 0 0 ready)
    (a : Word) (low : a.toNat<0x80000) : ready.getMem a=s.getMem a := by
  let called := GroupedBalancedSignUpperTreeCall67.called s
  let entered := GroupedBalancedSignBottomTreeEntry67.entryState called
  let initialized := GroupedBalancedSignBottomTreeInit67.initState entered
  have callSteps := GroupedBalancedSignUpperTreeCall67.call_step s pc
  have callPc := GroupedBalancedSignUpperTreeCall67.call_pc s pc
  have callSp : called.getReg .x2=0xfff7e0 ∨ called.getReg .x2=0xfff700 := by
    rw [GroupedBalancedSignUpperTreeCall67.call_sp]
    exact sp
  have entrySteps := GroupedBalancedSignBottomTreeEntryStack67.entry_steps_stack
    called callPc callSp
  have entryPc := GroupedBalancedSignBottomTreeEntry67.entry_pc called callPc
  have initSteps := GroupedBalancedSignBottomTreeInit67.init_steps entered entryPc
  have initPc := GroupedBalancedSignBottomTreeInit67.init_pc entered entryPc
  obtain ⟨built,prelude,_,preludeFrame⟩ :=
    GroupedBalancedSignUpperTreePreludeTrace67.prelude initialized initPc
  have builtTrace : Trace hash oldImage s 72 72 0 0 built := by
    have combined := (((OrdinarySteps.trace (hash := hash) callSteps).trans
      (OrdinarySteps.trace (hash := hash) entrySteps)).trans
      (OrdinarySteps.trace (hash := hash) initSteps)).trans
      (OrdinarySteps.trace (hash := hash) prelude)
    convert combined using 1 <;> decide
  have same := Trace.deterministic trace builtTrace
  have ne (b : Nat) (hb : 0x80000≤b) (small : b<2^64) :
      a≠BitVec.ofNat 64 b := ne_static a low b hb small
  have slotHigh : 0x90000≤(s.getReg .x2-16).toNat := by
    rcases sp with h | h <;> rw [h] <;> decide
  have neSlot : a≠called.getReg .x2-16 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [GroupedBalancedSignUpperTreeCall67.call_sp] at hn
    omega
  rw [same,
    preludeFrame a
      (ne 0x81008 (by decide) (by decide))
      (ne 0x81010 (by decide) (by decide))
      (ne 0x81018 (by decide) (by decide))
      (ne 0x810a8 (by decide) (by decide))
      (ne 0x810b0 (by decide) (by decide))
      (ne 0x810b8 (by decide) (by decide)),
    GroupedBalancedSignBottomTreeInitData67.init_frame entered a
      (ne 0x810c0 (by decide) (by decide))
      (ne 0x810c8 (by decide) (by decide))
      (ne 0x810d0 (by decide) (by decide)),
    GroupedBalancedSignBottomTreeEntryData67.entry_frame called a
      neSlot (ne 0x81050 (by decide) (by decide)),
    GroupedBalancedSignUpperTreeCall67.call_mem]

#print axioms start_before

theorem height3_before (hash : Hash) (s returned : MachineState)
    (treeBase witnessBase : Nat)
    (trace : Trace hash image s 957 1006 7 7 returned)
    (pc : s.pc=0x1c30)
    (sp : s.getReg .x2=0xfff7e0 ∨ s.getReg .x2=0xfff700)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (maxLevel : s.getMem 0x81060=3)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (selected : (s.getMem 0x810e8).toNat<1024)
    (count : s.getMem 0x810d0=8)
    (treeBound : treeBase+3<2^64)
    (witnessBound : witnessBase+16*3+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (a : Word) (low : a.toNat<witnessBase) :
    returned.getMem a=s.getMem a := by
  obtain ⟨ready,startTrace,startInv,readySp,slot⟩ :=
    GroupedBalancedSignUpperTreeStart67.start hash s 3 treeBase witnessBase 4
      pc sp tree maxLevel witness selected count (by decide)
  obtain ⟨final,parentTrace,finalPc,_,finalSp,finalHigh⟩ :=
    GroupedBalancedSignUpperTreeAllTrace67.height3 hash ready treeBase
      witnessBase startInv treeBound witnessBound witnessAligned
  obtain ⟨returnTrace,_,_⟩ :=
    GroupedBalancedSignUpperTreeCallee67.return_after hash s ready final sp
      slot readySp finalSp finalHigh finalPc
  have oldTrace : Trace hash oldImage s 957 1006 7 7
      (Keygen.returnState final) := by
    have combined := (startTrace.trans parentTrace).trans returnTrace
    convert combined using 1 <;> decide
  have built : Trace hash image s 957 1006 7 7
      (Keygen.returnState final) :=
    GroupedBalancedSignUpperTreeByteCallee67.transfer_height3 hash s
      (Keygen.returnState final) treeBase witnessBase oldTrace pc sp tree
      maxLevel witness selected count treeBound witnessBound witnessAligned
  have same := Trace.deterministic trace built
  rw [same,Keygen.return_mem]
  exact (GroupedBalancedSignUpperSelectedTreeParentsFrame67.height3_before hash ready final
    treeBase witnessBase startInv treeBound witnessBound
    witnessAligned parentTrace a low).trans
    (start_before hash s ready pc sp startTrace a (by omega))

theorem height4_before (hash : Hash) (s returned : MachineState)
    (treeBase witnessBase : Nat)
    (trace : Trace hash image s 1743 1848 15 15 returned)
    (pc : s.pc=0x1c30)
    (sp : s.getReg .x2=0xfff7e0 ∨ s.getReg .x2=0xfff700)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (maxLevel : s.getMem 0x81060=4)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (selected : (s.getMem 0x810e8).toNat<1024)
    (count : s.getMem 0x810d0=16)
    (treeBound : treeBase+4<2^64)
    (witnessBound : witnessBase+16*4+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (a : Word) (low : a.toNat<witnessBase) :
    returned.getMem a=s.getMem a := by
  obtain ⟨ready,startTrace,startInv,readySp,slot⟩ :=
    GroupedBalancedSignUpperTreeStart67.start hash s 4 treeBase witnessBase 8
      pc sp tree maxLevel witness selected count (by decide)
  obtain ⟨final,parentTrace,finalPc,_,finalSp,finalHigh⟩ :=
    GroupedBalancedSignUpperTreeAllTrace67.height4 hash ready treeBase
      witnessBase startInv treeBound witnessBound witnessAligned
  obtain ⟨returnTrace,_,_⟩ :=
    GroupedBalancedSignUpperTreeCallee67.return_after hash s ready final sp
      slot readySp finalSp finalHigh finalPc
  have oldTrace : Trace hash oldImage s 1743 1848 15 15
      (Keygen.returnState final) := by
    have combined := (startTrace.trans parentTrace).trans returnTrace
    convert combined using 1 <;> decide
  have built : Trace hash image s 1743 1848 15 15
      (Keygen.returnState final) :=
    GroupedBalancedSignUpperTreeByteCallee67.transfer_height4 hash s
      (Keygen.returnState final) treeBase witnessBase oldTrace pc sp tree
      maxLevel witness selected count treeBound witnessBound witnessAligned
  have same := Trace.deterministic trace built
  rw [same,Keygen.return_mem]
  exact (GroupedBalancedSignUpperSelectedTreeParentsFrame67.height4_before hash ready final
    treeBase witnessBase startInv treeBound witnessBound
    witnessAligned parentTrace a low).trans
    (start_before hash s ready pc sp startTrace a (by omega))

#print axioms height3_before
#print axioms height4_before
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeCalleeFrame67
