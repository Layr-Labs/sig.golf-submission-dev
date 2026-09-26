import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeControlFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeAllTrace67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeByteCallee67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeParentsFrame67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCalleeFrame67. -/
section
/-! The h3/h4 parent loops preserve the upper group control words. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeParentsFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeLevelTrace67
open GroupedBalancedSignUpperTreeControlFrame67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

theorem height3_frame (hash : Hash) (s final : MachineState)
    (treeBase witnessBase : Nat)
    (ready : Ready 3 treeBase witnessBase 0 4 0x83000 0x88000 s)
    (treeBound : treeBase+3<2^64)
    (witnessBound : witnessBase+16*3+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (trace : Trace hash image s 882 931 7 7 final)
    (a : Word) (safe : Safe a) : final.getMem a=s.getMem a := by
  obtain ⟨at1,trace0,ready1,_,_⟩ := height_step hash s 3 treeBase witnessBase
    0 4 0x83000 0x88000 ready (by decide) (Or.inl rfl) treeBound
    witnessBound witnessAligned (by decide) (by decide)
    (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨at2,trace1,ready2,_,_⟩ := height_step hash at1 3 treeBase
    witnessBase 1 2 0x88000 0x83000
    (by simpa only [show 4/2=2 by decide] using ready1)
    (by decide) (Or.inl rfl) treeBound witnessBound witnessAligned
    (by decide) (by decide) (Or.inr ⟨rfl,rfl⟩)
  obtain ⟨built,trace2,_,_,_,_⟩ :=
    GroupedBalancedSignUpperTreeTerminalTrace67.terminal hash at2 3 treeBase
      witnessBase 2 0x83000 0x88000
      (by simpa only [show 2/2=1 by decide] using ready2)
      (by decide) (Or.inl rfl) treeBound witnessBound witnessAligned
      (Or.inl ⟨rfl,rfl⟩)
  have builtTrace : Trace hash image s 882 931 7 7 built := by
    have combined := (trace0.trans trace1).trans trace2
    convert combined using 1 <;> decide
  have same := Trace.deterministic trace builtTrace
  rw [same]
  have f0 := height_step_frame hash s at1 3 treeBase witnessBase
    0 4 0x83000 0x88000 ready (by decide) (Or.inl rfl)
    witnessBound witnessAligned (by decide) (by decide)
    (Or.inl ⟨rfl,rfl⟩) trace0 a safe
  have f1 := height_step_frame hash at1 at2 3 treeBase witnessBase
    1 2 0x88000 0x83000
    (by simpa only [show 4/2=2 by decide] using ready1)
    (by decide) (Or.inl rfl) witnessBound witnessAligned
    (by decide) (by decide) (Or.inr ⟨rfl,rfl⟩) trace1 a safe
  have f2 := terminal_frame hash at2 built 3 treeBase witnessBase
    2 0x83000 0x88000
    (by simpa only [show 2/2=1 by decide] using ready2)
    (by decide) (Or.inl rfl) witnessBound witnessAligned
    (Or.inl ⟨rfl,rfl⟩) trace2 a safe
  exact f2.trans (f1.trans f0)

#print axioms height3_frame

theorem height4_frame (hash : Hash) (s final : MachineState)
    (treeBase witnessBase : Nat)
    (ready : Ready 4 treeBase witnessBase 0 8 0x83000 0x88000 s)
    (treeBound : treeBase+4<2^64)
    (witnessBound : witnessBase+16*4+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (trace : Trace hash image s 1668 1773 15 15 final)
    (a : Word) (safe : Safe a) : final.getMem a=s.getMem a := by
  obtain ⟨at1,trace0,ready1,_,_⟩ := height_step hash s 4 treeBase witnessBase
    0 8 0x83000 0x88000 ready (by decide) (Or.inr rfl) treeBound
    witnessBound witnessAligned (by decide) (by decide)
    (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨at2,trace1,ready2,_,_⟩ := height_step hash at1 4 treeBase
    witnessBase 1 4 0x88000 0x83000
    (by simpa only [show 8/2=4 by decide] using ready1)
    (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
    (by decide) (by decide) (Or.inr ⟨rfl,rfl⟩)
  obtain ⟨at3,trace2,ready3,_,_⟩ := height_step hash at2 4 treeBase
    witnessBase 2 2 0x83000 0x88000
    (by simpa only [show 4/2=2 by decide] using ready2)
    (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
    (by decide) (by decide) (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨built,trace3,_,_,_,_⟩ :=
    GroupedBalancedSignUpperTreeTerminalTrace67.terminal hash at3 4 treeBase
      witnessBase 3 0x88000 0x83000
      (by simpa only [show 2/2=1 by decide] using ready3)
      (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
      (Or.inr ⟨rfl,rfl⟩)
  have builtTrace : Trace hash image s 1668 1773 15 15 built := by
    have combined := ((trace0.trans trace1).trans trace2).trans trace3
    convert combined using 1 <;> decide
  have same := Trace.deterministic trace builtTrace
  rw [same]
  have f0 := height_step_frame hash s at1 4 treeBase witnessBase
    0 8 0x83000 0x88000 ready (by decide) (Or.inr rfl)
    witnessBound witnessAligned (by decide) (by decide)
    (Or.inl ⟨rfl,rfl⟩) trace0 a safe
  have f1 := height_step_frame hash at1 at2 4 treeBase witnessBase
    1 4 0x88000 0x83000
    (by simpa only [show 8/2=4 by decide] using ready1)
    (by decide) (Or.inr rfl) witnessBound witnessAligned
    (by decide) (by decide) (Or.inr ⟨rfl,rfl⟩) trace1 a safe
  have f2 := height_step_frame hash at2 at3 4 treeBase witnessBase
    2 2 0x83000 0x88000
    (by simpa only [show 4/2=2 by decide] using ready2)
    (by decide) (Or.inr rfl) witnessBound witnessAligned
    (by decide) (by decide) (Or.inl ⟨rfl,rfl⟩) trace2 a safe
  have f3 := terminal_frame hash at3 built 4 treeBase witnessBase
    3 0x88000 0x83000
    (by simpa only [show 2/2=1 by decide] using ready3)
    (by decide) (Or.inr rfl) witnessBound witnessAligned
    (Or.inr ⟨rfl,rfl⟩) trace3 a safe
  exact f3.trans (f2.trans (f1.trans f0))

#print axioms height4_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeParentsFrame67

end

/-! The final byte-image upper Merkle callee preserves next-group controls. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCalleeFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeControlFrame67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev oldImage := GroupedBalancedSignImage67.image

theorem height3_frame (hash : Hash) (s returned : MachineState)
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
    (a : Word) (safe : Safe a) : returned.getMem a=s.getMem a := by
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
  exact (GroupedBalancedSignUpperTreeParentsFrame67.height3_frame hash ready
    final treeBase witnessBase startInv treeBound witnessBound witnessAligned
    parentTrace a safe).trans
    (start_frame hash s ready pc sp startTrace a safe)

#print axioms height3_frame

theorem height4_frame (hash : Hash) (s returned : MachineState)
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
    (a : Word) (safe : Safe a) : returned.getMem a=s.getMem a := by
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
  exact (GroupedBalancedSignUpperTreeParentsFrame67.height4_frame hash ready
    final treeBase witnessBase startInv treeBound witnessBound witnessAligned
    parentTrace a safe).trans
    (start_frame hash s ready pc sp startTrace a safe)

#print axioms height4_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCalleeFrame67
