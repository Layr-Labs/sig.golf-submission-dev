import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperAllTreeWord67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeByteCallee67

/-! The returned Merkle callee exposes the advanced absolute tree level. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCalleeTreeWord67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev oldImage := GroupedBalancedSignImage67.image

theorem height3 (hash : Hash) (s returned : MachineState)
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
    (witnessAligned : witnessBase%8=0) :
    returned.getMem 0x81000=BitVec.ofNat 64 (treeBase+3) := by
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
  exact GroupedBalancedSignUpperAllTreeWord67.height3 hash ready final
    treeBase witnessBase startInv treeBound witnessBound witnessAligned
    parentTrace

theorem height4 (hash : Hash) (s returned : MachineState)
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
    (witnessAligned : witnessBase%8=0) :
    returned.getMem 0x81000=BitVec.ofNat 64 (treeBase+4) := by
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
  exact GroupedBalancedSignUpperAllTreeWord67.height4 hash ready final
    treeBase witnessBase startInv treeBound witnessBound witnessAligned
    parentTrace

#print axioms height3
#print axioms height4
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCalleeTreeWord67
