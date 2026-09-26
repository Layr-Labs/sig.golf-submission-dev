import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeStart67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeReturn67

/-! Exact h3/h4 upper Merkle subroutine traces, including its caller return. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCallee67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

theorem return_valid (s : MachineState)
    (sp : s.getReg .x2=0xfff7e0 ∨ s.getReg .x2=0xfff700) :
    accessValid (s.getReg .x2-16) 8=true := by
  rcases sp with h|h <;> rw [h] <;>
    decide

theorem return_after (hash : Hash) (s ready final : MachineState)
    (sp : s.getReg .x2=0xfff7e0 ∨ s.getReg .x2=0xfff700)
    (slot : ready.getMem (s.getReg .x2-16)=0x1c34)
    (readySp : ready.getReg .x2=s.getReg .x2-16)
    (finalSp : final.getReg .x2=ready.getReg .x2)
    (finalHigh : ∀ a : Word, 0x90000 ≤ a.toNat →
      final.getMem a=ready.getMem a)
    (finalPc : final.pc=0x20ec) :
    Trace hash image final 3 3 0 0 (Keygen.returnState final) ∧
    (Keygen.returnState final).pc=0x1c34 ∧
    (Keygen.returnState final).getReg .x2=s.getReg .x2 := by
  have high : 0x90000 ≤ (s.getReg .x2-16).toNat := by
    rcases sp with h|h <;> rw [h] <;> decide
  have finalSlot : final.getMem (final.getReg .x2)=0x1c34 := by
    rw [finalSp,readySp,finalHigh _ high]
    exact slot
  have valid : accessValid (final.getReg .x2) 8=true := by
    rw [finalSp,readySp]
    exact return_valid s sp
  refine ⟨GroupedBalancedSignBottomTreeReturn67.return_trace hash final
    finalPc valid,?_,?_⟩
  · rw [Keygen.return_pc,finalSlot]
    decide
  · rw [Keygen.return_sp,finalSp,readySp]
    exact BitVec.sub_add_cancel (s.getReg .x2) 16

theorem height3 (hash : Hash) (s : MachineState)
    (treeBase witnessBase : Nat)
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
    ∃ returned : MachineState,
      Trace hash image s 957 1006 7 7 returned ∧
      returned.pc=0x1c34 ∧
      returned.getReg .x2=s.getReg .x2 ∧
      returned.getMem 0x810c0=0x88000 := by
  obtain ⟨ready,startTrace,readyInv,readySp,slot⟩ :=
    GroupedBalancedSignUpperTreeStart67.start hash s 3 treeBase witnessBase 4
      pc sp tree maxLevel witness selected count (by decide)
  obtain ⟨final,parentTrace,finalPc,rootPtr,finalSp,finalHigh⟩ :=
    GroupedBalancedSignUpperTreeAllTrace67.height3 hash ready treeBase
      witnessBase readyInv treeBound witnessBound witnessAligned
  obtain ⟨returnTrace,returnPc,returnSp⟩ :=
    return_after hash s ready final sp slot readySp finalSp finalHigh finalPc
  refine ⟨Keygen.returnState final,?_,returnPc,returnSp,?_⟩
  · have combined := (startTrace.trans parentTrace).trans returnTrace
    convert combined using 1 <;> decide
  · rw [Keygen.return_mem]
    exact rootPtr

theorem height4 (hash : Hash) (s : MachineState)
    (treeBase witnessBase : Nat)
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
    ∃ returned : MachineState,
      Trace hash image s 1743 1848 15 15 returned ∧
      returned.pc=0x1c34 ∧
      returned.getReg .x2=s.getReg .x2 ∧
      returned.getMem 0x810c0=0x83000 := by
  obtain ⟨ready,startTrace,readyInv,readySp,slot⟩ :=
    GroupedBalancedSignUpperTreeStart67.start hash s 4 treeBase witnessBase 8
      pc sp tree maxLevel witness selected count (by decide)
  obtain ⟨final,parentTrace,finalPc,rootPtr,finalSp,finalHigh⟩ :=
    GroupedBalancedSignUpperTreeAllTrace67.height4 hash ready treeBase
      witnessBase readyInv treeBound witnessBound witnessAligned
  obtain ⟨returnTrace,returnPc,returnSp⟩ :=
    return_after hash s ready final sp slot readySp finalSp finalHigh finalPc
  refine ⟨Keygen.returnState final,?_,returnPc,returnSp,?_⟩
  · have combined := (startTrace.trans parentTrace).trans returnTrace
    convert combined using 1 <;> decide
  · rw [Keygen.return_mem]
    exact rootPtr

#print axioms height3
#print axioms height4
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCallee67
