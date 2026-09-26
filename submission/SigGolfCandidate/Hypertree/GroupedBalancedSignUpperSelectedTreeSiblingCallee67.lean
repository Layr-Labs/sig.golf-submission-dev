import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingAllData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeByteCallee67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeStartData67

/-! Authentication siblings persist through the Merkle callee return. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingCallee67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeParentData67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev oldImage := GroupedBalancedSignImage67.image
private abbrev node := GroupedBalancedSignUpperTreeModel67.nodeAt

theorem height3 (hash : Hash) (treeBase leafBase witnessBase selected : Nat)
    (leaves : Nat → Reference.Digest) (s returned : MachineState)
    (trace : Trace hash image s 957 1006 7 7 returned)
    (pc : s.pc=0x1c30)
    (sp : s.getReg .x2=0xfff7e0 ∨ s.getReg .x2=0xfff700)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (maxLevel : s.getMem 0x81060=3)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (chosen : s.getMem 0x810e8=BitVec.ofNat 64 selected)
    (chosenBound : selected<2^3)
    (count : s.getMem 0x810d0=8)
    (leafBound : leafBase<2^192)
    (params : Params leafBase 0 4 0x83000 0x88000 (leafBase/2))
    (scratch : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x810a8 i.val)=
        (BitVec.ofNat 192 leafBase).extractLsb' (64*i.val) 64)
    (leavesReady : ∀ j, j<8 → ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (0x83000+16*j+8*i.val))=
        (leaves j).extractLsb' (64*i.val) 64)
    (treeBound : treeBase+3<2^64)
    (witnessBound : witnessBase+16*3+16≤0x80000)
    (witnessAligned : witnessBase%8=0) :
    ∀ level, level<3 → ∀ i : Fin 2,
      returned.getMem (BitVec.ofNat 64 (witnessBase+16*level+8*i.val))=
        (node hash treeBase leafBase leaves level
          (Nat.xor (selected/2^level) 1)).extractLsb' (64*i.val) 64 := by
  have selectedSmall : (s.getMem 0x810e8).toNat<1024 := by
    rw [chosen,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : selected<2^64)]
    omega
  obtain ⟨ready,startTrace,startInv,readySp,slot⟩ :=
    GroupedBalancedSignUpperTreeStartData67.start_data hash treeBase
      leafBase witnessBase 4 3 leaves s pc sp tree maxLevel witness
      selectedSmall count (by decide) leafBound scratch leavesReady
  have readyChosen : ready.getMem 0x810e8=BitVec.ofNat 64 selected :=
    (GroupedBalancedSignUpperTreeControlFrame67.start_frame hash s ready
      pc sp startTrace 0x810e8
      (by simp [GroupedBalancedSignUpperTreeControlFrame67.Safe])).trans
      chosen
  obtain ⟨final,parentTrace,finalPc,rootPtr,rootWords⟩ :=
    GroupedBalancedSignUpperTreeAllData67.height3 hash treeBase leafBase
      witnessBase (leafBase/2) leaves ready params startInv treeBound
      witnessBound witnessAligned
  have finalSiblings :=
    GroupedBalancedSignUpperSelectedTreeSiblingAllData67.height3 hash
      treeBase leafBase witnessBase (leafBase/2) selected leaves ready final
      params startInv readyChosen chosenBound treeBound witnessBound
      witnessAligned parentTrace
  obtain ⟨other,otherTrace,_,_,finalSp,finalHigh⟩ :=
    GroupedBalancedSignUpperTreeAllTrace67.height3 hash ready treeBase
      witnessBase startInv.ready treeBound witnessBound witnessAligned
  have same := Trace.deterministic parentTrace otherTrace
  have finalSp' : final.getReg .x2=ready.getReg .x2 := by
    rw [same]
    exact finalSp
  have finalHigh' : ∀ a : Word, 0x90000≤a.toNat →
      final.getMem a=ready.getMem a := by
    intro a high
    rw [same]
    exact finalHigh a high
  obtain ⟨returnTrace,_,_⟩ :=
    GroupedBalancedSignUpperTreeCallee67.return_after hash s ready final sp
      slot readySp finalSp' finalHigh' finalPc
  have oldTrace : Trace hash oldImage s 957 1006 7 7
      (Keygen.returnState final) := by
    have combined := (startTrace.trans parentTrace).trans returnTrace
    convert combined using 1 <;> decide
  have byteTrace :=
    GroupedBalancedSignUpperTreeByteCallee67.transfer_height3 hash s
      (Keygen.returnState final) treeBase witnessBase oldTrace pc sp
      tree maxLevel witness selectedSmall count treeBound witnessBound
      witnessAligned
  have sameReturned := Trace.deterministic trace byteTrace
  intro level levelBound i
  rw [sameReturned,Keygen.return_mem]
  exact finalSiblings level levelBound i

theorem height4 (hash : Hash) (treeBase leafBase witnessBase selected : Nat)
    (leaves : Nat → Reference.Digest) (s returned : MachineState)
    (trace : Trace hash image s 1743 1848 15 15 returned)
    (pc : s.pc=0x1c30)
    (sp : s.getReg .x2=0xfff7e0 ∨ s.getReg .x2=0xfff700)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (maxLevel : s.getMem 0x81060=4)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (chosen : s.getMem 0x810e8=BitVec.ofNat 64 selected)
    (chosenBound : selected<2^4)
    (count : s.getMem 0x810d0=16)
    (leafBound : leafBase<2^192)
    (params : Params leafBase 0 8 0x83000 0x88000 (leafBase/2))
    (scratch : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x810a8 i.val)=
        (BitVec.ofNat 192 leafBase).extractLsb' (64*i.val) 64)
    (leavesReady : ∀ j, j<16 → ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (0x83000+16*j+8*i.val))=
        (leaves j).extractLsb' (64*i.val) 64)
    (treeBound : treeBase+4<2^64)
    (witnessBound : witnessBase+16*4+16≤0x80000)
    (witnessAligned : witnessBase%8=0) :
    ∀ level, level<4 → ∀ i : Fin 2,
      returned.getMem (BitVec.ofNat 64 (witnessBase+16*level+8*i.val))=
        (node hash treeBase leafBase leaves level
          (Nat.xor (selected/2^level) 1)).extractLsb' (64*i.val) 64 := by
  have selectedSmall : (s.getMem 0x810e8).toNat<1024 := by
    rw [chosen,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : selected<2^64)]
    omega
  obtain ⟨ready,startTrace,startInv,readySp,slot⟩ :=
    GroupedBalancedSignUpperTreeStartData67.start_data hash treeBase
      leafBase witnessBase 8 4 leaves s pc sp tree maxLevel witness
      selectedSmall count (by decide) leafBound scratch leavesReady
  have readyChosen : ready.getMem 0x810e8=BitVec.ofNat 64 selected :=
    (GroupedBalancedSignUpperTreeControlFrame67.start_frame hash s ready
      pc sp startTrace 0x810e8
      (by simp [GroupedBalancedSignUpperTreeControlFrame67.Safe])).trans
      chosen
  obtain ⟨final,parentTrace,finalPc,rootPtr,rootWords⟩ :=
    GroupedBalancedSignUpperTreeAllData67.height4 hash treeBase leafBase
      witnessBase (leafBase/2) leaves ready params startInv treeBound
      witnessBound witnessAligned
  have finalSiblings :=
    GroupedBalancedSignUpperSelectedTreeSiblingAllData67.height4 hash
      treeBase leafBase witnessBase (leafBase/2) selected leaves ready final
      params startInv readyChosen chosenBound treeBound witnessBound
      witnessAligned parentTrace
  obtain ⟨other,otherTrace,_,_,finalSp,finalHigh⟩ :=
    GroupedBalancedSignUpperTreeAllTrace67.height4 hash ready treeBase
      witnessBase startInv.ready treeBound witnessBound witnessAligned
  have same := Trace.deterministic parentTrace otherTrace
  have finalSp' : final.getReg .x2=ready.getReg .x2 := by
    rw [same]
    exact finalSp
  have finalHigh' : ∀ a : Word, 0x90000≤a.toNat →
      final.getMem a=ready.getMem a := by
    intro a high
    rw [same]
    exact finalHigh a high
  obtain ⟨returnTrace,_,_⟩ :=
    GroupedBalancedSignUpperTreeCallee67.return_after hash s ready final sp
      slot readySp finalSp' finalHigh' finalPc
  have oldTrace : Trace hash oldImage s 1743 1848 15 15
      (Keygen.returnState final) := by
    have combined := (startTrace.trans parentTrace).trans returnTrace
    convert combined using 1 <;> decide
  have byteTrace :=
    GroupedBalancedSignUpperTreeByteCallee67.transfer_height4 hash s
      (Keygen.returnState final) treeBase witnessBase oldTrace pc sp
      tree maxLevel witness selectedSmall count treeBound witnessBound
      witnessAligned
  have sameReturned := Trace.deterministic trace byteTrace
  intro level levelBound i
  rw [sameReturned,Keygen.return_mem]
  exact finalSiblings level levelBound i

#print axioms height3
#print axioms height4
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingCallee67
