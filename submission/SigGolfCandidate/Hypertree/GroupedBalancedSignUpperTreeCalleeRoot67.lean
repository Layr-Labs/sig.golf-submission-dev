import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeStartData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCallee67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCalleeData67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCalleeRoot67. -/
section
/-! Functional h3/h4 upper Merkle callee from leaf table to returned root. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCalleeData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeParentData67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev node := GroupedBalancedSignUpperTreeModel67.nodeAt

theorem height3 (hash : Hash) (treeBase leafBase witnessBase : Nat)
    (leaves : Nat → Reference.Digest) (s : MachineState)
    (pc : s.pc=0x1c30)
    (sp : s.getReg .x2=0xfff7e0 ∨ s.getReg .x2=0xfff700)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (maxLevel : s.getMem 0x81060=3)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (selected : (s.getMem 0x810e8).toNat<1024)
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
    ∃ returned : MachineState,
      Trace hash image s 957 1006 7 7 returned ∧
      returned.pc=0x1c34 ∧ returned.getReg .x2=s.getReg .x2 ∧
      returned.getMem 0x810c0=0x88000 ∧
      (∀ i : Fin 2,
        returned.getMem (BitVec.ofNat 64 (0x88000+8*i.val))=
          (node hash treeBase leafBase leaves 3 0).extractLsb'
            (64*i.val) 64) := by
  obtain ⟨ready,startTrace,startInv,readySp,slot⟩ :=
    GroupedBalancedSignUpperTreeStartData67.start_data hash treeBase
      leafBase witnessBase 4 3 leaves s pc sp tree maxLevel witness selected
      count (by decide) leafBound scratch leavesReady
  obtain ⟨final,parentTrace,finalPc,rootPtr,rootWords⟩ :=
    GroupedBalancedSignUpperTreeAllData67.height3 hash treeBase leafBase
      witnessBase (leafBase/2) leaves ready params startInv treeBound
      witnessBound witnessAligned
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
  obtain ⟨returnTrace,returnPc,returnSp⟩ :=
    GroupedBalancedSignUpperTreeCallee67.return_after hash s ready final sp
      slot readySp finalSp' finalHigh' finalPc
  refine ⟨Keygen.returnState final,?_,returnPc,returnSp,?_,?_⟩
  · have combined := (startTrace.trans parentTrace).trans returnTrace
    convert combined using 1 <;> decide
  · rw [Keygen.return_mem]
    exact rootPtr
  · intro i
    rw [Keygen.return_mem]
    exact rootWords i

theorem height4 (hash : Hash) (treeBase leafBase witnessBase : Nat)
    (leaves : Nat → Reference.Digest) (s : MachineState)
    (pc : s.pc=0x1c30)
    (sp : s.getReg .x2=0xfff7e0 ∨ s.getReg .x2=0xfff700)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (maxLevel : s.getMem 0x81060=4)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (selected : (s.getMem 0x810e8).toNat<1024)
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
    ∃ returned : MachineState,
      Trace hash image s 1743 1848 15 15 returned ∧
      returned.pc=0x1c34 ∧ returned.getReg .x2=s.getReg .x2 ∧
      returned.getMem 0x810c0=0x83000 ∧
      (∀ i : Fin 2,
        returned.getMem (BitVec.ofNat 64 (0x83000+8*i.val))=
          (node hash treeBase leafBase leaves 4 0).extractLsb'
            (64*i.val) 64) := by
  obtain ⟨ready,startTrace,startInv,readySp,slot⟩ :=
    GroupedBalancedSignUpperTreeStartData67.start_data hash treeBase
      leafBase witnessBase 8 4 leaves s pc sp tree maxLevel witness selected
      count (by decide) leafBound scratch leavesReady
  obtain ⟨final,parentTrace,finalPc,rootPtr,rootWords⟩ :=
    GroupedBalancedSignUpperTreeAllData67.height4 hash treeBase leafBase
      witnessBase (leafBase/2) leaves ready params startInv treeBound
      witnessBound witnessAligned
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
  obtain ⟨returnTrace,returnPc,returnSp⟩ :=
    GroupedBalancedSignUpperTreeCallee67.return_after hash s ready final sp
      slot readySp finalSp' finalHigh' finalPc
  refine ⟨Keygen.returnState final,?_,returnPc,returnSp,?_,?_⟩
  · have combined := (startTrace.trans parentTrace).trans returnTrace
    convert combined using 1 <;> decide
  · rw [Keygen.return_mem]
    exact rootPtr
  · intro i
    rw [Keygen.return_mem]
    exact rootWords i

#print axioms height3
#print axioms height4
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCalleeData67

end

/-! Identify the machine's upper Merkle root with the scheme root. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCalleeRoot67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeParentData67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

theorem height3_root (hash : Hash) (secretKey : SecretKey)
    (treeBase rootAddress witnessBase : Nat) (s : MachineState)
    (pc : s.pc=0x1c30)
    (sp : s.getReg .x2=0xfff7e0 ∨ s.getReg .x2=0xfff700)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (maxLevel : s.getMem 0x81060=3)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (selected : (s.getMem 0x810e8).toNat<1024)
    (count : s.getMem 0x810d0=8)
    (leafBound : rootAddress*2^3<2^192)
    (params : Params (rootAddress*2^3) 0 4 0x83000 0x88000
      ((rootAddress*2^3)/2))
    (scratch : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x810a8 i.val)=
        (BitVec.ofNat 192 (rootAddress*2^3)).extractLsb'
          (64*i.val) 64)
    (leavesReady : ∀ j, j<8 → ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (0x83000+16*j+8*i.val))=
        (GroupedBalancedUpperTree67.leafRoot hash secretKey treeBase
          (rootAddress*2^3+j)).extractLsb' (64*i.val) 64)
    (treeBound : treeBase+3<2^64)
    (witnessBound : witnessBase+16*3+16≤0x80000)
    (witnessAligned : witnessBase%8=0) :
    ∃ returned : MachineState,
      Trace hash image s 957 1006 7 7 returned ∧
      returned.pc=0x1c34 ∧ returned.getReg .x2=s.getReg .x2 ∧
      returned.getMem 0x810c0=0x88000 ∧
      (∀ i : Fin 2,
        returned.getMem (BitVec.ofNat 64 (0x88000+8*i.val))=
          (GroupedBalancedUpperTree67.root hash secretKey treeBase 3
            rootAddress).extractLsb' (64*i.val) 64) := by
  obtain ⟨returned,trace,pcDone,spDone,ptr,words⟩ :=
    GroupedBalancedSignUpperTreeCalleeData67.height3 hash treeBase
      (rootAddress*2^3) witnessBase
      (fun j => GroupedBalancedUpperTree67.leafRoot hash secretKey treeBase
        (rootAddress*2^3+j)) s pc sp tree maxLevel witness selected count
      leafBound params scratch leavesReady treeBound witnessBound
      witnessAligned
  refine ⟨returned,trace,pcDone,spDone,ptr,?_⟩
  intro i
  rw [words i]
  change (GroupedBalancedSignUpperTreeModel67.nodeAt hash treeBase
    (rootAddress*2^3)
    (fun j => GroupedBalancedUpperTree67.leafRoot hash secretKey treeBase
      (rootAddress*2^3+j)) 3 0).extractLsb' (64*i.val) 64 = _
  rw [GroupedBalancedSignUpperTreeModel67.node_eq_upper_root]

theorem height4_root (hash : Hash) (secretKey : SecretKey)
    (treeBase rootAddress witnessBase : Nat) (s : MachineState)
    (pc : s.pc=0x1c30)
    (sp : s.getReg .x2=0xfff7e0 ∨ s.getReg .x2=0xfff700)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (maxLevel : s.getMem 0x81060=4)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (selected : (s.getMem 0x810e8).toNat<1024)
    (count : s.getMem 0x810d0=16)
    (leafBound : rootAddress*2^4<2^192)
    (params : Params (rootAddress*2^4) 0 8 0x83000 0x88000
      ((rootAddress*2^4)/2))
    (scratch : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x810a8 i.val)=
        (BitVec.ofNat 192 (rootAddress*2^4)).extractLsb'
          (64*i.val) 64)
    (leavesReady : ∀ j, j<16 → ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (0x83000+16*j+8*i.val))=
        (GroupedBalancedUpperTree67.leafRoot hash secretKey treeBase
          (rootAddress*2^4+j)).extractLsb' (64*i.val) 64)
    (treeBound : treeBase+4<2^64)
    (witnessBound : witnessBase+16*4+16≤0x80000)
    (witnessAligned : witnessBase%8=0) :
    ∃ returned : MachineState,
      Trace hash image s 1743 1848 15 15 returned ∧
      returned.pc=0x1c34 ∧ returned.getReg .x2=s.getReg .x2 ∧
      returned.getMem 0x810c0=0x83000 ∧
      (∀ i : Fin 2,
        returned.getMem (BitVec.ofNat 64 (0x83000+8*i.val))=
          (GroupedBalancedUpperTree67.root hash secretKey treeBase 4
            rootAddress).extractLsb' (64*i.val) 64) := by
  obtain ⟨returned,trace,pcDone,spDone,ptr,words⟩ :=
    GroupedBalancedSignUpperTreeCalleeData67.height4 hash treeBase
      (rootAddress*2^4) witnessBase
      (fun j => GroupedBalancedUpperTree67.leafRoot hash secretKey treeBase
        (rootAddress*2^4+j)) s pc sp tree maxLevel witness selected count
      leafBound params scratch leavesReady treeBound witnessBound
      witnessAligned
  refine ⟨returned,trace,pcDone,spDone,ptr,?_⟩
  intro i
  rw [words i]
  change (GroupedBalancedSignUpperTreeModel67.nodeAt hash treeBase
    (rootAddress*2^4)
    (fun j => GroupedBalancedUpperTree67.leafRoot hash secretKey treeBase
      (rootAddress*2^4+j)) 4 0).extractLsb' (64*i.val) 64 = _
  rw [GroupedBalancedSignUpperTreeModel67.node_eq_upper_root]

#print axioms height3_root
#print axioms height4_root
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCalleeRoot67
