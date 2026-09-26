import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeBelow67

/-! Executable upper Merkle callee for the final byte-table signer image. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeByteCallee67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeParentData67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev oldImage := GroupedBalancedSignImage67.image

theorem transfer_height3 (hash : Hash) (s final : MachineState)
    (treeBase witnessBase : Nat)
    (trace : Trace hash oldImage s 957 1006 7 7 final)
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
    Trace hash image s 957 1006 7 7 final :=
  GroupedBalancedSignImageTransfer67.trace_transfer trace
    (GroupedBalancedSignUpperTreeBelow67.callee_height3_below hash s final
      treeBase witnessBase trace pc sp tree maxLevel witness selected count
      treeBound witnessBound witnessAligned)

theorem transfer_height4 (hash : Hash) (s final : MachineState)
    (treeBase witnessBase : Nat)
    (trace : Trace hash oldImage s 1743 1848 15 15 final)
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
    Trace hash image s 1743 1848 15 15 final :=
  GroupedBalancedSignImageTransfer67.trace_transfer trace
    (GroupedBalancedSignUpperTreeBelow67.callee_height4_below hash s final
      treeBase witnessBase trace pc sp tree maxLevel witness selected count
      treeBound witnessBound witnessAligned)

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
  obtain ⟨returned,oldTrace,pcDone,spDone,ptr,words⟩ :=
    GroupedBalancedSignUpperTreeCalleeRoot67.height3_root hash secretKey
      treeBase rootAddress witnessBase s pc sp tree maxLevel witness selected
      count leafBound params scratch leavesReady treeBound witnessBound
      witnessAligned
  exact ⟨returned,transfer_height3 hash s returned treeBase witnessBase
    oldTrace pc sp tree maxLevel witness selected count treeBound witnessBound
    witnessAligned,pcDone,spDone,ptr,words⟩

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
  obtain ⟨returned,oldTrace,pcDone,spDone,ptr,words⟩ :=
    GroupedBalancedSignUpperTreeCalleeRoot67.height4_root hash secretKey
      treeBase rootAddress witnessBase s pc sp tree maxLevel witness selected
      count leafBound params scratch leavesReady treeBound witnessBound
      witnessAligned
  exact ⟨returned,transfer_height4 hash s returned treeBase witnessBase
    oldTrace pc sp tree maxLevel witness selected count treeBound witnessBound
    witnessAligned,pcDone,spDone,ptr,words⟩

#print axioms height3_root
#print axioms height4_root
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeByteCallee67
