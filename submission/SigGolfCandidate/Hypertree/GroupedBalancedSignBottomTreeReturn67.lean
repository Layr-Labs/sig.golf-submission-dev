import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeStart67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeAllLevels67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeBufferParity67
import SigGolfCandidate.Hypertree.KeygenControl

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeComplete67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeReturn67. -/
section
/-! The signer builds its bottom root from the complete leaf table. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeComplete67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67.image

theorem bottom_tree (hash : Hash) (secretKey : SecretKey)
    (base : Nat) (s : MachineState)
    (pc : s.pc = 0x14ec)
    (sp : s.getReg .x2 = 0xfff7e0 ∨ s.getReg .x2 = 0xfff700)
    (aligned : base % 1024 = 0)
    (bounded : base + 1024 ≤ 2^160)
    (count : s.getMem 0x810d0 = 1024)
    (height : s.getMem 0x81000 = 0)
    (maxLevel : s.getMem 0x81060 = 10)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (selectedBound : (s.getMem 0x810e8).toNat < 1024)
    (scratch : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x810a8 i.val) =
        (BitVec.ofNat 192 base).extractLsb' (64*i.val) 64)
    (leafWords : ∀ j, j < 1024 → ∀ i : Fin 2,
      s.getMem (GroupedBalancedSignBottomStackSlots67.slot j i.val) =
        (GroupedBottomTree.leafRoot hash secretKey (base+j)).extractLsb'
          (64*i.val) 64) :
    ∃ (final : MachineState) (rootBuffer : Nat),
      Trace hash image s 87096 94257 1023 1023 final ∧
      final.pc = 0x20ec ∧
      final.getMem 0x810c0 = BitVec.ofNat 64 rootBuffer ∧
      (∀ i : Fin 2,
        final.getMem (BitVec.ofNat 64 (rootBuffer+8*i.val)) =
          (GroupedBottomTree.root hash secretKey 10 (base/1024)).extractLsb'
            (64*i.val) 64) := by
  obtain ⟨start,entryTrace,params,startInv⟩ :=
    GroupedBalancedSignBottomTreeStart67.first_start hash secretKey base s
      pc sp aligned bounded count height maxLevel witnessBase selectedBound
      scratch leafWords
  obtain ⟨final,rootBuffer,treeTrace,finalPc,source,rootWords⟩ :=
    GroupedBalancedSignBottomTreeAllLevels67.ten_levels hash secretKey
      base 512 0x83000 0x88000 (base/2) start params startInv
  refine ⟨final,rootBuffer,?_,finalPc,source,rootWords⟩
  simpa [image] using entryTrace.trans treeTrace

theorem bottom_tree_fixed (hash : Hash) (secretKey : SecretKey)
    (base : Nat) (s : MachineState)
    (pc : s.pc = 0x14ec)
    (sp : s.getReg .x2 = 0xfff7e0 ∨ s.getReg .x2 = 0xfff700)
    (aligned : base % 1024 = 0)
    (bounded : base + 1024 ≤ 2^160)
    (count : s.getMem 0x810d0 = 1024)
    (height : s.getMem 0x81000 = 0)
    (maxLevel : s.getMem 0x81060 = 10)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (selectedBound : (s.getMem 0x810e8).toNat < 1024)
    (scratch : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x810a8 i.val) =
        (BitVec.ofNat 192 base).extractLsb' (64*i.val) 64)
    (leafWords : ∀ j, j < 1024 → ∀ i : Fin 2,
      s.getMem (GroupedBalancedSignBottomStackSlots67.slot j i.val) =
        (GroupedBottomTree.leafRoot hash secretKey (base+j)).extractLsb'
          (64*i.val) 64) :
    ∃ final : MachineState,
      Trace hash image s 87096 94257 1023 1023 final ∧
      final.pc = 0x20ec ∧
      final.getMem 0x810c0 = 0x83000 ∧
      (∀ i : Fin 2,
        final.getMem (BitVec.ofNat 64 (0x83000+8*i.val)) =
          (GroupedBottomTree.root hash secretKey 10 (base/1024)).extractLsb'
            (64*i.val) 64) := by
  obtain ⟨start,entryTrace,params,startInv⟩ :=
    GroupedBalancedSignBottomTreeStart67.first_start hash secretKey base s
      pc sp aligned bounded count height maxLevel witnessBase selectedBound
      scratch leafWords
  obtain ⟨final,treeTrace,finalPc,source,rootWords⟩ :=
    GroupedBalancedSignBottomTreeBufferParity67.ten_levels_fixed hash secretKey
      base 512 0x88000 (base/2) start params startInv
  refine ⟨final,?_,finalPc,source,rootWords⟩
  simpa [image] using entryTrace.trans treeTrace

#print axioms bottom_tree
#print axioms bottom_tree_fixed
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeComplete67

end

/-! The bottom-tree function restores its caller at the root buffer handoff. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeReturn67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67.image

theorem return_code : Keygen.ReturnCode image 0x20ec := by decide

theorem return_trace (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x20ec)
    (valid : accessValid (s.getReg .x2) 8 = true) :
    Trace hash image s 3 3 0 0 (Keygen.returnState s) := by
  exact (Keygen.return_block image 0x20ec return_code s pc valid).trace

theorem return_pc (s : MachineState)
    (link : s.getMem (s.getReg .x2) = 0x14f0) :
    (Keygen.returnState s).pc = 0x14f0 := by
  rw [Keygen.return_pc,link]
  decide

theorem return_sp (s : MachineState) :
    (Keygen.returnState s).getReg .x2 = s.getReg .x2 + 16 :=
  Keygen.return_sp s

theorem return_mem (s : MachineState) (a : Word) :
    (Keygen.returnState s).getMem a = s.getMem a :=
  Keygen.return_mem s a

#print axioms return_trace
#print axioms return_pc
#print axioms return_sp
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeReturn67
