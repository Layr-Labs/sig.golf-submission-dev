import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeStartStack67

/-! The complete ten-level signer tree preserves its caller's stack slot and H5 index. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeCompleteStack67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomTreeParentFold67
open GroupedBalancedSignBottomTreeParentProtected67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

theorem bottom_tree_stack (hash : Hash) (secretKey : SecretKey)
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
            (64*i.val) 64) ∧
      final.getReg .x2 = s.getReg .x2 - 16 ∧
      final.getMem (s.getReg .x2 - 16) = 0x14f0 ∧
      (∀ a, Protected a → a ≠ s.getReg .x2 - 16 →
        final.getMem a = s.getMem a) ∧
      final.getMem 0x81000=10 := by
  obtain ⟨start,first,params,startInv,startSp,saved,startFrame⟩ :=
    GroupedBalancedSignBottomTreeStartStack67.start_stack hash secretKey base s
      pc sp aligned bounded count height maxLevel witnessBase selectedBound
      scratch leafWords
  obtain ⟨final,rest,finalPc,source,rootWords,restFrame,restSp,
    restTree⟩ :=
    GroupedBalancedSignBottomTreeAllStack67.ten_levels_stack hash secretKey
      base 512 0x88000 (base/2) start params startInv
  have slotHigh : 0x90000 ≤ (s.getReg .x2 - 16).toNat := by
    rcases sp with h | h <;> rw [h] <;> decide
  refine ⟨final,?_,finalPc,source,rootWords,restSp.trans startSp,?_,?_,
    restTree⟩
  · simpa [image] using first.trans rest
  · exact (restFrame _ (Or.inl slotHigh)).trans saved
  · intro a safe neSlot
    exact (restFrame a safe).trans (startFrame a safe neSlot)

#print axioms bottom_tree_stack
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeCompleteStack67
