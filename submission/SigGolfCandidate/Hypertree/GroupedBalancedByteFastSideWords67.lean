import SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeRoute67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastCopyWords67


/-! The sibling-load tail writes exactly one two-word child buffer. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastRouteWords67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeRoute67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem route_mem (s : MachineState) (dst : BitVec 12) (a : Word) :
    (routeState s dst).getMem a =
      if a = (0x80000 : Word) + signExtend12 dst + 8 then
        s.getMem (s.getMem 0x81048 + 8)
      else if a = (0x80000 : Word) + signExtend12 dst then
        s.getMem (s.getMem 0x81048)
      else s.getMem a := by
  simp [routeState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq, MachineState.getMem_setMem_ne]
  rfl

theorem right_route_words (s : MachineState) (i : Fin 4) :
    (execInstrBr (routeState s 0x520) (.JAL .x0 84)).getMem
      (Signing.wordAddress 0x80520 i.val) =
      if i.val < 2 then
        s.getMem (s.getMem 0x81048 + BitVec.ofNat 64 (8*i.val))
      else s.getMem (Signing.wordAddress 0x80520 i.val) := by
  fin_cases i <;> simp [route_mem, Signing.wordAddress,
    execInstrBr, signExtend12]

theorem left_route_words (s : MachineState) (i : Fin 4) :
    (routeState s 0x530).getMem
      (Signing.wordAddress 0x80520 i.val) =
      if i.val < 2 then s.getMem (Signing.wordAddress 0x80520 i.val)
      else s.getMem
        (s.getMem 0x81048 + BitVec.ofNat 64 (8*(i.val-2))) := by
  fin_cases i <;> simp [route_mem, Signing.wordAddress, signExtend12]

#print axioms route_mem
#print axioms right_route_words
#print axioms left_route_words

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastRouteWords67


/-! Functional left/right child arrangement before the node hash. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastSideWords67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastCopies67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastCopyWords67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastRouteWords67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def image : Image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem right_side_words (hash : Hash) (s : MachineState)
    (left right : Reference.Digest)
    (pc : s.pc = 0x17dc)
    (ptr0 : accessValid (s.getMem 0x81048) 8 = true)
    (ptr8 : accessValid (s.getMem 0x81048 + 8) 8 = true)
    (root : ∀ half : Fin 2,
      s.getMem (Signing.wordAddress 0x80500 half.val) =
        right.extractLsb' (64*half.val) 64)
    (sibling : ∀ half : Fin 2,
      s.getMem (s.getMem 0x81048 + BitVec.ofNat 64 (8*half.val)) =
        left.extractLsb' (64*half.val) 64)
    (separate : ∀ half : Fin 2, ∀ i, i < 2 →
      s.getMem 0x81048 + BitVec.ofNat 64 (8*half.val) ≠
        Signing.wordAddress 0x80530 i) :
    ∃ arranged,
      Trace hash image s 27 27 0 0 arranged ∧
      arranged.pc = 0x1880 ∧
      (∀ i : Fin 4,
        arranged.getMem (Signing.wordAddress 0x80520 i.val) =
          if i.val < 2 then left.extractLsb' (64*i.val) 64
          else right.extractLsb' (64*(i.val-2)) 64) ∧
      (∀ a : Word,
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80520 i.val) →
        arranged.getMem a = s.getMem a) := by
  obtain ⟨copied,first,inv,words,frame⟩ :=
    run_copy_words hash s 0x17dc 0x500 0x530 2
      0x80500 0x80530 2 witness_copy_code.1 witness_copy_code.2
      pc
      (by simp [setup_reg,signExtend12])
      (by simp [setup_reg,signExtend12])
      (by simp [setup_reg,signExtend12])
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (Or.inl (by decide))
  have copiedPC : copied.pc = 0x1808 := by
    have h := inv.2.2.1
    simpa [Keygen.CopyInvariant] using h
  have copiedPtr : copied.getMem 0x81048 = s.getMem 0x81048 := by
    exact frame 0x81048 (by intro i hi; interval_cases i <;> decide)
  have copiedRoot : ∀ half : Fin 2,
      copied.getMem (Signing.wordAddress 0x80530 half.val) =
        right.extractLsb' (64*half.val) 64 := by
    intro half
    rw [words half.val half.isLt]
    exact root half
  have copiedSibling : ∀ half : Fin 2,
      copied.getMem
        (copied.getMem 0x81048 + BitVec.ofNat 64 (8*half.val)) =
        left.extractLsb' (64*half.val) 64 := by
    intro half
    rw [copiedPtr]
    rw [frame _ (separate half)]
    exact sibling half
  have second := GroupedBalancedByteFastEdgeRoute67.right_route
    hash copied copiedPC (by rw [copiedPtr]; exact ptr0)
      (by rw [copiedPtr]; exact ptr8)
  let arranged := execInstrBr
    (GroupedBalancedByteFastEdgeRoute67.routeState copied 0x520)
    (.JAL .x0 84)
  refine ⟨arranged,?_,second.2,?_,?_⟩
  · have path := first.trans second.1
    simpa [arranged,image,GroupedBalancedByteFastCopies67.image,
      GroupedBalancedByteFastEdgeRoute67.image] using path
  · intro i
    change (execInstrBr
      (GroupedBalancedByteFastEdgeRoute67.routeState copied 0x520)
      (.JAL .x0 84)).getMem (Signing.wordAddress 0x80520 i.val) = _
    rw [right_route_words copied i]
    fin_cases i
    · simpa [Signing.wordAddress] using copiedSibling 0
    · simpa [Signing.wordAddress] using copiedSibling 1
    · simpa [Signing.wordAddress] using copiedRoot 0
    · simpa [Signing.wordAddress] using copiedRoot 1
  · intro a outside
    have routed : arranged.getMem a = copied.getMem a := by
      change (execInstrBr
        (GroupedBalancedByteFastEdgeRoute67.routeState copied 0x520)
        (.JAL .x0 84)).getMem a = copied.getMem a
      simp only [execInstrBr, MachineState.getMem_setPC,
        MachineState.getMem_setReg]
      rw [route_mem]
      have h0 : a ≠ (0x80000 : Word) + signExtend12 (0x520 : BitVec 12) := by
        simpa [Signing.wordAddress,signExtend12] using outside (0 : Fin 4)
      have h1 : a ≠ (0x80000 : Word) + signExtend12 (0x520 : BitVec 12) + 8 := by
        simpa [Signing.wordAddress,signExtend12] using outside (1 : Fin 4)
      by_cases e1 : a = (0x80000 : Word) +
          signExtend12 (0x520 : BitVec 12) + 8
      · exact False.elim (h1 e1)
      · rw [if_neg e1]
        by_cases e0 : a = (0x80000 : Word) +
            signExtend12 (0x520 : BitVec 12)
        · exact False.elim (h0 e0)
        · rw [if_neg e0]
    rw [routed]
    apply frame a
    intro i hi
    interval_cases i
    · simpa [Signing.wordAddress] using outside (2 : Fin 4)
    · simpa [Signing.wordAddress] using outside (3 : Fin 4)

#print axioms right_side_words

theorem left_side_words (hash : Hash) (s : MachineState)
    (left right : Reference.Digest)
    (pc : s.pc = 0x1830)
    (ptr0 : accessValid (s.getMem 0x81048) 8 = true)
    (ptr8 : accessValid (s.getMem 0x81048 + 8) 8 = true)
    (root : ∀ half : Fin 2,
      s.getMem (Signing.wordAddress 0x80500 half.val) =
        left.extractLsb' (64*half.val) 64)
    (sibling : ∀ half : Fin 2,
      s.getMem (s.getMem 0x81048 + BitVec.ofNat 64 (8*half.val)) =
        right.extractLsb' (64*half.val) 64)
    (separate : ∀ half : Fin 2, ∀ i, i < 2 →
      s.getMem 0x81048 + BitVec.ofNat 64 (8*half.val) ≠
        Signing.wordAddress 0x80520 i) :
    ∃ arranged,
      Trace hash image s 26 26 0 0 arranged ∧
      arranged.pc = 0x1880 ∧
      (∀ i : Fin 4,
        arranged.getMem (Signing.wordAddress 0x80520 i.val) =
          if i.val < 2 then left.extractLsb' (64*i.val) 64
          else right.extractLsb' (64*(i.val-2)) 64) ∧
      (∀ a : Word,
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80520 i.val) →
        arranged.getMem a = s.getMem a) := by
  obtain ⟨copied,first,inv,words,frame⟩ :=
    run_copy_words hash s 0x1830 0x500 0x520 2
      0x80500 0x80520 2 sibling_copy_code.1 sibling_copy_code.2
      pc
      (by simp [setup_reg,signExtend12])
      (by simp [setup_reg,signExtend12])
      (by simp [setup_reg,signExtend12])
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (Or.inl (by decide))
  have copiedPC : copied.pc = 0x185c := by
    have h := inv.2.2.1
    simpa [Keygen.CopyInvariant] using h
  have copiedPtr : copied.getMem 0x81048 = s.getMem 0x81048 := by
    exact frame 0x81048 (by intro i hi; interval_cases i <;> decide)
  have copiedRoot : ∀ half : Fin 2,
      copied.getMem (Signing.wordAddress 0x80520 half.val) =
        left.extractLsb' (64*half.val) 64 := by
    intro half
    rw [words half.val half.isLt]
    exact root half
  have copiedSibling : ∀ half : Fin 2,
      copied.getMem
        (copied.getMem 0x81048 + BitVec.ofNat 64 (8*half.val)) =
        right.extractLsb' (64*half.val) 64 := by
    intro half
    rw [copiedPtr]
    rw [frame _ (separate half)]
    exact sibling half
  have second := GroupedBalancedByteFastEdgeRoute67.left_route
    hash copied copiedPC (by rw [copiedPtr]; exact ptr0)
      (by rw [copiedPtr]; exact ptr8)
  let arranged := GroupedBalancedByteFastEdgeRoute67.routeState copied 0x530
  refine ⟨arranged,?_,second.2,?_,?_⟩
  · have path := first.trans second.1
    simpa [arranged,image,GroupedBalancedByteFastCopies67.image,
      GroupedBalancedByteFastEdgeRoute67.image] using path
  · intro i
    change (GroupedBalancedByteFastEdgeRoute67.routeState copied 0x530).getMem
      (Signing.wordAddress 0x80520 i.val) = _
    rw [left_route_words copied i]
    fin_cases i
    · simpa [Signing.wordAddress] using copiedRoot 0
    · simpa [Signing.wordAddress] using copiedRoot 1
    · simpa [Signing.wordAddress] using copiedSibling 0
    · simpa [Signing.wordAddress] using copiedSibling 1
  · intro a outside
    have routed : arranged.getMem a = copied.getMem a := by
      change (GroupedBalancedByteFastEdgeRoute67.routeState copied 0x530).getMem a =
        copied.getMem a
      rw [route_mem]
      have h0 : a ≠ (0x80000 : Word) + signExtend12 (0x530 : BitVec 12) := by
        simpa [Signing.wordAddress,signExtend12] using outside (2 : Fin 4)
      have h1 : a ≠ (0x80000 : Word) + signExtend12 (0x530 : BitVec 12) + 8 := by
        simpa [Signing.wordAddress,signExtend12] using outside (3 : Fin 4)
      by_cases e1 : a = (0x80000 : Word) +
          signExtend12 (0x530 : BitVec 12) + 8
      · exact False.elim (h1 e1)
      · rw [if_neg e1]
        by_cases e0 : a = (0x80000 : Word) +
            signExtend12 (0x530 : BitVec 12)
        · exact False.elim (h0 e0)
        · rw [if_neg e0]
    rw [routed]
    apply frame a
    intro i hi
    interval_cases i
    · simpa [Signing.wordAddress] using outside (0 : Fin 4)
    · simpa [Signing.wordAddress] using outside (1 : Fin 4)

#print axioms left_side_words

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastSideWords67
