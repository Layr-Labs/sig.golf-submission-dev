import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelect67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomH2FromSeed67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomFirstH267. -/
section
/-! Any bottom H1 seed is copied into the H2 payload before the leaf call. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomH2FromSeed67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image

theorem input_to_leaf (hash : Hash) (s : MachineState)
    (leaf : Nat) (seed : Reference.Digest)
    (pc : s.pc = 0x13c4)
    (level : s.getMem 0x81000 = 0)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (seedWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80300 i.val) =
        seed.extractLsb' (64*i.val) 64) :
    ∃ staged ready after : MachineState,
      Trace hash image s 51 58 1 1 after ∧
      staged.pc = 0x13f0 ∧ ready.pc = 0x1474 ∧ after.pc = 0x1478 ∧
      hashInput ready = Reference.packed (KeygenDomain.payload
        (KeygenDomain.header 2 0 0 0 0) leaf seed) ∧
      (∀ i : Fin 2,
        after.getMem (Signing.wordAddress 0x80300 i.val) =
          (GroupedBottomTree.leafFromSeed hash leaf seed).extractLsb'
            (64*i.val) 64) ∧
      (∀ a : Word,
        a ≠ 0x80000 → a ≠ 0x80008 →
        a ≠ 0x80010 → a ≠ 0x80018 →
        (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80020 i.val) →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) →
        after.getMem a = s.getMem a) := by
  obtain ⟨staged,copied,stagedPc,inputWords,inputFrame⟩ :=
    GroupedBalancedSignBottomSeedCopies67.input_copy s pc
  have stagedLevel : staged.getMem 0x81000 = 0 := by
    rw [inputFrame _ (by intro i hi; interval_cases i <;> decide)]
    exact level
  have stagedAddress : ∀ i : Fin 3,
      staged.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64 := by
    intro i
    rw [inputFrame _
      (by intro j hj; fin_cases i <;> interval_cases j <;> decide)]
    exact address i
  have stagedSeed : ∀ i : Fin 2,
      staged.getMem (Signing.wordAddress 0x80020 i.val) =
        seed.extractLsb' (64*i.val) 64 := by
    intro i
    rw [inputWords i.val i.isLt]
    exact seedWords i
  let ready := GroupedBalancedSignBottomH2Prelude67.preludeState staged
  let after := writeHash ready (hash (hashInput ready))
  have query := GroupedBalancedSignBottomH2Query67.leaf_query staged
    leaf seed stagedLevel stagedAddress stagedSeed
  have answer := GroupedBalancedSignBottomH2Query67.leaf_answer hash staged
    leaf seed stagedLevel stagedAddress stagedSeed
  have call := GroupedBalancedSignBottomH2Query67.leaf_call hash staged stagedPc
  have readyPc := GroupedBalancedSignBottomH2Prelude67.prelude_pc staged stagedPc
  have afterPc : after.pc = 0x1478 := by
    change ready.pc + 4 = 0x1478
    rw [readyPc]
    decide
  refine ⟨staged,ready,after,?_,stagedPc,readyPc,afterPc,query,answer,?_⟩
  · simpa [image,Nat.add_comm,Nat.add_left_comm] using
      (OrdinarySteps.trace (hash := hash) copied).trans call
  · intro a h0 h1 h2 h3 hin hout
    rw [show after = writeHash ready (hash (hashInput ready)) from rfl,
      Signing.hash_answer_frame ready _
        (GroupedBalancedSignBottomH2Prelude67.prelude_hash_args staged).2.2.1
        a hout,
      GroupedBalancedSignBottomH2Prelude67.prelude_frame staged a h0 h1 h2 h3]
    exact inputFrame a (by intro i hi; exact hin ⟨i,hi⟩)

#print axioms input_to_leaf
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomH2FromSeed67

end

/-! The optional selected-seed copy followed by the first bottom leaf hash. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomFirstH267
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image

theorem first_leaf_h2 (hash : Hash) (s : MachineState)
    (leaf : Nat) (seed : Reference.Digest)
    (pc : s.pc = 0x137c)
    (level : s.getMem 0x81000 = 0)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (seedWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80300 i.val) =
        seed.extractLsb' (64*i.val) 64) :
    ∃ ready after : MachineState,
      Trace hash image s
        (if s.getMem 0x810e0 = s.getMem 0x810e8 then 75 else 58)
        (if s.getMem 0x810e0 = s.getMem 0x810e8 then 82 else 65)
        1 1 after ∧
      ready.pc = 0x1474 ∧ after.pc = 0x1478 ∧
      hashInput ready = Reference.packed (KeygenDomain.payload
        (KeygenDomain.header 2 0 0 0 0) leaf seed) ∧
      (∀ i : Fin 2,
        after.getMem (Signing.wordAddress 0x80300 i.val) =
          (GroupedBottomTree.leafFromSeed hash leaf seed).extractLsb'
            (64*i.val) 64) ∧
      (∀ a : Word,
        a ≠ 0x80000 → a ≠ 0x80008 →
        a ≠ 0x80010 → a ≠ 0x80018 →
        (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80020 i.val) →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) →
        (∀ i : Fin 2, a ≠ Signing.wordAddress 0x20080 i.val) →
        after.getMem a = s.getMem a) ∧
      (s.getMem 0x810e0 = s.getMem 0x810e8 →
        ∀ i : Fin 2,
          after.getMem (Signing.wordAddress 0x20080 i.val) =
            seed.extractLsb' (64*i.val) 64) ∧
      (s.getMem 0x810e0 ≠ s.getMem 0x810e8 →
        ∀ i : Fin 2,
          after.getMem (Signing.wordAddress 0x20080 i.val) =
            s.getMem (Signing.wordAddress 0x20080 i.val)) := by
  let routed := GroupedBalancedSignBottomSelect67.selectState s
  have route := GroupedBalancedSignBottomSelect67.select_steps s pc
  have routePc := GroupedBalancedSignBottomSelect67.select_pc s pc
  have routeLevel : routed.getMem 0x81000 = 0 := by
    rw [GroupedBalancedSignBottomSelect67.select_frame]
    exact level
  have routeAddress : ∀ i : Fin 3,
      routed.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64 := by
    intro i
    rw [GroupedBalancedSignBottomSelect67.select_frame]
    exact address i
  have routeSeed : ∀ i : Fin 2,
      routed.getMem (Signing.wordAddress 0x80300 i.val) =
        seed.extractLsb' (64*i.val) 64 := by
    intro i
    rw [GroupedBalancedSignBottomSelect67.select_frame]
    exact seedWords i
  by_cases selected : s.getMem 0x810e0 = s.getMem 0x810e8
  · have selectedPc : routed.pc = 0x1398 := by
      rw [routePc,if_pos selected]
    obtain ⟨copied,copyTrace,copiedPc,copyWords,copyFrame⟩ :=
      GroupedBalancedSignBottomSeedCopies67.selected_copy routed selectedPc
    have copiedLevel : copied.getMem 0x81000 = 0 := by
      rw [copyFrame _ (by intro i hi; interval_cases i <;> decide)]
      exact routeLevel
    have copiedAddress : ∀ i : Fin 3,
        copied.getMem (Signing.wordAddress 0x81008 i.val) =
          (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64 := by
      intro i
      rw [copyFrame _
        (by intro j hj; fin_cases i <;> interval_cases j <;> decide)]
      exact routeAddress i
    have copiedSeed : ∀ i : Fin 2,
        copied.getMem (Signing.wordAddress 0x80300 i.val) =
          seed.extractLsb' (64*i.val) 64 := by
      intro i
      rw [copyFrame _
        (by intro j hj; fin_cases i <;> interval_cases j <;> decide)]
      exact routeSeed i
    obtain ⟨staged,ready,after,h2,_,readyPc,afterPc,query,answer,frame⟩ :=
      GroupedBalancedSignBottomH2FromSeed67.input_to_leaf hash copied
        leaf seed copiedPc copiedLevel copiedAddress copiedSeed
    refine ⟨ready,after,?_,readyPc,afterPc,query,answer,?_,?_,?_⟩
    · simp only [if_pos selected]
      simpa [image,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (((OrdinarySteps.trace (hash := hash) route).trans
          (OrdinarySteps.trace (hash := hash) copyTrace)).trans h2)
    · intro a h0 h1 h2 h3 hin hout hwit
      rw [frame a h0 h1 h2 h3 hin hout,
        copyFrame a (by intro i hi; exact hwit ⟨i,hi⟩),
        GroupedBalancedSignBottomSelect67.select_frame s a]
    · intro _ i
      rw [frame _ (by fin_cases i <;> decide)
        (by fin_cases i <;> decide) (by fin_cases i <;> decide)
        (by fin_cases i <;> decide)
        (by intro j; fin_cases i <;> fin_cases j <;> decide)
        (by intro j; fin_cases i <;> fin_cases j <;> decide),
        copyWords i.val i.isLt,routeSeed i]
    · intro unequal
      exact False.elim (unequal selected)
  · have skippedPc : routed.pc = 0x13c4 := by
      rw [routePc,if_neg selected]
    obtain ⟨staged,ready,after,h2,_,readyPc,afterPc,query,answer,frame⟩ :=
      GroupedBalancedSignBottomH2FromSeed67.input_to_leaf hash routed
        leaf seed skippedPc routeLevel routeAddress routeSeed
    refine ⟨ready,after,?_,readyPc,afterPc,query,answer,?_,?_,?_⟩
    · simp only [if_neg selected]
      simpa [image,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        ((OrdinarySteps.trace (hash := hash) route).trans h2)
    · intro a h0 h1 h2 h3 hin hout hwit
      rw [frame a h0 h1 h2 h3 hin hout,
        GroupedBalancedSignBottomSelect67.select_frame s a]
    · intro equal
      exact False.elim (selected equal)
    · intro _ i
      rw [frame _ (by fin_cases i <;> decide)
        (by fin_cases i <;> decide) (by fin_cases i <;> decide)
        (by fin_cases i <;> decide)
        (by intro j; fin_cases i <;> fin_cases j <;> decide)
        (by intro j; fin_cases i <;> fin_cases j <;> decide),
        GroupedBalancedSignBottomSelect67.select_frame s _]

#print axioms first_leaf_h2
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomFirstH267
