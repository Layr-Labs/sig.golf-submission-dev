import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafAdvanceData67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomH1Loop67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafTick67. -/
section
/-! One arbitrary bottom-tree H1 seed derivation from the leaf-loop entry. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomH1Loop67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image

theorem loop_seed (hash : Hash) (s : MachineState)
    (secretKey : SecretKey) (leaf : Nat)
    (pc : s.pc = 0x12cc)
    (level : s.getMem 0x81000 = 0)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (keyWords : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    ∃ staged ready after : MachineState,
      Trace hash image s 62 69 1 1 after ∧
      staged.pc = 0x12f4 ∧ ready.pc = 0x1378 ∧ after.pc = 0x137c ∧
      hashInput ready = Reference.packed (KeygenDomain.secretPayload
        (KeygenDomain.header 1 0 0 0 0) leaf secretKey) ∧
      after = writeHash ready (hash (hashInput ready)) ∧
      (∀ i : Fin 2, after.getMem (Signing.wordAddress 0x80300 i.val) =
        (GroupedBottomTree.secret hash secretKey leaf).extractLsb'
          (64*i.val) 64) ∧
      after.getMem 0x81000 = 0 ∧
      (∀ i : Fin 3, after.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64) ∧
      (∀ a : Word,
        a ≠ 0x80000 → a ≠ 0x80008 →
        a ≠ 0x80010 → a ≠ 0x80018 →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80020 i.val) →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) →
        after.getMem a = s.getMem a) := by
  obtain ⟨staged,keyTrace,stagedPc,stagedKey,stagedFrame⟩ :=
    GroupedBalancedSignBottomKeyCopy67.key_copy s pc
  have stagedLevel : staged.getMem 0x81000 = 0 := by
    rw [stagedFrame _ (by intro i hi; interval_cases i <;> decide)]
    exact level
  have stagedAddress : ∀ i : Fin 3,
      staged.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64 := by
    intro i
    rw [stagedFrame _ (by intro j hj; fin_cases i <;> interval_cases j <;> decide)]
    exact address i
  have stagedSecret : ∀ i : Fin 4,
      staged.getMem (Signing.wordAddress 0x80020 i.val) =
        secretKey.extractLsb' (64*i.val) 64 := by
    intro i
    rw [stagedKey i.val i.isLt]
    exact keyWords i
  let ready := GroupedBalancedSignBottomH1Prelude67.preludeState staged
  let after := writeHash ready (hash (hashInput ready))
  have query := GroupedBalancedSignBottomH1Query67.secret_query staged leaf
    secretKey stagedLevel stagedAddress stagedSecret
  have answer := GroupedBalancedSignBottomH1Query67.secret_answer hash staged leaf
    secretKey stagedLevel stagedAddress stagedSecret
  have h1 := GroupedBalancedSignBottomH1Query67.secret_call hash staged stagedPc
  have readyPc := GroupedBalancedSignBottomH1Prelude67.prelude_pc staged stagedPc
  have afterPc : after.pc = 0x137c := by
    change ready.pc + 4 = 0x137c
    rw [readyPc]
    decide
  have controlFrame (a : Word)
      (h0 : a ≠ 0x80000) (h1 : a ≠ 0x80008)
      (h2 : a ≠ 0x80010) (h3 : a ≠ 0x80018)
      (hout : ∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) :
      after.getMem a = staged.getMem a := by
    rw [show after = writeHash ready (hash (hashInput ready)) from rfl,
      Signing.hash_answer_frame ready _
        (GroupedBalancedSignBottomH1Prelude67.prelude_hash_args staged).2.2.1
        a hout]
    exact GroupedBalancedSignBottomH1Prelude67.prelude_frame staged a
      h0 h1 h2 h3
  refine ⟨staged,ready,after,?_,stagedPc,readyPc,afterPc,query,rfl,
    answer,?_,?_,?_⟩
  · simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (OrdinarySteps.trace (hash := hash) keyTrace).trans h1
  · rw [controlFrame _ (by decide) (by decide) (by decide)
      (by decide) (by intro i; fin_cases i <;> decide)]
    exact stagedLevel
  · intro i
    rw [controlFrame _
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by intro j; fin_cases i <;> fin_cases j <;> decide)]
    exact stagedAddress i
  · intro a h0 h1 h2 h3 hkey hout
    rw [controlFrame a h0 h1 h2 h3 hout]
    exact stagedFrame a (by intro i hi; exact hkey ⟨i,hi⟩)

#print axioms loop_seed
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomH1Loop67

end

/-! One complete bottom leaf, from loop entry to the next branch. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafTick67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image

theorem leaf_tick (hash : Hash) (s : MachineState)
    (secretKey : SecretKey) (leaf : Nat)
    (pc : s.pc = 0x12cc)
    (counter : (s.getMem 0x810e0).toNat < 1024)
    (level : s.getMem 0x81000 = 0)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (keyWords : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    ∃ seedReady seeded leafReady leafAfter next : MachineState,
      Trace hash image s
        (if s.getMem 0x810e0 = s.getMem 0x810e8 then 166 else 149)
        (if s.getMem 0x810e0 = s.getMem 0x810e8 then 180 else 163)
        2 2 next ∧
      seedReady.pc = 0x1378 ∧ leafReady.pc = 0x1474 ∧
      leafAfter.pc = 0x1478 ∧
      hashInput seedReady = Reference.packed (KeygenDomain.secretPayload
        (KeygenDomain.header 1 0 0 0 0) leaf secretKey) ∧
      hashInput leafReady = Reference.packed (KeygenDomain.payload
        (KeygenDomain.header 2 0 0 0 0) leaf
        (GroupedBottomTree.secret hash secretKey leaf)) ∧
      (∀ i : Fin 2, leafAfter.getMem (Signing.wordAddress 0x80300 i.val) =
        (GroupedBottomTree.leafRoot hash secretKey leaf).extractLsb'
          (64*i.val) 64) ∧
      next.getMem 0x810e0 = s.getMem 0x810e0 + 1 ∧
      next.getMem 0x81008 = s.getMem 0x81008 + 1 ∧
      next.pc =
        (if s.getMem 0x810e0 + 1 = (1024 : Word) then 0x14ec else 0x12cc) ∧
      next = GroupedBalancedSignBottomLeafAdvance67.advanceState leafAfter ∧
      (∀ a : Word,
        a ≠ 0x80000 → a ≠ 0x80008 →
        a ≠ 0x80010 → a ≠ 0x80018 →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80020 i.val) →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) →
        seeded.getMem a = s.getMem a) ∧
      (∀ a : Word,
        a ≠ 0x80000 → a ≠ 0x80008 →
        a ≠ 0x80010 → a ≠ 0x80018 →
        (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80020 i.val) →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) →
        (∀ i : Fin 2, a ≠ Signing.wordAddress 0x20080 i.val) →
        leafAfter.getMem a = seeded.getMem a) ∧
      (s.getMem 0x810e0 = s.getMem 0x810e8 →
        ∀ i : Fin 2,
          next.getMem (Signing.wordAddress 0x20080 i.val) =
            (GroupedBottomTree.secret hash secretKey leaf).extractLsb'
              (64*i.val) 64) ∧
      (s.getMem 0x810e0 ≠ s.getMem 0x810e8 →
        ∀ i : Fin 2,
          next.getMem (Signing.wordAddress 0x20080 i.val) =
            s.getMem (Signing.wordAddress 0x20080 i.val)) := by
  obtain ⟨staged,seedReady,seeded,h1,_,seedPc,seededPc,seedQuery,_,
    seedWords,seedLevel,seedAddress,seedFrame⟩ :=
    GroupedBalancedSignBottomH1Loop67.loop_seed hash s secretKey leaf
      pc level address keyWords
  have seedCounter : seeded.getMem 0x810e0 = s.getMem 0x810e0 :=
    seedFrame 0x810e0 (by decide) (by decide) (by decide) (by decide)
      (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
  have seedSelected : seeded.getMem 0x810e8 = s.getMem 0x810e8 :=
    seedFrame 0x810e8 (by decide) (by decide) (by decide) (by decide)
      (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
  obtain ⟨leafReady,leafAfter,h2,leafPc,leafAfterPc,leafQuery,leafWords,
    leafFrame,selectedWords,skippedWords⟩ :=
    GroupedBalancedSignBottomFirstH267.first_leaf_h2 hash seeded leaf
      (GroupedBottomTree.secret hash secretKey leaf)
      seededPc seedLevel seedAddress seedWords
  have leafCounter : leafAfter.getMem 0x810e0 = s.getMem 0x810e0 := by
    rw [leafFrame 0x810e0 (by decide) (by decide) (by decide)
      (by decide) (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)]
    exact seedCounter
  have leafSelected : leafAfter.getMem 0x810e8 = s.getMem 0x810e8 := by
    rw [leafFrame 0x810e8 (by decide) (by decide) (by decide)
      (by decide) (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)]
    exact seedSelected
  have leafBound : (leafAfter.getMem 0x810e0).toNat < 1024 := by
    rw [leafCounter]
    exact counter
  obtain ⟨advance,advanceCounter,advanceAddress,advancePc⟩ :=
    GroupedBalancedSignBottomLeafAdvanceData67.advance_trace hash leafAfter
      leafAfterPc leafBound
  refine ⟨seedReady,seeded,leafReady,leafAfter,
    GroupedBalancedSignBottomLeafAdvance67.advanceState leafAfter,
    ?_,seedPc,leafPc,leafAfterPc,seedQuery,leafQuery,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · by_cases selected : s.getMem 0x810e0 = s.getMem 0x810e8
    · have selectedSeeded : seeded.getMem 0x810e0 = seeded.getMem 0x810e8 := by
        rw [seedCounter,seedSelected]
        exact selected
      simp only [if_pos selectedSeeded] at h2
      simp only [if_pos selected]
      simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (h1.trans h2).trans advance
    · have skipped : seeded.getMem 0x810e0 ≠ seeded.getMem 0x810e8 := by
        rw [seedCounter,seedSelected]
        exact selected
      simp only [if_neg skipped] at h2
      simp only [if_neg selected]
      simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (h1.trans h2).trans advance
  · intro i
    simpa only [GroupedBottomTree.leafRoot] using leafWords i
  · rw [advanceCounter,leafCounter]
  · rw [advanceAddress]
    have addr : leafAfter.getMem 0x81008 = s.getMem 0x81008 := by
      rw [leafFrame 0x81008 (by decide) (by decide) (by decide)
        (by decide) (by intro i; fin_cases i <;> decide)
        (by intro i; fin_cases i <;> decide)
        (by intro i; fin_cases i <;> decide)]
      rw [seedFrame 0x81008 (by decide) (by decide) (by decide)
        (by decide) (by intro i; fin_cases i <;> decide)
        (by intro i; fin_cases i <;> decide)]
    rw [addr]
  · rw [advancePc,leafCounter]
  · rfl
  · exact seedFrame
  · exact leafFrame
  · intro selected i
    have aLow : (Signing.wordAddress 0x20080 i.val).toNat < 0x83000 := by
      fin_cases i <;> decide
    have ⟨h0,h8⟩ := GroupedBalancedSignBottomStackBound67.below_stack
      (leafAfter.getMem 0x810e0) (Signing.wordAddress 0x20080 i.val)
        leafBound aLow
    rw [GroupedBalancedSignBottomLeafAdvanceData67.advance_frame
      leafAfter leafBound _ h0 h8
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    apply selectedWords
    rw [seedCounter,seedSelected]
    exact selected
  · intro skipped i
    have aLow : (Signing.wordAddress 0x20080 i.val).toNat < 0x83000 := by
      fin_cases i <;> decide
    have ⟨h0,h8⟩ := GroupedBalancedSignBottomStackBound67.below_stack
      (leafAfter.getMem 0x810e0) (Signing.wordAddress 0x20080 i.val)
        leafBound aLow
    rw [GroupedBalancedSignBottomLeafAdvanceData67.advance_frame
      leafAfter leafBound _ h0 h8
      (by fin_cases i <;> decide) (by fin_cases i <;> decide),
      skippedWords (by rw [seedCounter,seedSelected]; exact skipped) i]
    exact seedFrame _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)
      (by intro j; fin_cases i <;> fin_cases j <;> decide)
      (by intro j; fin_cases i <;> fin_cases j <;> decide)

#print axioms leaf_tick
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafTick67
