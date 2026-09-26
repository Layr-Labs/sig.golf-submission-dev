import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafInvariant67

/-! The index extraction and bottom-tree setup establish the leaf-loop invariant. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoopStart67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomLeafInvariant67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image

theorem setup_initial (hash : Hash) (s : MachineState)
    (secretKey : SecretKey) (leaf : Nat)
    (pc : s.pc = 0x11f4)
    (low : (s.getMem 0x81090 &&& 18446744073709550592#64) =
      (BitVec.ofNat 192 leaf).extractLsb' 0 64)
    (middle : s.getMem 0x81098 =
      (BitVec.ofNat 192 leaf).extractLsb' 64 64)
    (high : s.getMem 0x810a0 =
      (BitVec.ofNat 192 leaf).extractLsb' 128 64)
    (keyWords : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    ∃ start : MachineState,
      Trace hash image s 72 72 0 0 start ∧
      Inv hash secretKey leaf (start.getMem 0x810e8) 0 start ∧
      start.getMem 0x81060 = 10 ∧
      start.getMem 0x810d0 = 1024 ∧
      start.getMem 0x810f8 = 0x20090 ∧
      (∀ i : Fin 3,
        start.getMem (Signing.wordAddress 0x810a8 i.val) =
          (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64) ∧
      start.getMem 0x810e8 = (s.getMem 0x81090 &&& 1023#64) ∧
      (∀ i : Fin 3,
        start.getMem (Signing.wordAddress 0x81090 i.val) =
          s.getMem (Signing.wordAddress 0x81090 i.val)) ∧
      (∀ a : Word, 0xfff700 ≤ a.toNat → start.getMem a = s.getMem a) ∧
      (∀ a : Word, 0x20060 ≤ a.toNat → a.toNat < 0x20080 →
        start.getMem a = s.getMem a) := by
  let entry := GroupedBalancedSignBottomEntry67.entryState s
  have entryTrace := GroupedBalancedSignBottomEntry67.entry_steps s pc
  have entryPc := GroupedBalancedSignBottomEntry67.entry_pc s pc
  obtain ⟨upper,upperTrace,upperPc,upperWords,upperFrame⟩ :=
    GroupedBalancedSignBottomCopies67.upper_copy entry entryPc
  obtain ⟨lower,lowerTrace,lowerPc,lowerWords,lowerFrame⟩ :=
    GroupedBalancedSignBottomCopies67.base_copy upper upperPc
  let start := GroupedBalancedSignBottomBuilderInit67.initState lower
  have initTrace := GroupedBalancedSignBottomBuilderInit67.init_steps lower lowerPc
  have startPc := GroupedBalancedSignBottomBuilderInit67.init_pc lower lowerPc
  have startAddress : ∀ i : Fin 3,
      start.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64 := by
    intro i
    rw [GroupedBalancedSignBottomBuilderInit67.init_frame lower _
      (by fin_cases i <;> decide),lowerWords i.val i.isLt]
    fin_cases i
    · rw [upperFrame _ (by intro j hj; interval_cases j <;> decide)]
      simpa [entry,Signing.wordAddress] using
        (GroupedBalancedSignBottomEntry67.entry_rounded s).trans low
    · change upper.getMem 0x810b0 = _
      rw [show upper.getMem 0x810b0 = entry.getMem 0x81098 from by
        simpa [Signing.wordAddress] using upperWords 0 (by decide)]
      rw [GroupedBalancedSignBottomEntry67.entry_frame s _ (by decide) (by decide)]
      simpa [entry] using middle
    · change upper.getMem 0x810b8 = _
      rw [show upper.getMem 0x810b8 = entry.getMem 0x810a0 from by
        simpa [Signing.wordAddress] using upperWords 1 (by decide)]
      rw [GroupedBalancedSignBottomEntry67.entry_frame s _ (by decide) (by decide)]
      simpa [entry] using high
  have startKey : ∀ i : Fin 4,
      start.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64 := by
    intro i
    rw [GroupedBalancedSignBottomBuilderInit67.init_frame lower _
        (by fin_cases i <;> decide),
      lowerFrame _ (by intro j hj; interval_cases j <;> fin_cases i <;> decide),
      upperFrame _ (by intro j hj; interval_cases j <;> fin_cases i <;> decide),
      GroupedBalancedSignBottomEntry67.entry_frame s _
        (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact keyWords i
  have run : Trace hash image s 72 72 0 0 start := by
    simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (((OrdinarySteps.trace (hash := hash) entryTrace).trans
        (OrdinarySteps.trace (hash := hash) upperTrace)).trans
        (OrdinarySteps.trace (hash := hash) lowerTrace)).trans
        (OrdinarySteps.trace (hash := hash) initTrace)
  refine ⟨start,run,?_,GroupedBalancedSignBottomBuilderInit67.init_height lower,
    GroupedBalancedSignBottomBuilderInit67.init_leaves lower,
    GroupedBalancedSignBottomBuilderInit67.init_pointer lower,?_,?_,?_,?_,?_⟩
  · refine ⟨?_,?_,rfl,?_,?_,startKey,?_⟩
    · simpa only [show (0 : Nat) < 1024 from by decide,if_true] using startPc
    · simpa using GroupedBalancedSignBottomBuilderInit67.init_counter lower
    · exact GroupedBalancedSignBottomBuilderInit67.init_level lower
    · intro _ w
      simpa only [Nat.add_zero] using startAddress w
    · intro j hj
      omega
  · intro i
    rw [GroupedBalancedSignBottomBuilderInit67.init_frame lower _
        (by fin_cases i <;> decide),
      lowerFrame _ (by intro j hj; interval_cases j <;> fin_cases i <;> decide)]
    fin_cases i
    · rw [upperFrame _ (by intro j hj; interval_cases j <;> decide)]
      simpa [entry,Signing.wordAddress] using
        (GroupedBalancedSignBottomEntry67.entry_rounded s).trans low
    · change upper.getMem 0x810b0 = _
      rw [show upper.getMem 0x810b0 = entry.getMem 0x81098 from by
        simpa [Signing.wordAddress] using upperWords 0 (by decide)]
      rw [GroupedBalancedSignBottomEntry67.entry_frame s _
        (by decide) (by decide)]
      simpa [entry] using middle
    · change upper.getMem 0x810b8 = _
      rw [show upper.getMem 0x810b8 = entry.getMem 0x810a0 from by
        simpa [Signing.wordAddress] using upperWords 1 (by decide)]
      rw [GroupedBalancedSignBottomEntry67.entry_frame s _
        (by decide) (by decide)]
      simpa [entry] using high
  · rw [GroupedBalancedSignBottomBuilderInit67.init_frame lower _
      (by decide),lowerFrame _ (by intro j hj; interval_cases j <;> decide),
      upperFrame _ (by intro j hj; interval_cases j <;> decide)]
    exact GroupedBalancedSignBottomEntry67.entry_selected s
  · intro i
    rw [GroupedBalancedSignBottomBuilderInit67.init_frame lower _
        (by fin_cases i <;> decide),
      lowerFrame _ (by intro j hj; interval_cases j <;> fin_cases i <;> decide),
      upperFrame _ (by intro j hj; interval_cases j <;> fin_cases i <;> decide),
      GroupedBalancedSignBottomEntry67.entry_frame s _
        (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
  · intro a high
    have ne (w : Word) (hw : w.toNat < 0xfff700) : a ≠ w := by
      intro eq
      have h := congrArg BitVec.toNat eq
      omega
    have outside (base count : Nat) (bound : base + 8*count ≤ MEMORY_BYTES)
        (upper : base + 8*count ≤ 0xfff700) (i : Nat) (hi : i < count) :
        a ≠ Signing.wordAddress base i := by
      have h := Signing.outside_copy_word a.toNat base count i
        a.isLt bound hi (Or.inr (by omega))
      simpa using h
    have outsideLower : ∀ i, i < 3 →
        a ≠ Signing.wordAddress 0x81008 i := by
      intro i hi
      exact outside 0x81008 3 (by decide) (by decide) i hi
    have outsideUpper : ∀ i, i < 2 →
        a ≠ Signing.wordAddress 0x810b0 i := by
      intro i hi
      exact outside 0x810b0 2 (by decide) (by decide) i hi
    rw [GroupedBalancedSignBottomBuilderInit67.init_frame lower a
      ⟨ne _ (by decide), ne _ (by decide), ne _ (by decide),
       ne _ (by decide), ne _ (by decide)⟩,
      lowerFrame a outsideLower,
      upperFrame a outsideUpper,
      GroupedBalancedSignBottomEntry67.entry_frame s a
        (ne _ (by decide)) (ne _ (by decide))]
  · intro a low high
    have ne (b : Word) (hb : 0x20080 ≤ b.toNat) : a ≠ b := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      omega
    have outside (base count : Nat) (hb : 0x20080 ≤ base)
        (bound : base + 8*count ≤ MEMORY_BYTES) (i : Nat) (hi : i < count) :
        a ≠ Signing.wordAddress base i := by
      have h := Signing.outside_copy_word a.toNat base count i
        a.isLt bound hi (Or.inl (by omega))
      simpa using h
    rw [GroupedBalancedSignBottomBuilderInit67.init_frame lower a
      ⟨ne _ (by decide), ne _ (by decide), ne _ (by decide),
       ne _ (by decide), ne _ (by decide)⟩,
      lowerFrame a
        (by intro i hi; exact outside 0x81008 3 (by decide) (by decide) i hi),
      upperFrame a
        (by intro i hi; exact outside 0x810b0 2 (by decide) (by decide) i hi),
      GroupedBalancedSignBottomEntry67.entry_frame s a
        (ne _ (by decide)) (ne _ (by decide))]

#print axioms setup_initial
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoopStart67
