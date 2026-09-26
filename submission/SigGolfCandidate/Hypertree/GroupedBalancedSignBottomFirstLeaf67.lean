import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomBuilderInit67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomKeyCopy67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomFirstLeaf67. -/
section
/-! Copy the secret key into the first bottom source query. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomKeyCopy67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image

def setupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 32)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 32)
  execInstrBr s (.ADDI .x10 .x0 4)

private theorem setup_code :
    Keygen.instructionAt image 0x12cc = some (.base (.ADDI .x6 .x0 32)) ∧
    Keygen.instructionAt image 0x12d0 = some (.base (.LUI .x7 0x80)) ∧
    Keygen.instructionAt image 0x12d4 = some (.base (.ADDI .x7 .x7 32)) ∧
    Keygen.instructionAt image 0x12d8 = some (.base (.ADDI .x10 .x0 4)) := by
  decide

theorem setup_steps (s : MachineState) (pc : s.pc = 0x12cc) :
    OrdinarySteps image s 4 (setupState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 32)
  let s2 := execInstrBr s1 (.LUI .x7 0x80)
  let s3 := execInstrBr s2 (.ADDI .x7 .x7 32)
  obtain ⟨c0,c1,c2,c3⟩ := setup_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 32)) 3
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s1.pc = 0x12d0 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x7 .x7 32)) 1
  · have hp : s2.pc = 0x12d4 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 (setupState s) _ (.base (.ADDI .x10 .x0 4)) 0
  · have hp : s3.pc = 0x12d8 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  exact OrdinarySteps.refl _
theorem copy_code : Keygen.CopyCode image 0x12dc := by decide
theorem copy_inv (s : MachineState) (pc : s.pc = 0x12cc) :
    Keygen.CopyInvariant 0x12dc 0x20 0x80020 4 4 (setupState s) := by
  unfold Keygen.CopyInvariant setupState
  simp [execInstrBr,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,signExtend12,pc]
theorem key_copy (s : MachineState) (pc : s.pc = 0x12cc) :
    ∃ final, OrdinarySteps image s 28 final ∧ final.pc = 0x12f4 ∧
      (∀ i, i < 4 → final.getMem (Signing.wordAddress 0x80020 i) =
        s.getMem (Signing.wordAddress 0x20 i)) ∧
      (∀ a, (∀ i, i < 4 → a ≠ Signing.wordAddress 0x80020 i) →
        final.getMem a = s.getMem a) := by
  let begun := setupState s
  obtain ⟨final,loop,done,words,frame⟩ := Signing.copy_all image
    0x12dc copy_code 0x20 0x80020 4 begun (copy_inv s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final,?_,done.2.2.1,?_,?_⟩
  · have full := Keygen.ordinary_trans image s begun final 4 24
      (setup_steps s pc) loop
    simpa only [show 24 + 4 = 28 by decide] using full
  · intro i hi
    rw [words i hi]
    simp [begun,setupState,execInstrBr]
  · intro a outside
    rw [frame a outside]
    simp [begun,setupState,execInstrBr]

#print axioms key_copy
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomKeyCopy67

end

/-! From the stored H5 index through the first tree-addressed private seed. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomFirstLeaf67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image

theorem first_leaf (hash : Hash) (s : MachineState)
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
    ∃ staged ready after : MachineState,
      Trace hash image s 134 141 1 1 after ∧
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
      (∀ a : Word, 0x20060 ≤ a.toNat → a.toNat < 0x20080 →
        after.getMem a = s.getMem a) := by
  let entry := GroupedBalancedSignBottomEntry67.entryState s
  have entryTrace := GroupedBalancedSignBottomEntry67.entry_steps s pc
  have entryPc := GroupedBalancedSignBottomEntry67.entry_pc s pc
  obtain ⟨upper,upperTrace,upperPc,upperWords,upperFrame⟩ :=
    GroupedBalancedSignBottomCopies67.upper_copy entry entryPc
  obtain ⟨base,baseTrace,basePc,baseWords,baseFrame⟩ :=
    GroupedBalancedSignBottomCopies67.base_copy upper upperPc
  let initialized := GroupedBalancedSignBottomBuilderInit67.initState base
  have initTrace := GroupedBalancedSignBottomBuilderInit67.init_steps base basePc
  have initPc := GroupedBalancedSignBottomBuilderInit67.init_pc base basePc
  obtain ⟨staged,keyTrace,stagedPc,stagedKey,stagedFrame⟩ :=
    GroupedBalancedSignBottomKeyCopy67.key_copy initialized initPc
  have stagedLevel : staged.getMem 0x81000 = 0 := by
    rw [stagedFrame _ (by intro i hi; interval_cases i <;> decide)]
    exact GroupedBalancedSignBottomBuilderInit67.init_level base
  have stagedAddress : ∀ i : Fin 3,
      staged.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64 := by
    intro i
    have keepKey := stagedFrame (Signing.wordAddress 0x81008 i.val)
      (by intro j hj; fin_cases i <;> interval_cases j <;> decide)
    rw [keepKey,GroupedBalancedSignBottomBuilderInit67.init_frame base _
      (by fin_cases i <;> decide),baseWords i.val i.isLt]
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
  have stagedSecret : ∀ i : Fin 4,
      staged.getMem (Signing.wordAddress 0x80020 i.val) =
        secretKey.extractLsb' (64*i.val) 64 := by
    intro i
    rw [stagedKey i.val i.isLt,
      GroupedBalancedSignBottomBuilderInit67.init_frame base _
        (by fin_cases i <;> decide),
      baseFrame _ (by intro j hj; interval_cases j <;> fin_cases i <;> decide),
      upperFrame _ (by intro j hj; interval_cases j <;> fin_cases i <;> decide),
      GroupedBalancedSignBottomEntry67.entry_frame s _
        (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
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
  have setup : Trace hash image s 100 100 0 0 staged := by
    have e := OrdinarySteps.trace (hash := hash) entryTrace
    have u := OrdinarySteps.trace (hash := hash) upperTrace
    have b := OrdinarySteps.trace (hash := hash) baseTrace
    have n := OrdinarySteps.trace (hash := hash) initTrace
    have k := OrdinarySteps.trace (hash := hash) keyTrace
    simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ((((e.trans u).trans b).trans n).trans k)
  refine ⟨staged,ready,after,?_,stagedPc,readyPc,afterPc,query,rfl,
    answer,?_,?_,?_⟩
  · simpa only [show 34 + 100 = 134 by decide,
      show 41 + 100 = 141 by decide] using setup.trans h1
  · rw [controlFrame _ (by decide) (by decide) (by decide)
      (by decide) (by intro i; fin_cases i <;> decide)]
    exact stagedLevel
  · intro i
    rw [controlFrame _
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by intro j; fin_cases i <;> fin_cases j <;> decide)]
    exact stagedAddress i
  · intro a low high
    have ne (b : Nat) (hb : 0x20080 ≤ b) (hbound : b < 2^64) :
        a ≠ BitVec.ofNat 64 b := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound] at hn
      omega
    have outside (base count : Nat) (hb : 0x20080 ≤ base)
        (bound : base + 8*count ≤ MEMORY_BYTES) (i : Nat) (hi : i < count) :
        a ≠ Signing.wordAddress base i := by
      have h := Signing.outside_copy_word a.toNat base count i
        a.isLt bound hi (Or.inl (by omega))
      simpa using h
    rw [controlFrame a
      (ne 0x80000 (by decide) (by decide))
      (ne 0x80008 (by decide) (by decide))
      (ne 0x80010 (by decide) (by decide))
      (ne 0x80018 (by decide) (by decide))
      (by intro i; exact outside 0x80300 4 (by decide) (by decide) i.val i.isLt),
      stagedFrame a
        (by intro i hi; exact outside 0x80020 4 (by decide) (by decide) i hi),
      GroupedBalancedSignBottomBuilderInit67.init_frame base a
        ⟨ne 0x81000 (by decide) (by decide),
         ne 0x81060 (by decide) (by decide),
         ne 0x810d0 (by decide) (by decide),
         ne 0x810e0 (by decide) (by decide),
         ne 0x810f8 (by decide) (by decide)⟩,
      baseFrame a
        (by intro i hi; exact outside 0x81008 3 (by decide) (by decide) i hi),
      upperFrame a
        (by intro i hi; exact outside 0x810b0 2 (by decide) (by decide) i hi),
      GroupedBalancedSignBottomEntry67.entry_frame s a
        (ne 0x810e8 (by decide) (by decide))
        (ne 0x810a8 (by decide) (by decide))]

#print axioms first_leaf
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomFirstLeaf67
