import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Input67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4NodeQuery67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexFrame67

/-! The verifier orders the current node and its witness sibling before H4. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4Payload67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyH4IndexHeader67
open GroupedBalancedVerifyH4IndexFrame67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem header_frame (s : MachineState) (a : Word)
    (h0 : a ≠ 0x81008) (h1 : a ≠ 0x81010)
    (h2 : a ≠ 0x81018) (h3 : a ≠ 0x81020) :
    (GroupedBalancedVerifyTreeHeader67.headerState s).getMem a = s.getMem a := by
  change a ≠ 528392#64 at h0
  change a ≠ 528400#64 at h1
  change a ≠ 528408#64 at h2
  change a ≠ 528416#64 at h3
  simp [GroupedBalancedVerifyTreeHeader67.headerState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1,h2,h3]

theorem nonzero_sibling_left (s : MachineState) (p : Word)
    (pointer : s.getMem 0x81048 = p) (i : Fin 2) :
    (GroupedBalancedVerifyTreeSiblingNonzero67.siblingState s).getMem
      (Signing.wordAddress 0x80520 i.val) =
      s.getMem (p + BitVec.ofNat 64 (8*i.val)) := by
  have pointerBV : s.getMem 0x81048#64 = p := by simpa using pointer
  fin_cases i <;>
    simp [GroupedBalancedVerifyTreeSiblingNonzero67.siblingState,
      Signing.wordAddress,execInstrBr,signExtend12,pointerBV,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem nonzero_current_right (s : MachineState) (i : Fin 2) :
    (GroupedBalancedVerifyTreeSiblingNonzero67.siblingState s).getMem
      (Signing.wordAddress 0x80530 i.val) =
      s.getMem (Signing.wordAddress 0x80530 i.val) := by
  fin_cases i <;>
    simp [GroupedBalancedVerifyTreeSiblingNonzero67.siblingState,
      Signing.wordAddress,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem zero_current_left (s : MachineState) (i : Fin 2) :
    (GroupedBalancedVerifyTreeSiblingZero67.siblingState s).getMem
      (Signing.wordAddress 0x80520 i.val) =
      s.getMem (Signing.wordAddress 0x80520 i.val) := by
  fin_cases i <;>
    simp [GroupedBalancedVerifyTreeSiblingZero67.siblingState,
      Signing.wordAddress,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem zero_sibling_right (s : MachineState) (p : Word)
    (pointer : s.getMem 0x81048 = p) (i : Fin 2) :
    (GroupedBalancedVerifyTreeSiblingZero67.siblingState s).getMem
      (Signing.wordAddress 0x80530 i.val) =
      s.getMem (p + BitVec.ofNat 64 (8*i.val)) := by
  have pointerBV : s.getMem 0x81048#64 = p := by simpa using pointer
  fin_cases i <;>
    simp [GroupedBalancedVerifyTreeSiblingZero67.siblingState,
      Signing.wordAddress,execInstrBr,signExtend12,pointerBV,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

private theorem nonzero_setup_code :
    Keygen.CopySetupCode image 0x1314 0x500 0x530 2 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopySetupCode
  decide

private theorem nonzero_copy_code : Keygen.CopyCode image 0x1328 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

private theorem zero_setup_code :
    Keygen.CopySetupCode image 0x1368 0x500 0x520 2 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopySetupCode
  decide

private theorem zero_copy_code : Keygen.CopyCode image 0x137c := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

private theorem nonzero_copy_full (s : MachineState) (pc : s.pc = 0x1314) :
    ∃ mid, OrdinarySteps image s 17 mid ∧ mid.pc = 0x1340 ∧
      (∀ i : Fin 2, mid.getMem (Signing.wordAddress 0x80530 i.val) =
        s.getMem (Signing.wordAddress 0x80500 i.val)) ∧
      (∀ a, (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80530 i.val) →
        mid.getMem a = s.getMem a) ∧
      GroupedBalancedVerifyTreeHighFrame67.SafeFrame s mid := by
  obtain ⟨mid,run,endPc,words,_,sp,frame⟩ :=
    Keygen.copy_two image 0x1314 0x500 0x530 0x80500 0x80530
      nonzero_setup_code nonzero_copy_code
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) s pc
  refine ⟨mid,run,by simpa using endPc,words,frame,?_,sp⟩
  intro a ha
  exact frame a (by
    intro i eq
    have hn := congrArg BitVec.toNat eq
    simp [Signing.wordAddress] at hn
    omega)

private theorem zero_copy_full (s : MachineState) (pc : s.pc = 0x1368) :
    ∃ mid, OrdinarySteps image s 17 mid ∧ mid.pc = 0x1394 ∧
      (∀ i : Fin 2, mid.getMem (Signing.wordAddress 0x80520 i.val) =
        s.getMem (Signing.wordAddress 0x80500 i.val)) ∧
      (∀ a, (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80520 i.val) →
        mid.getMem a = s.getMem a) ∧
      GroupedBalancedVerifyTreeHighFrame67.SafeFrame s mid := by
  obtain ⟨mid,run,endPc,words,_,sp,frame⟩ :=
    Keygen.copy_two image 0x1368 0x500 0x520 0x80500 0x80520
      zero_setup_code zero_copy_code
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) s pc
  refine ⟨mid,run,by simpa using endPc,words,frame,?_,sp⟩
  intro a ha
  exact frame a (by
    intro i eq
    have hn := congrArg BitVec.toNat eq
    simp [Signing.wordAddress] at hn
    omega)

private theorem below_not_word (a : Word) (small : a.toNat < 0x80000)
    (n : Nat) (large : 0x80000 ≤ n) (bound : n < 2^64) :
    a ≠ BitVec.ofNat 64 n := by
  intro same
  have hn := congrArg BitVec.toNat same
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound] at hn
  omega

private theorem header_keep_below (s : MachineState) (a : Word)
    (small : a.toNat < 0x80000) :
    (GroupedBalancedVerifyTreeHeader67.headerState s).getMem a =
      s.getMem a := by
  apply header_frame s a
  · exact below_not_word a small 0x81008 (by decide) (by decide)
  · exact below_not_word a small 0x81010 (by decide) (by decide)
  · exact below_not_word a small 0x81018 (by decide) (by decide)
  · exact below_not_word a small 0x81020 (by decide) (by decide)

private theorem below_not_destination (a : Word)
    (small : a.toNat < 0x80000) (dst : Nat)
    (lower : 0x80000 ≤ dst) (upper : dst + 8 < 2^64) :
    ∀ i : Fin 2, a ≠ Signing.wordAddress dst i.val := by
  intro i
  fin_cases i
  · simpa [Signing.wordAddress] using
      below_not_word a small dst lower (by omega)
  · simpa [Signing.wordAddress] using
      below_not_word a small (dst+8) (by omega) upper

theorem nonzero_payload (s : MachineState) (p : Word)
    (pc : s.pc = 0x1314) (pointer : s.getMem 0x81048 = p)
    (pSmall : p.toNat < 0x80000)
    (p8Small : (p+8).toNat < 0x80000)
    (valid0 : accessValid p 8 = true)
    (valid8 : accessValid (p+8) 8 = true)
    (root sibling : Reference.Digest)
    (rootWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80500 i.val) =
        root.extractLsb' (64*i.val) 64)
    (siblingWords : ∀ i : Fin 2,
      s.getMem (p + BitVec.ofNat 64 (8*i.val)) =
        sibling.extractLsb' (64*i.val) 64) :
    ∃ final, OrdinarySteps image s 56 final ∧ final.pc = 0x13e4 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80020 i.val) =
          sibling.extractLsb' (64*i.val) 64) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80030 i.val) =
          root.extractLsb' (64*i.val) 64) ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧ IndexFrame s final ∧
      final.getMem 0x81048 = p ∧
      final.getMem 0x81050 = s.getMem 0x81050 ∧
      GroupedBalancedVerifyTreeHighFrame67.SafeFrame s final ∧
      GroupedBalancedVerifyStackGlobal67.LowFrame s final := by
  obtain ⟨copied,copyRun,copyPc,copyRoot,copyFrame,copySafe⟩ :=
    nonzero_copy_full s pc
  have copiedPointer : copied.getMem 0x81048 = p :=
    (copyFrame 0x81048 (by intro i; fin_cases i <;> decide)).trans pointer
  have copiedSibling (i : Fin 2) :
      copied.getMem (p + BitVec.ofNat 64 (8*i.val)) =
        s.getMem (p + BitVec.ofNat 64 (8*i.val)) := by
    fin_cases i
    · simpa using copyFrame p
        (below_not_destination p pSmall 0x80530 (by decide) (by decide))
    · simpa using copyFrame (p+8)
        (below_not_destination (p+8) p8Small 0x80530 (by decide) (by decide))
  let staged := GroupedBalancedVerifyTreeSiblingNonzero67.siblingState copied
  have siblingRun := GroupedBalancedVerifyTreeSiblingNonzero67.sibling_steps
    copied p copyPc copiedPointer valid0 valid8
  have stagedPc := GroupedBalancedVerifyTreeSiblingNonzero67.sibling_pc
    copied copyPc
  have stagedLeft (i : Fin 2) :
      staged.getMem (Signing.wordAddress 0x80520 i.val) =
        sibling.extractLsb' (64*i.val) 64 := by
    exact (nonzero_sibling_left copied p copiedPointer i).trans
      ((copiedSibling i).trans (siblingWords i))
  have stagedRight (i : Fin 2) :
      staged.getMem (Signing.wordAddress 0x80530 i.val) =
        root.extractLsb' (64*i.val) 64 := by
    exact (nonzero_current_right copied i).trans
      ((copyRoot i).trans (rootWords i))
  let joined := execInstrBr staged (.JAL .x0 84)
  have jumpRun := GroupedBalancedVerifyTreeSiblingNonzero67.jump_step
    staged stagedPc
  have joinedPc := GroupedBalancedVerifyTreeSiblingNonzero67.jump_pc
    staged stagedPc
  have joinedLeft (i : Fin 2) :
      joined.getMem (Signing.wordAddress 0x80520 i.val) =
        sibling.extractLsb' (64*i.val) 64 := by
    simpa [joined,execInstrBr] using stagedLeft i
  have joinedRight (i : Fin 2) :
      joined.getMem (Signing.wordAddress 0x80530 i.val) =
        root.extractLsb' (64*i.val) 64 := by
    simpa [joined,execInstrBr] using stagedRight i
  obtain ⟨final,inputRun,finalPc,inputWords,inputPointer,inputCount,inputSafe⟩ :=
    GroupedBalancedVerifyTreeH4Input67.copy_input joined joinedPc
  refine ⟨final,?_,finalPc,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have first := Keygen.ordinary_trans image s copied staged 17 9
      copyRun siblingRun
    have second := Keygen.ordinary_trans image s staged joined 26 1
      (by simpa only [Nat.reduceAdd] using first) jumpRun
    have third := Keygen.ordinary_trans image s joined final 27 29
      (by simpa only [Nat.reduceAdd] using second) inputRun
    simpa only [Nat.reduceAdd] using third
  · intro i
    fin_cases i
    · simpa [Signing.wordAddress] using
        (inputWords (0 : Fin 4)).trans (joinedLeft 0)
    · simpa [Signing.wordAddress] using
        (inputWords (1 : Fin 4)).trans (joinedLeft 1)
  · intro i
    fin_cases i
    · simpa [Signing.wordAddress] using
        (inputWords (2 : Fin 4)).trans (joinedRight 0)
    · simpa [Signing.wordAddress] using
        (inputWords (3 : Fin 4)).trans (joinedRight 1)
  · have copiedBase := GroupedBalancedVerifyTreeH4Base67.nonzero_copy_base
      s copied pc copyRun
    have stagedBase := GroupedBalancedVerifyTreeH4Base67.nonzero_sibling_base copied
    have joinedBase : joined.getMem 0x81000 = staged.getMem 0x81000 := by
      simp [joined,execInstrBr]
    exact (GroupedBalancedVerifyTreeH4Base67.input_copy_base
      joined final joinedPc inputRun).trans
      (joinedBase.trans (stagedBase.trans copiedBase))
  · have copiedIndex := nonzero_copy_index s copied pc copyRun
    have stagedIndex := nonzero_sibling_index copied
    have joinedIndex : IndexFrame staged joined := by
      intro i
      simp [joined,execInstrBr]
    exact index_trans copiedIndex
      (index_trans stagedIndex
        (index_trans joinedIndex (input_copy_index joined final joinedPc inputRun)))
  · have stagedPointer := GroupedBalancedVerifyTreeSiblingNonzero67.sibling_pointer copied
    have joinedPointer : joined.getMem 0x81048 = staged.getMem 0x81048 := by
      simp [joined,execInstrBr]
    exact inputPointer.trans (joinedPointer.trans (stagedPointer.trans copiedPointer))
  · have copiedCount : copied.getMem 0x81050 = s.getMem 0x81050 :=
      copyFrame 0x81050 (by intro i; fin_cases i <;> decide)
    have stagedCount := GroupedBalancedVerifyTreeSiblingNonzero67.sibling_count copied
    have joinedCount : joined.getMem 0x81050 = staged.getMem 0x81050 := by
      simp [joined,execInstrBr]
    exact inputCount.trans (joinedCount.trans (stagedCount.trans copiedCount))
  · have stagedSafe := GroupedBalancedVerifyTreeSiblingNonzero67.sibling_safe copied
    have joinedSafe : GroupedBalancedVerifyTreeHighFrame67.SafeFrame staged joined := by
      constructor
      · intro a _
        simp [joined,execInstrBr]
      · simp [joined,execInstrBr,MachineState.getReg_setReg_ne]
    exact GroupedBalancedVerifyTreeHighFrame67.safe_trans copySafe
      (GroupedBalancedVerifyTreeHighFrame67.safe_trans stagedSafe
        (GroupedBalancedVerifyTreeHighFrame67.safe_trans joinedSafe inputSafe))
  · have copiedLow := GroupedBalancedVerifyTreeH4Base67.nonzero_copy_low
      s copied pc copyRun
    have stagedLow := GroupedBalancedVerifyTreeH4Base67.nonzero_sibling_low copied
    have joinedLow : GroupedBalancedVerifyStackGlobal67.LowFrame staged joined := by
      intro a _
      simp [joined,execInstrBr]
    exact (copiedLow.trans stagedLow).trans
      (joinedLow.trans
        (GroupedBalancedVerifyTreeH4Base67.input_copy_low joined final joinedPc inputRun))

theorem zero_payload (s : MachineState) (p : Word)
    (pc : s.pc = 0x1368) (pointer : s.getMem 0x81048 = p)
    (pSmall : p.toNat < 0x80000)
    (p8Small : (p+8).toNat < 0x80000)
    (valid0 : accessValid p 8 = true)
    (valid8 : accessValid (p+8) 8 = true)
    (root sibling : Reference.Digest)
    (rootWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80500 i.val) =
        root.extractLsb' (64*i.val) 64)
    (siblingWords : ∀ i : Fin 2,
      s.getMem (p + BitVec.ofNat 64 (8*i.val)) =
        sibling.extractLsb' (64*i.val) 64) :
    ∃ final, OrdinarySteps image s 55 final ∧ final.pc = 0x13e4 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80020 i.val) =
          root.extractLsb' (64*i.val) 64) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80030 i.val) =
          sibling.extractLsb' (64*i.val) 64) ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧ IndexFrame s final ∧
      final.getMem 0x81048 = p ∧
      final.getMem 0x81050 = s.getMem 0x81050 ∧
      GroupedBalancedVerifyTreeHighFrame67.SafeFrame s final ∧
      GroupedBalancedVerifyStackGlobal67.LowFrame s final := by
  obtain ⟨copied,copyRun,copyPc,copyRoot,copyFrame,copySafe⟩ :=
    zero_copy_full s pc
  have copiedPointer : copied.getMem 0x81048 = p :=
    (copyFrame 0x81048 (by intro i; fin_cases i <;> decide)).trans pointer
  have copiedSibling (i : Fin 2) :
      copied.getMem (p + BitVec.ofNat 64 (8*i.val)) =
        s.getMem (p + BitVec.ofNat 64 (8*i.val)) := by
    fin_cases i
    · simpa using copyFrame p
        (below_not_destination p pSmall 0x80520 (by decide) (by decide))
    · simpa using copyFrame (p+8)
        (below_not_destination (p+8) p8Small 0x80520 (by decide) (by decide))
  let staged := GroupedBalancedVerifyTreeSiblingZero67.siblingState copied
  have siblingRun := GroupedBalancedVerifyTreeSiblingZero67.sibling_steps
    copied p copyPc copiedPointer valid0 valid8
  have stagedPc := GroupedBalancedVerifyTreeSiblingZero67.sibling_pc
    copied copyPc
  have stagedLeft (i : Fin 2) :
      staged.getMem (Signing.wordAddress 0x80520 i.val) =
        root.extractLsb' (64*i.val) 64 := by
    exact (zero_current_left copied i).trans
      ((copyRoot i).trans (rootWords i))
  have stagedRight (i : Fin 2) :
      staged.getMem (Signing.wordAddress 0x80530 i.val) =
        sibling.extractLsb' (64*i.val) 64 := by
    exact (zero_sibling_right copied p copiedPointer i).trans
      ((copiedSibling i).trans (siblingWords i))
  obtain ⟨final,inputRun,finalPc,inputWords,inputPointer,inputCount,inputSafe⟩ :=
    GroupedBalancedVerifyTreeH4Input67.copy_input staged stagedPc
  refine ⟨final,?_,finalPc,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have first := Keygen.ordinary_trans image s copied staged 17 9
      copyRun siblingRun
    have second := Keygen.ordinary_trans image s staged final 26 29
      (by simpa only [Nat.reduceAdd] using first) inputRun
    simpa only [Nat.reduceAdd] using second
  · intro i
    fin_cases i
    · simpa [Signing.wordAddress] using
        (inputWords (0 : Fin 4)).trans (stagedLeft 0)
    · simpa [Signing.wordAddress] using
        (inputWords (1 : Fin 4)).trans (stagedLeft 1)
  · intro i
    fin_cases i
    · simpa [Signing.wordAddress] using
        (inputWords (2 : Fin 4)).trans (stagedRight 0)
    · simpa [Signing.wordAddress] using
        (inputWords (3 : Fin 4)).trans (stagedRight 1)
  · have copiedBase := GroupedBalancedVerifyTreeH4Base67.zero_copy_base
      s copied pc copyRun
    have stagedBase := GroupedBalancedVerifyTreeH4Base67.zero_sibling_base copied
    exact (GroupedBalancedVerifyTreeH4Base67.input_copy_base
      staged final stagedPc inputRun).trans
      (stagedBase.trans copiedBase)
  · have copiedIndex := zero_copy_index s copied pc copyRun
    have stagedIndex := zero_sibling_index copied
    exact index_trans copiedIndex
      (index_trans stagedIndex (input_copy_index staged final stagedPc inputRun))
  · have stagedPointer := GroupedBalancedVerifyTreeSiblingZero67.sibling_pointer copied
    exact inputPointer.trans (stagedPointer.trans copiedPointer)
  · have copiedCount : copied.getMem 0x81050 = s.getMem 0x81050 :=
      copyFrame 0x81050 (by intro i; fin_cases i <;> decide)
    have stagedCount := GroupedBalancedVerifyTreeSiblingZero67.sibling_count copied
    exact inputCount.trans (stagedCount.trans copiedCount)
  · have stagedSafe := GroupedBalancedVerifyTreeSiblingZero67.sibling_safe copied
    exact GroupedBalancedVerifyTreeHighFrame67.safe_trans copySafe
      (GroupedBalancedVerifyTreeHighFrame67.safe_trans stagedSafe inputSafe)
  · have copiedLow := GroupedBalancedVerifyTreeH4Base67.zero_copy_low
      s copied pc copyRun
    have stagedLow := GroupedBalancedVerifyTreeH4Base67.zero_sibling_low copied
    exact (copiedLow.trans stagedLow).trans
      (GroupedBalancedVerifyTreeH4Base67.input_copy_low staged final stagedPc inputRun)

theorem header_payload (s : MachineState) (p : Word)
    (pc : s.pc = 0x1290) (pointer : s.getMem 0x81048 = p)
    (pSmall : p.toNat < 0x80000)
    (p8Small : (p+8).toNat < 0x80000)
    (valid0 : accessValid p 8 = true)
    (valid8 : accessValid (p+8) 8 = true)
    (root sibling : Reference.Digest)
    (rootWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80500 i.val) =
        root.extractLsb' (64*i.val) 64)
    (siblingWords : ∀ i : Fin 2,
      s.getMem (p + BitVec.ofNat 64 (8*i.val)) =
        sibling.extractLsb' (64*i.val) 64) :
    ∃ n final, (n = 88 ∨ n = 89) ∧
      OrdinarySteps image s n final ∧ final.pc = 0x13e4 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80020 i.val) =
          (if s.getMem 0x81008#64 &&& 1#64 = 0#64
            then root else sibling).extractLsb' (64*i.val) 64) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80030 i.val) =
          (if s.getMem 0x81008#64 &&& 1#64 = 0#64
            then sibling else root).extractLsb' (64*i.val) 64) ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      IndexFrame (GroupedBalancedVerifyTreeHeader67.headerState s) final ∧
      final.getMem 0x81048 = p ∧
      final.getMem 0x81050 = s.getMem 0x81050 ∧
      GroupedBalancedVerifyTreeHighFrame67.SafeFrame s final ∧
      GroupedBalancedVerifyStackGlobal67.LowFrame s final := by
  let header := GroupedBalancedVerifyTreeHeader67.headerState s
  have headerRun := GroupedBalancedVerifyTreeHeader67.header_steps s pc
  have headerPc := GroupedBalancedVerifyTreeHeader67.header_pc s pc
  have selector := (GroupedBalancedVerifyTreeHeader67.header_selector s).1
  let branched := execInstrBr header (.BEQ .x6 .x0 88)
  have branchRun := GroupedBalancedVerifyTreeHeader67.branch_step
    header headerPc
  have branchPc := GroupedBalancedVerifyTreeHeader67.branch_pc
    header headerPc (GroupedBalancedVerifyTreeHeader67.header_bit s)
  have branchPointer : branched.getMem 0x81048 = p := by
    simpa [branched,execInstrBr,header] using
      (GroupedBalancedVerifyTreeHeader67.header_pointer s).trans pointer
  have branchBase : branched.getMem 0x81000 = s.getMem 0x81000 := by
    have h : branched.getMem 0x81000 = header.getMem 0x81000 := by
      simp [branched,execInstrBr]
    exact h.trans (GroupedBalancedVerifyTreeH4Base67.header_base s)
  have branchIndex : IndexFrame header branched := branch_index header
  have branchCount : branched.getMem 0x81050 = s.getMem 0x81050 := by
    have h := GroupedBalancedVerifyTreeHeader67.branch_count header
    exact h.trans (GroupedBalancedVerifyTreeHeader67.header_count s)
  have branchSafe : GroupedBalancedVerifyTreeHighFrame67.SafeFrame s branched :=
    GroupedBalancedVerifyTreeHighFrame67.safe_trans
      (GroupedBalancedVerifyTreeHeader67.header_safe s)
      (GroupedBalancedVerifyTreeHeader67.branch_safe header)
  have branchLow : GroupedBalancedVerifyStackGlobal67.LowFrame s branched :=
    (GroupedBalancedVerifyTreeH4Base67.header_low s).trans
      (GroupedBalancedVerifyTreeH4Base67.branch_low header)
  have branchRoot (i : Fin 2) :
      branched.getMem (Signing.wordAddress 0x80500 i.val) =
        root.extractLsb' (64*i.val) 64 := by
    have frame := header_frame s (Signing.wordAddress 0x80500 i.val)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    simpa [branched,execInstrBr,header] using frame.trans (rootWords i)
  have branchSibling (i : Fin 2) :
      branched.getMem (p + BitVec.ofNat 64 (8*i.val)) =
        sibling.extractLsb' (64*i.val) 64 := by
    have small : (p + BitVec.ofNat 64 (8*i.val)).toNat < 0x80000 := by
      fin_cases i
      · simpa using pSmall
      · simpa using p8Small
    have frame := header_keep_below s
      (p + BitVec.ofNat 64 (8*i.val)) small
    simpa [branched,execInstrBr,header] using frame.trans (siblingWords i)
  by_cases bitZero : header.getReg .x6 = 0
  · have branchAt : branched.pc = 0x1368 := by
      have p := branchPc
      simpa [branched,bitZero] using p
    obtain ⟨final,pathRun,finalPc,left,right,finalBase,finalIndex,
      finalPointer,finalCount,finalSafe,finalLow⟩ :=
      zero_payload branched p branchAt branchPointer pSmall p8Small
        valid0 valid8 root sibling branchRoot branchSibling
    refine ⟨88,final,Or.inl rfl,?_,finalPc,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · have first := Keygen.ordinary_trans image s header branched 32 1
        headerRun branchRun
      have second := Keygen.ordinary_trans image s branched final 33 55
        (by simpa only [Nat.reduceAdd] using first) pathRun
      simpa only [Nat.reduceAdd] using second
    · intro i
      have selected : s.getMem 0x81008#64 &&& 1#64 = 0#64 := by
        rw [← selector]
        exact bitZero
      simpa [selected] using left i
    · intro i
      have selected : s.getMem 0x81008#64 &&& 1#64 = 0#64 := by
        rw [← selector]
        exact bitZero
      simpa [selected] using right i
    · exact finalBase.trans branchBase
    · exact index_trans branchIndex finalIndex
    · exact finalPointer
    · exact finalCount.trans branchCount
    · exact GroupedBalancedVerifyTreeHighFrame67.safe_trans branchSafe finalSafe
    · exact branchLow.trans finalLow
  · have branchAt : branched.pc = 0x1314 := by
      have p := branchPc
      have notZero : ¬ header.getReg .x6 = 0#64 := by simpa using bitZero
      simpa [branched,notZero] using p
    obtain ⟨final,pathRun,finalPc,left,right,finalBase,finalIndex,
      finalPointer,finalCount,finalSafe,finalLow⟩ :=
      nonzero_payload branched p branchAt branchPointer pSmall p8Small
        valid0 valid8 root sibling branchRoot branchSibling
    refine ⟨89,final,Or.inr rfl,?_,finalPc,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · have first := Keygen.ordinary_trans image s header branched 32 1
        headerRun branchRun
      have second := Keygen.ordinary_trans image s branched final 33 56
        (by simpa only [Nat.reduceAdd] using first) pathRun
      simpa only [Nat.reduceAdd] using second
    · intro i
      have selected : ¬ s.getMem 0x81008#64 &&& 1#64 = 0#64 := by
        rw [← selector]
        exact bitZero
      simpa [selected] using left i
    · intro i
      have selected : ¬ s.getMem 0x81008#64 &&& 1#64 = 0#64 := by
        rw [← selector]
        exact bitZero
      simpa [selected] using right i
    · exact finalBase.trans branchBase
    · exact index_trans branchIndex finalIndex
    · exact finalPointer
    · exact finalCount.trans branchCount
    · exact GroupedBalancedVerifyTreeHighFrame67.safe_trans branchSafe finalSafe
    · exact branchLow.trans finalLow

#print axioms header_frame
#print axioms nonzero_sibling_left
#print axioms zero_sibling_right
#print axioms nonzero_payload
#print axioms zero_payload
#print axioms header_payload

end SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4Payload67
