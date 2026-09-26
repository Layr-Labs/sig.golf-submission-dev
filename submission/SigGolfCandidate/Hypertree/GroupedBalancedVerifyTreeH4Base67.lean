import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Fold67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreePrefixSafe67

/-! The verifier tree loop advances the WOTS height word once per round. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Base67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyTreeHighFrame67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev Low := GroupedBalancedVerifyStackGlobal67.LowFrame
private theorem low_ne (a : Word) (low : a.toNat < 0x80000)
    (b : Nat) (bound : 0x80000 ≤ b) (small : b < 2^64) :
    a ≠ BitVec.ofNat 64 b :=
  GroupedBalancedVerifyStackGlobal67.low_ne a low b bound small

theorem header_low (s : MachineState) :
    Low s (GroupedBalancedVerifyTreeHeader67.headerState s) := by
  intro a low
  simp [GroupedBalancedVerifyTreeHeader67.headerState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  split_ifs with e1 e2 e3 e4
  all_goals
    try { have hn := congrArg BitVec.toNat e1; simp at hn; omega }
    try { have hn := congrArg BitVec.toNat e2; simp at hn; omega }
    try { have hn := congrArg BitVec.toNat e3; simp at hn; omega }
    try { have hn := congrArg BitVec.toNat e4; simp at hn; omega }
    try rfl

theorem branch_low (s : MachineState) :
    Low s (execInstrBr s (.BEQ .x6 .x0 88)) := by
  intro a _
  simp [execInstrBr]

theorem nonzero_sibling_low (s : MachineState) :
    Low s (GroupedBalancedVerifyTreeSiblingNonzero67.siblingState s) := by
  intro a low
  have ne0 := low_ne a low 0x80520 (by decide) (by decide)
  have ne8 := low_ne a low 0x80528 (by decide) (by decide)
  simp [GroupedBalancedVerifyTreeSiblingNonzero67.siblingState,execInstrBr,
    signExtend12,ne0,ne8,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,MachineState.getMem_setMem_ne]

theorem zero_sibling_low (s : MachineState) :
    Low s (GroupedBalancedVerifyTreeSiblingZero67.siblingState s) := by
  intro a low
  have ne0 := low_ne a low 0x80530 (by decide) (by decide)
  have ne8 := low_ne a low 0x80538 (by decide) (by decide)
  simp [GroupedBalancedVerifyTreeSiblingZero67.siblingState,execInstrBr,
    signExtend12,ne0,ne8,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,MachineState.getMem_setMem_ne]

theorem header_base (s : MachineState) :
    (GroupedBalancedVerifyTreeHeader67.headerState s).getMem 0x81000 =
      s.getMem 0x81000 := by
  simp [GroupedBalancedVerifyTreeHeader67.headerState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem nonzero_sibling_base (s : MachineState) :
    (GroupedBalancedVerifyTreeSiblingNonzero67.siblingState s).getMem 0x81000 =
      s.getMem 0x81000 := by
  simp [GroupedBalancedVerifyTreeSiblingNonzero67.siblingState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem zero_sibling_base (s : MachineState) :
    (GroupedBalancedVerifyTreeSiblingZero67.siblingState s).getMem 0x81000 =
      s.getMem 0x81000 := by
  simp [GroupedBalancedVerifyTreeSiblingZero67.siblingState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem h4_header_base (s : MachineState) :
    (GroupedBalancedVerifyTreeH4Header67.headerState s).getMem 0x81000 =
      s.getMem 0x81000 := by
  simp [GroupedBalancedVerifyTreeH4Header67.headerState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem tail_base (s : MachineState) :
    (GroupedBalancedVerifyTreeH4Tail67.updateState s).getMem 0x81000 =
      s.getMem 0x81000 + 1 := by
  simp [GroupedBalancedVerifyTreeH4Tail67.updateState,execInstrBr,signExtend12,
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

theorem nonzero_copy_base (s mid : MachineState)
    (pc : s.pc = 0x1314) (run : OrdinarySteps image s 17 mid) :
    mid.getMem 0x81000 = s.getMem 0x81000 := by
  obtain ⟨other,otherRun,_,_,_,_,frame⟩ :=
    Keygen.copy_two image 0x1314 0x500 0x530 0x80500 0x80530
      nonzero_setup_code nonzero_copy_code (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) s pc
  have eq := Keygen.ordinary_deterministic run otherRun
  subst other
  exact frame 0x81000 (by intro i; fin_cases i <;> decide)

theorem nonzero_copy_low (s mid : MachineState)
    (pc : s.pc = 0x1314) (run : OrdinarySteps image s 17 mid) :
    Low s mid := by
  obtain ⟨other,otherRun,_,_,_,_,frame⟩ :=
    Keygen.copy_two image 0x1314 0x500 0x530 0x80500 0x80530
      nonzero_setup_code nonzero_copy_code (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) s pc
  have eq := Keygen.ordinary_deterministic run otherRun
  subst other
  intro a low
  exact frame a (by
    intro i
    simpa [Signing.wordAddress] using
      low_ne a low (0x80530+8*i.val) (by omega) (by omega))

theorem zero_copy_base (s mid : MachineState)
    (pc : s.pc = 0x1368) (run : OrdinarySteps image s 17 mid) :
    mid.getMem 0x81000 = s.getMem 0x81000 := by
  obtain ⟨other,otherRun,_,_,_,_,frame⟩ :=
    Keygen.copy_two image 0x1368 0x500 0x520 0x80500 0x80520
      zero_setup_code zero_copy_code (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) s pc
  have eq := Keygen.ordinary_deterministic run otherRun
  subst other
  exact frame 0x81000 (by intro i; fin_cases i <;> decide)

theorem zero_copy_low (s mid : MachineState)
    (pc : s.pc = 0x1368) (run : OrdinarySteps image s 17 mid) :
    Low s mid := by
  obtain ⟨other,otherRun,_,_,_,_,frame⟩ :=
    Keygen.copy_two image 0x1368 0x500 0x520 0x80500 0x80520
      zero_setup_code zero_copy_code (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) s pc
  have eq := Keygen.ordinary_deterministic run otherRun
  subst other
  intro a low
  exact frame a (by
    intro i
    simpa [Signing.wordAddress] using
      low_ne a low (0x80520+8*i.val) (by omega) (by omega))

theorem sibling_paths_base (s : MachineState) (p : Word)
    (pc : s.pc = 0x1314 ∨ s.pc = 0x1368)
    (pointer : s.getMem 0x81048 = p)
    (valid0 : accessValid p 8 = true)
    (valid8 : accessValid (p+8) 8 = true) :
    ∃ n final, (n = 26 ∨ n = 27) ∧ OrdinarySteps image s n final ∧
      final.pc = 0x13b8 ∧ final.getMem 0x81048 = p ∧
      final.getMem 0x81050 = s.getMem 0x81050 ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      GroupedBalancedVerifyTreeHighFrame67.SafeFrame s final ∧
      Low s final := by
  rcases pc with nonzero | zero
  · obtain ⟨final,run,endPC,endPointer,endCount,safe⟩ :=
      GroupedBalancedVerifyTreeSiblingNonzero67.nonzero_path s p
        nonzero pointer valid0 valid8
    obtain ⟨copied,copyRun,copyPC,_,copyPointer,_,_⟩ :=
      GroupedBalancedVerifyTreeSiblingNonzero67.copy_current s nonzero
    let staged := GroupedBalancedVerifyTreeSiblingNonzero67.siblingState copied
    let sameFinal := execInstrBr staged (.JAL .x0 84)
    have stagedRun := GroupedBalancedVerifyTreeSiblingNonzero67.sibling_steps
      copied p copyPC (copyPointer.trans pointer) valid0 valid8
    have stagedPC := GroupedBalancedVerifyTreeSiblingNonzero67.sibling_pc
      copied copyPC
    have jumpRun := GroupedBalancedVerifyTreeSiblingNonzero67.jump_step
      staged stagedPC
    have sameRun : OrdinarySteps image s 27 sameFinal := by
      have first := Keygen.ordinary_trans image s copied staged 17 9
        copyRun stagedRun
      have all := Keygen.ordinary_trans image s staged sameFinal 26 1
        (by simpa only [Nat.reduceAdd] using first) jumpRun
      simpa only [Nat.reduceAdd] using all
    have eq := Keygen.ordinary_deterministic run sameRun
    subst final
    refine ⟨27,sameFinal,Or.inr rfl,sameRun,endPC,endPointer,endCount,
      ?_,safe,?_⟩
    have h0 : sameFinal.getMem 0x81000 = staged.getMem 0x81000 := by
      simp [sameFinal,execInstrBr]
    exact h0.trans ((nonzero_sibling_base copied).trans
      (nonzero_copy_base s copied nonzero copyRun))
    exact ((nonzero_copy_low s copied nonzero copyRun).trans
      (nonzero_sibling_low copied)).trans (by
        intro a _
        simp [sameFinal,staged,execInstrBr])
  · obtain ⟨final,run,endPC,endPointer,endCount,safe⟩ :=
      GroupedBalancedVerifyTreeSiblingZero67.zero_path s p
        zero pointer valid0 valid8
    obtain ⟨copied,copyRun,copyPC,_,copyPointer,_,_⟩ :=
      GroupedBalancedVerifyTreeSiblingZero67.copy_current s zero
    let staged := GroupedBalancedVerifyTreeSiblingZero67.siblingState copied
    have stagedRun := GroupedBalancedVerifyTreeSiblingZero67.sibling_steps
      copied p copyPC (copyPointer.trans pointer) valid0 valid8
    have sameRun : OrdinarySteps image s 26 staged := by
      have all := Keygen.ordinary_trans image s copied staged 17 9
        copyRun stagedRun
      simpa only [Nat.reduceAdd] using all
    have eq := Keygen.ordinary_deterministic run sameRun
    subst final
    refine ⟨26,staged,Or.inl rfl,sameRun,endPC,endPointer,endCount,
      ?_,safe,?_⟩
    exact (zero_sibling_base copied).trans
      (zero_copy_base s copied zero copyRun)
    exact (zero_copy_low s copied zero copyRun).trans
      (zero_sibling_low copied)

private theorem input_setup_code :
    Keygen.CopySetupCode image 0x13b8 0x520 0x20 4 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopySetupCode
  decide
private theorem input_copy_code : Keygen.CopyCode image 0x13cc := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

theorem input_copy_base (s final : MachineState)
    (pc : s.pc = 0x13b8) (run : OrdinarySteps image s 29 final) :
    final.getMem 0x81000 = s.getMem 0x81000 := by
  let setup := Keygen.copySetup s 0x520 0x20 4
  have setupRun := Keygen.copy_setup_block image 0x13b8 0x520 0x20 4
    input_setup_code s pc
  have inv : Keygen.CopyInvariant 0x13cc 0x80520 0x80020 4 4 setup := by
    have regs := Keygen.copy_setup_regs s 0x520 0x20 4
    simp only [Keygen.CopyInvariant,setup,Keygen.copy_setup_pc,pc,
      regs.1,regs.2.1,regs.2.2]
    simp [signExtend12]
  obtain ⟨other,copyRun,_,_,frame,_,_⟩ :=
    Keygen.copy_all_frame image 0x13cc input_copy_code 0x80520 0x80020 4
      setup inv (by decide) (by decide) (by decide) (by decide) (by decide)
  have otherRun : OrdinarySteps image s 29 other := by
    have all := Keygen.ordinary_trans image s setup other 5 24
      setupRun copyRun
    simpa only [Nat.reduceAdd] using all
  have eq := Keygen.ordinary_deterministic run otherRun
  subst other
  rw [frame 0x81000 (by intro i hi; interval_cases i <;> decide)]
  exact Keygen.copy_setup_mem s 0x520 0x20 4 0x81000

theorem input_copy_low (s final : MachineState)
    (pc : s.pc = 0x13b8) (run : OrdinarySteps image s 29 final) :
    Low s final := by
  let setup := Keygen.copySetup s 0x520 0x20 4
  have setupRun := Keygen.copy_setup_block image 0x13b8 0x520 0x20 4
    input_setup_code s pc
  have inv : Keygen.CopyInvariant 0x13cc 0x80520 0x80020 4 4 setup := by
    have regs := Keygen.copy_setup_regs s 0x520 0x20 4
    simp only [Keygen.CopyInvariant,setup,Keygen.copy_setup_pc,pc,
      regs.1,regs.2.1,regs.2.2]
    simp [signExtend12]
  obtain ⟨other,copyRun,_,_,frame,_,_⟩ :=
    Keygen.copy_all_frame image 0x13cc input_copy_code 0x80520 0x80020 4
      setup inv (by decide) (by decide) (by decide) (by decide) (by decide)
  have otherRun : OrdinarySteps image s 29 other := by
    have all := Keygen.ordinary_trans image s setup other 5 24
      setupRun copyRun
    simpa only [Nat.reduceAdd] using all
  have eq := Keygen.ordinary_deterministic run otherRun
  subst other
  intro a low
  rw [frame a (by
    intro i hi
    simpa [Signing.wordAddress] using
      low_ne a low (0x80020+8*i) (by omega) (by omega))]
  exact Keygen.copy_setup_mem s 0x520 0x20 4 a

theorem h4_header_low (s : MachineState) :
    Low s (GroupedBalancedVerifyTreeH4Header67.headerState s) := by
  intro a low
  simp [GroupedBalancedVerifyTreeH4Header67.headerState,execInstrBr,
    signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,MachineState.getMem_setMem_eq,
    MachineState.getMem_setMem_ne]
  split_ifs with e1 e2 e3 e4
  all_goals
    try { have hn := congrArg BitVec.toNat e1; simp at hn; omega }
    try { have hn := congrArg BitVec.toNat e2; simp at hn; omega }
    try { have hn := congrArg BitVec.toNat e3; simp at hn; omega }
    try { have hn := congrArg BitVec.toNat e4; simp at hn; omega }
    try rfl

private theorem answer_setup_code :
    Keygen.CopySetupCode image 0x146c 0x300 0x500 2 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopySetupCode
  decide
private theorem answer_copy_code : Keygen.CopyCode image 0x1480 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

theorem answer_copy_base (s final : MachineState)
    (pc : s.pc = 0x146c) (run : OrdinarySteps image s 17 final) :
    final.getMem 0x81000 = s.getMem 0x81000 := by
  obtain ⟨other,otherRun,_,_,_,_,frame⟩ :=
    Keygen.copy_two image 0x146c 0x300 0x500 0x80300 0x80500
      answer_setup_code answer_copy_code (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) s pc
  have eq := Keygen.ordinary_deterministic run otherRun
  subst other
  exact frame 0x81000 (by intro i; fin_cases i <;> decide)

theorem answer_copy_low (s final : MachineState)
    (pc : s.pc = 0x146c) (run : OrdinarySteps image s 17 final) :
    Low s final := by
  obtain ⟨other,otherRun,_,_,_,_,frame⟩ :=
    Keygen.copy_two image 0x146c 0x300 0x500 0x80300 0x80500
      answer_setup_code answer_copy_code (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) s pc
  have eq := Keygen.ordinary_deterministic run otherRun
  subst other
  intro a low
  exact frame a (by
    intro i
    simpa [Signing.wordAddress] using
      low_ne a low (0x80500+8*i.val) (by omega) (by omega))

theorem tail_low (s : MachineState) :
    Low s (GroupedBalancedVerifyTreeH4Tail67.updateState s) := by
  intro a low
  apply GroupedBalancedVerifyTreeH4Tail67.update_mem s a
  all_goals
    intro eq
    have value := congrArg BitVec.toNat eq
    simp at value
    omega

theorem hash_base (s : MachineState) (answer : BitVec 256)
    (dest : s.getReg .x12 = 0x80300) :
    (writeHash s answer).getMem 0x81000 = s.getMem 0x81000 := by
  exact Signing.hash_answer_frame s answer dest 0x81000
    (by intro i; fin_cases i <;> decide)

theorem round_base (hash : Hash) (s : MachineState) (p c : Word)
    (pc : s.pc = 0x1290)
    (pointer : s.getMem 0x81048 = p)
    (count : s.getMem 0x81050 = c)
    (valid0 : accessValid p 8 = true)
    (valid8 : accessValid (p+8) 8 = true) :
    ∃ n final, (n = 162 ∨ n = 163) ∧
      Trace hash image s n (n+7) 1 1 final ∧
      final.getMem 0x81048 = p+16 ∧
      final.getMem 0x81050 = c+1 ∧
      final.pc = (if c+1 ≠ (10 : Word) then 0x1290 else 0x14f4) ∧
      final.getMem 0x81000 = s.getMem 0x81000+1 ∧
      SafeFrame s final ∧
      Low s final := by
  let header := GroupedBalancedVerifyTreeHeader67.headerState s
  have headerRun := GroupedBalancedVerifyTreeHeader67.header_steps s pc
  have headerPC := GroupedBalancedVerifyTreeHeader67.header_pc s pc
  let branch := execInstrBr header (.BEQ .x6 .x0 88)
  have branchRun := GroupedBalancedVerifyTreeHeader67.branch_step header headerPC
  have branchPC := GroupedBalancedVerifyTreeHeader67.branch_pc header headerPC
    (GroupedBalancedVerifyTreeHeader67.header_bit s)
  have branchCases : branch.pc = 0x1314 ∨ branch.pc = 0x1368 := by
    by_cases bit : header.getReg .x6 = 0
    · right
      have bitBV : header.getReg .x6 = 0#64 := by simpa using bit
      simpa [branch,bitBV] using branchPC
    · left
      have bitBV : ¬ header.getReg .x6 = 0#64 := by simpa using bit
      simpa [branch,bitBV] using branchPC
  have branchPointer : branch.getMem 0x81048 = p := by
    simpa [branch,execInstrBr] using
      (GroupedBalancedVerifyTreeHeader67.header_pointer s).trans pointer
  have branchCount : branch.getMem 0x81050 = c := by
    exact (GroupedBalancedVerifyTreeHeader67.branch_count header).trans
      ((GroupedBalancedVerifyTreeHeader67.header_count s).trans count)
  have branchBase : branch.getMem 0x81000 = s.getMem 0x81000 := by
    have h0 : branch.getMem 0x81000 = header.getMem 0x81000 := by
      simp [branch,execInstrBr]
    exact h0.trans (header_base s)
  obtain ⟨bn,joined,bnCases,siblingRun,joinedPC,joinedPointer,
    joinedCount,joinedBase,siblingSafe,siblingLow⟩ :=
    sibling_paths_base branch p branchCases branchPointer valid0 valid8
  obtain ⟨copied,copyRun,copyPC,_,copyPointer,copyCount,copySafe⟩ :=
    GroupedBalancedVerifyTreeH4Input67.copy_input joined joinedPC
  let ready := GroupedBalancedVerifyTreeH4Header67.headerState copied
  have header4Run := GroupedBalancedVerifyTreeH4Header67.header_block copied copyPC
  have fields := GroupedBalancedVerifyTreeH4Query67.header_fields copied copyPC
  let answered := writeHash ready (hash (hashInput ready))
  have hashRun := GroupedBalancedVerifyTreeH4Query67.hash_trace hash ready fields
  have hashPC := GroupedBalancedVerifyTreeH4Query67.hash_pc hash ready fields
  obtain ⟨stored,answerRun,answerPC,_,answerPointer,answerCount,answerSafe⟩ :=
    GroupedBalancedVerifyTreeH4Answer67.answer_copy answered hashPC
  let final := GroupedBalancedVerifyTreeH4Tail67.updateState stored
  have tailRun := GroupedBalancedVerifyTreeH4Tail67.update_block stored answerPC
  have storedPointer : stored.getMem 0x81048 = p := by
    exact answerPointer.trans
      ((GroupedBalancedVerifyTreeH4Query67.hash_pointer hash ready fields).trans
        ((GroupedBalancedVerifyTreeH4Header67.header_pointer copied).trans
          (copyPointer.trans joinedPointer)))
  have storedCount : stored.getMem 0x81050 = c := by
    exact answerCount.trans
      ((GroupedBalancedVerifyTreeH4Query67.hash_count hash ready fields).trans
        ((GroupedBalancedVerifyTreeH4Header67.header_count copied).trans
          (copyCount.trans (joinedCount.trans branchCount))))
  have storedBase : stored.getMem 0x81000 = s.getMem 0x81000 := by
    have h0 := answer_copy_base answered stored hashPC answerRun
    have h1 := hash_base ready (hash (hashInput ready)) fields.destination
    have h2 := h4_header_base copied
    have h3 := input_copy_base joined copied joinedPC copyRun
    exact h0.trans (h1.trans (h2.trans
      (h3.trans (joinedBase.trans branchBase))))
  refine ⟨136+bn,final,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rcases bnCases with h | h <;> simp [h]
  · have t0 : Trace hash image s 33 33 0 0 branch :=
      headerRun.trace.trans branchRun.trace
    have t1 := t0.trans siblingRun.trace
    have t2 := t1.trans copyRun.trace
    have t3 := t2.trans header4Run.trace
    have t4 := t3.trans hashRun
    have t5 := t4.trans answerRun.trace
    have all := t5.trans tailRun.trace
    simpa [image,final,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all
  · rw [GroupedBalancedVerifyTreeH4Tail67.update_pointer,storedPointer]
  · rw [GroupedBalancedVerifyTreeH4Tail67.update_round_count,storedCount]
  · rw [GroupedBalancedVerifyTreeH4Tail67.update_pc_count stored answerPC,
      storedCount]
  · rw [tail_base,storedBase]
  · have h0 := safe_trans
      (GroupedBalancedVerifyTreeHeader67.header_safe s)
      (GroupedBalancedVerifyTreeHeader67.branch_safe header)
    have h1 := safe_trans h0 siblingSafe
    have h2 := safe_trans h1 copySafe
    have h3 := safe_trans h2
      (GroupedBalancedVerifyTreeH4Header67.header_safe copied)
    have h4 := safe_trans h3
      (GroupedBalancedVerifyTreeH4Query67.hash_safe hash ready fields)
    have h5 := safe_trans h4 answerSafe
    exact safe_trans h5 (GroupedBalancedVerifyTreeH4Tail67.update_safe stored)
  · have h0 := (header_low s).trans (branch_low header)
    have h1 := h0.trans siblingLow
    have h2 := h1.trans (input_copy_low joined copied joinedPC copyRun)
    have h3 := h2.trans (h4_header_low copied)
    have h4 := h3.trans
      (GroupedBalancedVerifyTreePrefixSafe67.hash_low ready
        (hash (hashInput ready)) fields.destination)
    have h5 := h4.trans (answer_copy_low answered stored hashPC answerRun)
    exact h5.trans (tail_low stored)

theorem rounds_base (hash : Hash) (start : MachineState)
    (pc : start.pc = 0x1290)
    (pointer : start.getMem 0x81048 = 0x2c730)
    (counter : start.getMem 0x81050 = 0) :
    ∀ k : Nat, k ≤ 10 →
      ∃ n final, n ≤ 163*k ∧
        Trace hash image start n (n+7*k) k k final ∧
        final.pc = GroupedBalancedVerifyTreeH4Fold67.loopPC k ∧
        final.getMem 0x81048 = GroupedBalancedVerifyTreeH4Fold67.ptrAt k ∧
        final.getMem 0x81050 = GroupedBalancedVerifyTreeH4Fold67.countAt k ∧
        final.getMem 0x81000 = start.getMem 0x81000 + BitVec.ofNat 64 k ∧
        SafeFrame start final ∧
        Low start final := by
  intro k
  induction k with
  | zero =>
      intro _
      refine ⟨0,start,by decide,?_,?_,?_,?_,?_,safe_refl start,
        GroupedBalancedVerifyStackGlobal67.LowFrame.refl start⟩
      · simpa using (Trace.refl start : Trace hash image start 0 0 0 0 start)
      · simpa [GroupedBalancedVerifyTreeH4Fold67.loopPC] using pc
      · simpa [GroupedBalancedVerifyTreeH4Fold67.ptrAt] using pointer
      · simpa [GroupedBalancedVerifyTreeH4Fold67.countAt] using counter
      · simp
  | succ k ih =>
      intro hk
      have klt : k < 10 := by omega
      obtain ⟨n,mid,nBound,run,midPC,midPointer,midCounter,midBase,midSafe,
        midLow⟩ :=
        ih (by omega)
      have roundPC : mid.pc = 0x1290 := by
        simpa [GroupedBalancedVerifyTreeH4Fold67.loopPC,
          Nat.ne_of_lt klt] using midPC
      have valid0 : accessValid
          (GroupedBalancedVerifyTreeH4Fold67.ptrAt k) 8 = true := by
        interval_cases k <;> decide
      have valid8 : accessValid
          (GroupedBalancedVerifyTreeH4Fold67.ptrAt k + 8) 8 = true := by
        interval_cases k <;> decide
      obtain ⟨m,final,mCases,roundRun,endPointer,endCounter,endPC,
        endBase,roundSafe,roundLow⟩ := round_base hash mid
        (GroupedBalancedVerifyTreeH4Fold67.ptrAt k)
        (GroupedBalancedVerifyTreeH4Fold67.countAt k)
        roundPC midPointer midCounter valid0 valid8
      refine ⟨n+m,final,?_,?_,?_,?_,?_,?_,safe_trans midSafe roundSafe,
        midLow.trans roundLow⟩
      · rcases mCases with h | h <;> omega
      · have all := run.trans roundRun
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
          Nat.mul_add,Nat.add_mul] using all
      · rw [endPC]
        interval_cases k <;> decide
      · simpa [GroupedBalancedVerifyTreeH4Fold67.ptrAt] using endPointer
      · simpa [GroupedBalancedVerifyTreeH4Fold67.countAt] using endCounter
      · calc
          final.getMem 0x81000 = mid.getMem 0x81000 + 1 := endBase
          _ = (start.getMem 0x81000 + BitVec.ofNat 64 k) + 1 := by rw [midBase]
          _ = start.getMem 0x81000 + BitVec.ofNat 64 (k+1) := by
            simp [BitVec.ofNat_add,BitVec.add_assoc]

theorem ten_rounds_base (hash : Hash) (start : MachineState)
    (pc : start.pc = 0x1290)
    (pointer : start.getMem 0x81048 = 0x2c730)
    (counter : start.getMem 0x81050 = 0) :
    ∃ n final, n ≤ 1630 ∧
      Trace hash image start n (n+70) 10 10 final ∧
      final.pc = 0x14f4 ∧
      final.getMem 0x81048 = GroupedBalancedVerifyTreeH4Fold67.ptrAt 10 ∧
      final.getMem 0x81050 = GroupedBalancedVerifyTreeH4Fold67.countAt 10 ∧
      final.getMem 0x81000 = start.getMem 0x81000 + 10 ∧
      SafeFrame start final ∧
      Low start final := by
  obtain ⟨n,final,bound,run,endPC,endPointer,endCount,endBase,safe,
    low⟩ :=
    rounds_base hash start pc pointer counter 10 (by decide)
  exact ⟨n,final,by simpa using bound,by simpa using run,
    by simpa [GroupedBalancedVerifyTreeH4Fold67.loopPC] using endPC,
    endPointer,endCount,by simpa using endBase,safe,low⟩

end SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Base67
