import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafTick67
import SigGolfCandidate.Hypertree.KeygenCopyFrame
import SigGolfCandidate.TraceDeterminism

/-! Stack pointer preservation for the signer's three generated bottom-leaf copy loops. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomCopyStack67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

theorem key_copy_sp (s final : MachineState) (pc : s.pc = 0x12cc)
    (trace : OrdinarySteps image s 28 final) :
    final.getReg .x2 = s.getReg .x2 := by
  let begun := GroupedBalancedSignBottomKeyCopy67.setupState s
  obtain ⟨other,loop,_,_,_,_,sp⟩ := Keygen.copy_all_frame image 0x12dc
    GroupedBalancedSignBottomKeyCopy67.copy_code 0x20 0x80020 4 begun
    (GroupedBalancedSignBottomKeyCopy67.copy_inv s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have setup := GroupedBalancedSignBottomKeyCopy67.setup_steps s pc
  have constructed : OrdinarySteps image s 28 other := by
    simpa only [show 4+24=28 by decide] using
      Keygen.ordinary_trans image s begun other 4 24 setup loop
  have same := Keygen.ordinary_deterministic trace constructed
  rw [same,sp]
  simp [begun,GroupedBalancedSignBottomKeyCopy67.setupState,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem selected_copy_sp (s final : MachineState) (pc : s.pc = 0x1398)
    (trace : OrdinarySteps image s 17 final) :
    final.getReg .x2 = s.getReg .x2 := by
  let begun := GroupedBalancedSignBottomSeedCopies67.selectedSetup s
  obtain ⟨other,loop,_,_,_,_,sp⟩ := Keygen.copy_all_frame image 0x13ac
    GroupedBalancedSignBottomSeedCopies67.selected_copy_code 0x80300 0x20080 2 begun
    (GroupedBalancedSignBottomSeedCopies67.selected_copy_inv s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have setup := GroupedBalancedSignBottomSeedCopies67.selected_setup_steps s pc
  have constructed : OrdinarySteps image s 17 other := by
    simpa only [show 5+12=17 by decide] using
      Keygen.ordinary_trans image s begun other 5 12 setup loop
  have same := Keygen.ordinary_deterministic trace constructed
  rw [same,sp]
  simp [begun,GroupedBalancedSignBottomSeedCopies67.selectedSetup,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem input_copy_sp (s final : MachineState) (pc : s.pc = 0x13c4)
    (trace : OrdinarySteps image s 17 final) :
    final.getReg .x2 = s.getReg .x2 := by
  let begun := GroupedBalancedSignBottomSeedCopies67.inputSetup s
  obtain ⟨other,loop,_,_,_,_,sp⟩ := Keygen.copy_all_frame image 0x13d8
    GroupedBalancedSignBottomSeedCopies67.input_copy_code 0x80300 0x80020 2 begun
    (GroupedBalancedSignBottomSeedCopies67.input_copy_inv s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have setup := GroupedBalancedSignBottomSeedCopies67.input_setup_steps s pc
  have constructed : OrdinarySteps image s 17 other := by
    simpa only [show 5+12=17 by decide] using
      Keygen.ordinary_trans image s begun other 5 12 setup loop
  have same := Keygen.ordinary_deterministic trace constructed
  rw [same,sp]
  simp [begun,GroupedBalancedSignBottomSeedCopies67.inputSetup,execInstrBr,
    MachineState.getReg_setReg_ne]

#print axioms key_copy_sp
#print axioms selected_copy_sp
#print axioms input_copy_sp
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomCopyStack67

/-! Stack-pointer refinement of bottom H1/H2 query segments. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomHashStack67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

theorem h1_prelude_sp (s : MachineState) :
    (GroupedBalancedSignBottomH1Prelude67.preludeState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignBottomH1Prelude67.preludeState,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem h2_prelude_sp (s : MachineState) :
    (GroupedBalancedSignBottomH2Prelude67.preludeState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignBottomH2Prelude67.preludeState,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem h1_sp (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x12cc)
    (trace : Trace hash image s 62 69 1 1 final) :
    final.getReg .x2 = s.getReg .x2 := by
  obtain ⟨staged,copy,stagedPc,_,_⟩ :=
    GroupedBalancedSignBottomKeyCopy67.key_copy s pc
  have call := GroupedBalancedSignBottomH1Query67.secret_call hash staged stagedPc
  have constructed : Trace hash image s 62 69 1 1
      (writeHash (GroupedBalancedSignBottomH1Prelude67.preludeState staged)
        (hash (hashInput (GroupedBalancedSignBottomH1Prelude67.preludeState staged)))) := by
    simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (OrdinarySteps.trace (hash := hash) copy).trans call
  have same := trace.deterministic constructed
  rw [same,Keygen.hash_registers,h1_prelude_sp]
  exact GroupedBalancedSignBottomCopyStack67.key_copy_sp s staged pc copy

theorem select_sp (s : MachineState) :
    (GroupedBalancedSignBottomSelect67.selectState s).getReg .x2 = s.getReg .x2 := by
  simp [GroupedBalancedSignBottomSelect67.selectState,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem advance_sp (s : MachineState) :
    (GroupedBalancedSignBottomLeafAdvance67.advanceState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignBottomLeafAdvance67.advanceState,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem h2_from_seed_sp (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x13c4)
    (trace : Trace hash image s 51 58 1 1 final) :
    final.getReg .x2 = s.getReg .x2 := by
  obtain ⟨staged,copy,stagedPc,_,_⟩ :=
    GroupedBalancedSignBottomSeedCopies67.input_copy s pc
  have call := GroupedBalancedSignBottomH2Query67.leaf_call hash staged stagedPc
  have constructed : Trace hash image s 51 58 1 1
      (writeHash (GroupedBalancedSignBottomH2Prelude67.preludeState staged)
        (hash (hashInput (GroupedBalancedSignBottomH2Prelude67.preludeState staged)))) := by
    simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (OrdinarySteps.trace (hash := hash) copy).trans call
  have same := trace.deterministic constructed
  rw [same,Keygen.hash_registers,h2_prelude_sp]
  exact GroupedBalancedSignBottomCopyStack67.input_copy_sp s staged pc copy

theorem h2_sp (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x137c)
    (trace : Trace hash image s
      (if s.getMem 0x810e0 = s.getMem 0x810e8 then 75 else 58)
      (if s.getMem 0x810e0 = s.getMem 0x810e8 then 82 else 65)
      1 1 final) :
    final.getReg .x2 = s.getReg .x2 := by
  let routed := GroupedBalancedSignBottomSelect67.selectState s
  have route := GroupedBalancedSignBottomSelect67.select_steps s pc
  have routePc := GroupedBalancedSignBottomSelect67.select_pc s pc
  by_cases chosen : s.getMem 0x810e0 = s.getMem 0x810e8
  · have selectedPc : routed.pc = 0x1398 := by rw [routePc,if_pos chosen]
    obtain ⟨copied,copy,copiedPc,_,_⟩ :=
      GroupedBalancedSignBottomSeedCopies67.selected_copy routed selectedPc
    obtain ⟨staged,inputCopy,stagedPc,_,_⟩ :=
      GroupedBalancedSignBottomSeedCopies67.input_copy copied copiedPc
    have call := GroupedBalancedSignBottomH2Query67.leaf_call hash staged stagedPc
    have constructed : Trace hash image s 75 82 1 1
        (writeHash (GroupedBalancedSignBottomH2Prelude67.preludeState staged)
          (hash (hashInput (GroupedBalancedSignBottomH2Prelude67.preludeState staged)))) := by
      simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (((OrdinarySteps.trace (hash := hash) route).trans
          (OrdinarySteps.trace (hash := hash) copy)).trans
          (OrdinarySteps.trace (hash := hash) inputCopy)).trans call
    have actual : Trace hash image s 75 82 1 1 final := by
      simpa only [if_pos chosen] using trace
    have same := actual.deterministic constructed
    rw [same,Keygen.hash_registers,h2_prelude_sp]
    exact (GroupedBalancedSignBottomCopyStack67.input_copy_sp copied staged
      copiedPc inputCopy).trans
        ((GroupedBalancedSignBottomCopyStack67.selected_copy_sp routed copied
          selectedPc copy).trans (select_sp s))
  · have skippedPc : routed.pc = 0x13c4 := by rw [routePc,if_neg chosen]
    obtain ⟨staged,inputCopy,stagedPc,_,_⟩ :=
      GroupedBalancedSignBottomSeedCopies67.input_copy routed skippedPc
    have call := GroupedBalancedSignBottomH2Query67.leaf_call hash staged stagedPc
    have constructed : Trace hash image s 58 65 1 1
        (writeHash (GroupedBalancedSignBottomH2Prelude67.preludeState staged)
          (hash (hashInput (GroupedBalancedSignBottomH2Prelude67.preludeState staged)))) := by
      simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        ((OrdinarySteps.trace (hash := hash) route).trans
          (OrdinarySteps.trace (hash := hash) inputCopy)).trans call
    have actual : Trace hash image s 58 65 1 1 final := by
      simpa only [if_neg chosen] using trace
    have same := actual.deterministic constructed
    rw [same,Keygen.hash_registers,h2_prelude_sp]
    exact (GroupedBalancedSignBottomCopyStack67.input_copy_sp routed staged
      skippedPc inputCopy).trans (select_sp s)

theorem leaf_tick_sp (hash : Hash) (secretKey : SecretKey)
    (leaf : Nat) (s final : MachineState)
    (pc : s.pc = 0x12cc)
    (counter : (s.getMem 0x810e0).toNat < 1024)
    (level : s.getMem 0x81000 = 0)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (keyWords : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64)
    (trace : Trace hash image s
      (if s.getMem 0x810e0 = s.getMem 0x810e8 then 166 else 149)
      (if s.getMem 0x810e0 = s.getMem 0x810e8 then 180 else 163)
      2 2 final) :
    final.getReg .x2 = s.getReg .x2 := by
  obtain ⟨_,_,seeded,h1,_,_,seededPc,_,_,seedWords,
    seedLevel,seedAddress,seedFrame⟩ :=
    GroupedBalancedSignBottomH1Loop67.loop_seed hash s secretKey leaf
      pc level address keyWords
  have seedCounter : seeded.getMem 0x810e0 = s.getMem 0x810e0 :=
    seedFrame 0x810e0 (by decide) (by decide) (by decide) (by decide)
      (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
  have seedChosen : seeded.getMem 0x810e8 = s.getMem 0x810e8 :=
    seedFrame 0x810e8 (by decide) (by decide) (by decide) (by decide)
      (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
  obtain ⟨_,leafAfter,h2,_,leafAfterPc,_,_,leafFrame⟩ :=
    GroupedBalancedSignBottomFirstH267.first_leaf_h2 hash seeded leaf
      (GroupedBottomTree.secret hash secretKey leaf) seededPc
      seedLevel seedAddress seedWords
  have leafCounter : leafAfter.getMem 0x810e0 = s.getMem 0x810e0 := by
    rw [leafFrame.1 0x810e0 (by decide) (by decide) (by decide)
      (by decide) (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)]
    exact seedCounter
  have leafBound : (leafAfter.getMem 0x810e0).toNat < 1024 := by
    rw [leafCounter]
    exact counter
  have advance :=
    (GroupedBalancedSignBottomLeafAdvanceData67.advance_trace hash leafAfter
      leafAfterPc leafBound).1
  let result := GroupedBalancedSignBottomLeafAdvance67.advanceState leafAfter
  have constructed : Trace hash image s
      (if s.getMem 0x810e0 = s.getMem 0x810e8 then 166 else 149)
      (if s.getMem 0x810e0 = s.getMem 0x810e8 then 180 else 163)
      2 2 result := by
    by_cases chosen : s.getMem 0x810e0 = s.getMem 0x810e8
    · have seededChosen : seeded.getMem 0x810e0 = seeded.getMem 0x810e8 := by
        rw [seedCounter,seedChosen]
        exact chosen
      simp only [if_pos seededChosen] at h2
      simp only [if_pos chosen]
      simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (h1.trans h2).trans advance
    · have seededSkipped : seeded.getMem 0x810e0 ≠ seeded.getMem 0x810e8 := by
        rw [seedCounter,seedChosen]
        exact chosen
      simp only [if_neg seededSkipped] at h2
      simp only [if_neg chosen]
      simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (h1.trans h2).trans advance
  have same := trace.deterministic constructed
  rw [same,advance_sp,
    h2_sp hash seeded leafAfter seededPc h2,
    h1_sp hash s seeded pc h1]

#print axioms h1_sp
#print axioms h2_sp
#print axioms leaf_tick_sp
#print axioms select_sp
#print axioms advance_sp
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomHashStack67
