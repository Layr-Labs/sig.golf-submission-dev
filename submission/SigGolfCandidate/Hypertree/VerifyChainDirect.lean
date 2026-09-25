import SigGolfCandidate.Hypertree.VerifyChainHeaderDirect
import SigGolfCandidate.Hypertree.KeygenCopySetup

namespace SigGolfCandidate.Hypertree.VerifyChainDirect
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen Signing
set_option maxRecDepth 4096

/-- The verifier keeps each chain answer in the value buffer and skips the old answer copy. -/
def Code (image : Image) (p : Word) : Prop :=
  CopySetupCode image p 0x510 0x20 2 ∧ CopyCode image (p+20) ∧
  VerifyChainHeaderDirect.Code image (p+44) ∧
  instructionAt image (p+236) = some (.base .ECALL) ∧
  instructionAt image (p+240) = some (.base (.JAL .x0 44))

instance (image : Image) (p : Word) : Decidable (Code image p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

theorem verify_code : Code verify 0x1500 := by decide

private theorem answer_word (s : MachineState) (answer : BitVec 256)
    (dst : s.getReg .x12 = 0x80510) (i : Fin 2) :
    (writeHash s answer).getMem (wordAddress 0x80510 i.val) =
      answer.extractLsb' (64*i.val) 64 := by
  fin_cases i <;> simp [writeHash, dst, wordAddress, MachineState.writeWords]

private theorem answer_frame (s : MachineState) (answer : BitVec 256)
    (dst : s.getReg .x12 = 0x80510) (a : Word)
    (outside : ∀ i : Fin 4, a ≠ wordAddress 0x80510 i.val) :
    (writeHash s answer).getMem a = s.getMem a := by
  have h0 : a ≠ 0x80510 := outside 0
  have h1 : a ≠ 0x80518 := outside 1
  have h2 : a ≠ 0x80520 := outside 2
  have h3 : a ≠ 0x80528 := outside 3
  simp only [writeHash, MachineState.getMem_setPC, dst, MachineState.writeWords,
    Expansion.mem_setMem]
  change (if a = 0x80528 then _ else if a = 0x80520 then _ else
    if a = 0x80518 then _ else if a = 0x80510 then _ else s.getMem a) = s.getMem a
  rw [if_neg h3, if_neg h2, if_neg h1, if_neg h0]

private def jumped (s : MachineState) : MachineState := execInstrBr s (.JAL .x0 44)

private theorem jump_block (image : Image) (p : Word)
    (code : instructionAt image p = some (.base (.JAL .x0 44)))
    (s : MachineState) (pc : s.pc = p) : OrdinarySteps image s 1 (jumped s) := by
  apply OrdinarySteps.step s (jumped s) _ (.base (.JAL .x0 44)) 0
  · simpa only [fetch_at, pc] using code
  · rfl
  exact OrdinarySteps.refl _

private theorem jump_pc (s : MachineState) : (jumped s).pc = s.pc + 44 := by
  simp [jumped, execInstrBr]
  decide

private theorem jump_mem (s : MachineState) (a : Word) : (jumped s).getMem a = s.getMem a := by
  simp [jumped, execInstrBr]

private theorem jump_stack (s : MachineState) :
    (jumped s).getReg .x1 = s.getReg .x1 ∧ (jumped s).getReg .x2 = s.getReg .x2 := by
  simp [jumped, execInstrBr, MachineState.getReg_setReg_ne]

/-- One verifier chain HASH core, including the one-instruction jump over the unused copy. -/
theorem compute (image : Image) (hash : Hash) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) (level tree step : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (hlevel : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (hleaf : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side))
    (hchain : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (hstep : s.getMem 0x80438 = BitVec.ofNat 64 step)
    (hindex : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (hvalue : ∀ i : Fin 2, s.getMem (wordAddress 0x80510 i.val) =
      value.extractLsb' (64*i.val) 64) :
    ∃ final, Trace hash image s 67 74 1 1 final ∧ final.pc = p+284 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80510 i.val) =
        (Reference.chainHash hash level tree side chain step value).extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 6, a ≠ wordAddress 0x80000 i.val) →
        (∀ i : Fin 4, a ≠ wordAddress 0x80510 i.val) →
        final.getMem a = s.getMem a) := by
  obtain ⟨copied, pre, cpc, content, cra, csp, cframe⟩ :=
    copy_two image p 0x510 0x20 0x80510 0x80020 code.1 code.2.1
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s pc
  have levelEq : copied.getMem 0x80400 = BitVec.ofNat 64 level := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact hlevel
  have leafEq : copied.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side) := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact hleaf
  have chainEq : copied.getMem 0x80430 = BitVec.ofNat 64 chain.val := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact hchain
  have stepEq : copied.getMem 0x80438 = BitVec.ofNat 64 step := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact hstep
  have indexEq : ∀ i : Fin 3, copied.getMem (wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    rw [cframe _ (by intro j; fin_cases i <;> fin_cases j <;> decide)]
    exact hindex i
  have valueEq : ∀ i : Fin 2, copied.getMem (wordAddress 0x80020 i.val) =
      value.extractLsb' (64*i.val) 64 := by intro i; rw [content i]; exact hvalue i
  let prepared := VerifyChainHeaderDirect.state copied
  have headTrace := VerifyChainHeaderDirect.block image (p+44) code.2.2.1 copied cpc
  have hpc : prepared.pc = p+236 := by
    simp only [prepared, VerifyChainHeaderDirect.pc, cpc]; simp [BitVec.add_assoc]
  obtain ⟨service, source, bits, destination⟩ := VerifyChainHeaderDirect.regs copied
  have words := VerifyChainHeaderDirect.words copied level tree (Reference.sideNumber side) chain.val step value
    levelEq leafEq chainEq stepEq indexEq valueEq
  have hf : fetch image prepared = some (.base .ECALL) := by
    simpa only [fetch_at, hpc] using code.2.2.2.1
  have valid : hashArgumentsValid prepared = true := by
    change hashArgumentsValid (VerifyChainHeaderDirect.state copied) = true
    simp [hashArgumentsValid, source, bits, destination, accessValid, rangeValid, MEMORY_BYTES]
  let answer := hash (hashInput prepared)
  let hashed := writeHash prepared answer
  have hashTrace : Trace hash image prepared 1 8 1 1 hashed := by
    have length : (hashInput prepared).1 = 384 := by
      change (prepared.getReg .x11).toNat = 384
      rw [bits]
      decide
    simpa [hashed, answer, length, compressions] using
      Trace.hash prepared hashed 0 0 0 0 hf service valid (Trace.refl hashed)
  have hashPC : hashed.pc = p+240 := by simp only [hashed, hash_pc, hpc]; simp [BitVec.add_assoc]
  have jumpCode : instructionAt image (p+240) = some (.base (.JAL .x0 44)) := code.2.2.2.2
  have post := jump_block image (p+240) jumpCode hashed hashPC
  let final := jumped hashed
  have answerEq : answer = Reference.query hash 2 level tree (Reference.sideNumber side) chain.val step (bytes value) := by
    change hash (hashInput prepared) = Reference.query hash 2 level tree
      (Reference.sideNumber side) chain.val step (bytes value)
    rw [KeygenDomain.query_eq prepared _ tree value source bits words]
    rfl
  refine ⟨final, pre.trace.trans (headTrace.trace.trans (hashTrace.trans post.trace)), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [final, jump_pc, hashPC]; simp [BitVec.add_assoc]
  · intro i
    rw [jump_mem, answer_word prepared answer destination i, answerEq]
    let result := Reference.query hash 2 level tree (Reference.sideNumber side) chain.val step (bytes value)
    change result.extractLsb' (64*i.val) 64 = (result.extractLsb' 0 128).extractLsb' (64*i.val) 64
    fin_cases i <;> ext j hj <;> simp (disch := omega)
  · exact (jump_stack hashed).1.trans ((hash_registers _ _ _).trans ((VerifyChainHeaderDirect.stack copied).1.trans cra))
  · exact (jump_stack hashed).2.trans ((hash_registers _ _ _).trans ((VerifyChainHeaderDirect.stack copied).2.trans csp))
  · intro a inputOutside valueOutside
    rw [jump_mem, answer_frame prepared answer destination a valueOutside,
      VerifyChainHeaderDirect.frame copied a (fun i => inputOutside ⟨i.val,by have := i.isLt; omega⟩)]
    apply cframe
    intro i
    have h := inputOutside ⟨i.val+4,by have := i.isLt; omega⟩
    simpa [wordAddress,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

end SigGolfCandidate.Hypertree.VerifyChainDirect
