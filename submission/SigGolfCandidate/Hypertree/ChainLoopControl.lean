import SigGolfCandidate.Hypertree.KeygenChainHeader
import SigGolfCandidate.Hypertree.KeygenCopySetup

/-! Inlined from SigGolfCandidate.Hypertree.KeygenChainExecution; its only importer was SigGolfCandidate.Hypertree.ChainLoopControl. -/
section
namespace SigGolfCandidate.Hypertree.KeygenChain
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096

def Code (image : Image) (p : Word) : Prop :=
  CopySetupCode image p 0x510 0x20 2 ∧ CopyCode image (p+20) ∧
  KeygenChainHeader.Code image (p+44) ∧
  instructionAt image (p+236) = some (.base .ECALL) ∧
  CopySetupCode image (p+240) 0x300 0x510 2 ∧ CopyCode image (p+260)

instance (image : Image) (p : Word) : Decidable (Code image p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- One complete chain HASH core, shared by generation, signing, and verification. -/
theorem compute (image : Image) (hash : Hash) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) (level tree step : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (hlevel : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (hleaf : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side))
    (hchain : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (hstep : s.getMem 0x80438 = BitVec.ofNat 64 step)
    (hindex : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (hvalue : ∀ i : Fin 2, s.getMem (Signing.wordAddress 0x80510 i.val) =
      value.extractLsb' (64*i.val) 64) :
    ∃ final, Trace hash image s 83 90 1 1 final ∧ final.pc = p+284 ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress 0x80510 i.val) =
        (Reference.chainHash hash level tree side chain step value).extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 6, a ≠ Signing.wordAddress 0x80000 i.val) →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) →
        (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80510 i.val) →
        final.getMem a = s.getMem a) := by
  obtain ⟨copied,pre,cpc,content,cra,csp,cframe⟩ :=
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
  have indexEq : ∀ i : Fin 3, copied.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    rw [cframe _ (by intro j; fin_cases i <;> fin_cases j <;> decide)]
    exact hindex i
  have valueEq : ∀ i : Fin 2, copied.getMem (Signing.wordAddress 0x80020 i.val) =
      value.extractLsb' (64*i.val) 64 := by intro i; rw [content i]; exact hvalue i
  let prepared := KeygenChainHeader.state copied
  have headTrace := KeygenChainHeader.block image (p+44) code.2.2.1 copied cpc
  have hpc : prepared.pc = p+236 := by
    simp only [prepared,KeygenChainHeader.pc,cpc]; simp [BitVec.add_assoc]
  obtain ⟨service,source,bits,destination⟩ := KeygenChainHeader.regs copied
  have words := KeygenChainHeader.words copied level tree (Reference.sideNumber side) chain.val step value
    levelEq leafEq chainEq stepEq indexEq valueEq
  have hf : fetch image prepared = some (.base .ECALL) := by
    simpa only [fetch_at,hpc] using code.2.2.2.1
  let hashed := writeHash prepared (hash (hashInput prepared))
  have hashTrace := KeygenDomain.hash_trace image hash prepared hf service source bits destination
  have hashPC : hashed.pc = p+240 := by simp only [hashed,hash_pc,hpc]; simp [BitVec.add_assoc]
  have suffixCode : CopyCode image ((p+240)+20) := by
    simpa [BitVec.add_assoc] using code.2.2.2.2.2
  obtain ⟨final,post,fpc,result,fra,fsp,fframe⟩ :=
    copy_two image (p+240) 0x300 0x510 0x80300 0x80510 code.2.2.2.2.1 suffixCode
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hashed hashPC
  refine ⟨final,pre.trace.trans (headTrace.trace.trans (hashTrace.trans post.trace)),?_,?_,?_,?_,?_⟩
  · simpa [BitVec.add_assoc] using fpc
  · intro i
    rw [result i]
    exact KeygenDomain.answer_words hash prepared 2 level tree (Reference.sideNumber side) chain.val step value
      source bits destination words i
  · exact fra.trans ((hash_registers _ _ _).trans ((KeygenChainHeader.stack copied).1.trans cra))
  · exact fsp.trans ((hash_registers _ _ _).trans ((KeygenChainHeader.stack copied).2.trans csp))
  · intro a inputOutside answerOutside valueOutside
    rw [fframe a valueOutside,Signing.hash_answer_frame prepared _ destination a answerOutside]
    rw [KeygenChainHeader.frame copied a (fun i => inputOutside ⟨i.val,by have := i.isLt; omega⟩)]
    apply cframe
    intro i
    have h := inputOutside ⟨i.val+4,by have := i.isLt; omega⟩
    simpa [Signing.wordAddress,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem keygen_code : Code keygen 0x13b8 := by decide

/-- info: 'SigGolfCandidate.Hypertree.KeygenChain.compute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compute

end SigGolfCandidate.Hypertree.KeygenChain

end

namespace SigGolfCandidate.Hypertree.ChainLoopControl
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def CheckCode (image : Image) (p : Word) : Prop :=
  instructionAt image (p + 0) = some (.base (.LUI .x28 0x80)) ∧
  instructionAt image (p + 4) = some (.base (.ADDI .x28 .x28 0x438)) ∧
  instructionAt image (p + 8) = some (.base (.LD .x6 .x28 0)) ∧
  instructionAt image (p + 12) = some (.base (.ADDI .x7 .x0 7)) ∧
  instructionAt image (p + 16) = some (.base (.BEQ .x6 .x7 320))

instance (image : Image) (p : Word) : Decidable (CheckCode image p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def check (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x438)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x7 .x0 7)
  execInstrBr s (.BEQ .x6 .x7 320)

theorem check_block (image : Image) (p : Word) (code : CheckCode image p)
    (s : MachineState) (pc : s.pc = p) : OrdinarySteps image s 5 (check s) := by
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x438)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x7 .x0 7)
  let s5 := execInstrBr s4 (.BEQ .x6 .x7 320)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 4
  · have hp : s.pc = p + 0 := by simp [execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using code.1
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x438)) 3
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using code.2.1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 2
  · have hp : s2.pc = p + 8 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using code.2.2.1
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x0 7)) 1
  · have hp : s3.pc = p + 12 := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using code.2.2.2.1
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.BEQ .x6 .x7 320)) 0
  · have hp : s4.pc = p + 16 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using code.2.2.2.2
  · rfl
  exact OrdinarySteps.refl _

def IncrementCode (image : Image) (p : Word) (jump : BitVec 21) : Prop :=
  instructionAt image (p + 0) = some (.base (.LUI .x28 0x80)) ∧
  instructionAt image (p + 4) = some (.base (.ADDI .x28 .x28 0x438)) ∧
  instructionAt image (p + 8) = some (.base (.LD .x6 .x28 0)) ∧
  instructionAt image (p + 12) = some (.base (.ADDI .x6 .x6 1)) ∧
  instructionAt image (p + 16) = some (.base (.LUI .x28 0x80)) ∧
  instructionAt image (p + 20) = some (.base (.ADDI .x28 .x28 0x438)) ∧
  instructionAt image (p + 24) = some (.base (.SD .x28 .x6 0)) ∧
  instructionAt image (p + 28) = some (.base (.JAL .x0 jump))

instance (image : Image) (p : Word) (jump : BitVec 21) : Decidable (IncrementCode image p jump) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def increment (s : MachineState) (jump : BitVec 21) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x438)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x438)
  let s := execInstrBr s (.SD .x28 .x6 0)
  execInstrBr s (.JAL .x0 jump)

theorem increment_block (image : Image) (p : Word) (jump : BitVec 21) (code : IncrementCode image p jump)
    (s : MachineState) (pc : s.pc = p) : OrdinarySteps image s 8 (increment s jump) := by
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x438)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 1)
  let s5 := execInstrBr s4 (.LUI .x28 0x80)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 0x438)
  let s7 := execInstrBr s6 (.SD .x28 .x6 0)
  let s8 := execInstrBr s7 (.JAL .x0 jump)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 7
  · have hp : s.pc = p + 0 := by simp [execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using code.1
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x438)) 6
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using code.2.1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 5
  · have hp : s2.pc = p + 8 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using code.2.2.1
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 1)) 4
  · have hp : s3.pc = p + 12 := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using code.2.2.2.1
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x80)) 3
  · have hp : s4.pc = p + 16 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using code.2.2.2.2.1
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 0x438)) 2
  · have hp : s5.pc = p + 20 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using code.2.2.2.2.2.1
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x6 0)) 1
  · have hp : s6.pc = p + 24 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using code.2.2.2.2.2.2.1
  · simp [s1, s2, s3, s4, s5, s6, s7, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 s8 _ (.base (.JAL .x0 jump)) 0
  · have hp : s7.pc = p + 28 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using code.2.2.2.2.2.2.2
  · rfl
  exact OrdinarySteps.refl _

theorem check_pc (s : MachineState) :
    (check s).pc = s.pc + (if s.getMem 0x80438 = 7 then 336 else 20) := by
  simp [check, execInstrBr, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, BitVec.add_assoc]
  split <;> rfl

theorem check_mem (s : MachineState) (a : Word) :
    (check s).getMem a = s.getMem a := by simp [check, execInstrBr]

theorem check_stack (s : MachineState) :
    (check s).getReg .x1 = s.getReg .x1 ∧ (check s).getReg .x2 = s.getReg .x2 := by
  simp [check, execInstrBr, MachineState.getReg_setReg_ne]

theorem increment_pc (s : MachineState) (jump : BitVec 21) :
    (increment s jump).pc = s.pc + 28 + signExtend21 jump := by
  simp [increment, execInstrBr, BitVec.add_assoc]

theorem increment_mem (s : MachineState) (jump : BitVec 21) (a : Word) :
    (increment s jump).getMem a = if a = 0x80438 then s.getMem 0x80438 + 1 else s.getMem a := by
  simp [increment, execInstrBr, signExtend12, Expansion.mem_setMem,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem increment_stack (s : MachineState) (jump : BitVec 21) :
    (increment s jump).getReg .x1 = s.getReg .x1 ∧ (increment s jump).getReg .x2 = s.getReg .x2 := by
  simp [increment, execInstrBr, MachineState.getReg_setReg_ne]

/-- info: 'SigGolfCandidate.Hypertree.ChainLoopControl.increment_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms increment_block

end SigGolfCandidate.Hypertree.ChainLoopControl
