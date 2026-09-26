import SigGolfCandidate.Hypertree.KeygenCopyFrame
import SigGolfCandidate.Hypertree.KeygenSecretHeader
import SigGolfCandidate.Hypertree.KeygenCopySetup

/-! Inlined from SigGolfCandidate.Hypertree.KeygenSecretKeyCopy; its only importer was SigGolfCandidate.Hypertree.KeygenSecretExecution. -/
section
namespace SigGolfCandidate.Hypertree.KeygenSecretKey
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen

def Code (image : Image) (p : Word) : Prop :=
  instructionAt image p = some (.base (.ADDI .x6 .x0 0x20)) ∧
  instructionAt image (p+4) = some (.base (.LUI .x7 128)) ∧
  instructionAt image (p+8) = some (.base (.ADDI .x7 .x7 0x20)) ∧
  instructionAt image (p+12) = some (.base (.ADDI .x10 .x0 4)) ∧
  CopyCode image (p+16)

instance (image : Image) (p : Word) : Decidable (Code image p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def setup (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0x20)
  let s := execInstrBr s (.LUI .x7 128)
  let s := execInstrBr s (.ADDI .x7 .x7 0x20)
  execInstrBr s (.ADDI .x10 .x0 4)

theorem setup_block (image : Image) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) : OrdinarySteps image s 4 (setup s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0x20)
  let s2 := execInstrBr s1 (.LUI .x7 128)
  let s3 := execInstrBr s2 (.ADDI .x7 .x7 0x20)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0x20)) 3
  · simpa only [fetch_at,pc] using code.1
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x7 128)) 2
  · simpa only [fetch_at,s1,execInstrBr,MachineState.setPC,pc] using code.2.1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x7 .x7 0x20)) 1
  · have hp : s2.pc = p+8 := by simp [s1,s2,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using code.2.2.1
  · rfl
  apply OrdinarySteps.step s3 (setup s) _ (.base (.ADDI .x10 .x0 4)) 0
  · have hp : s3.pc = p+12 := by simp [s1,s2,s3,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using code.2.2.2.1
  · rfl
  exact OrdinarySteps.refl _

theorem setup_pc (s : MachineState) : (setup s).pc = s.pc+16 := by
  simp [setup,execInstrBr,BitVec.add_assoc]

theorem setup_regs (s : MachineState) :
    (setup s).getReg .x6 = 0x20 ∧ (setup s).getReg .x7 = 0x80020 ∧ (setup s).getReg .x10 = 4 := by
  simp [setup,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem setup_mem (s : MachineState) (a : Word) : (setup s).getMem a = s.getMem a := by
  simp [setup,execInstrBr]

theorem setup_stack (s : MachineState) :
    (setup s).getReg .x1 = s.getReg .x1 ∧ (setup s).getReg .x2 = s.getReg .x2 := by
  simp [setup,execInstrBr,MachineState.getReg_setReg_ne]

/-- The exact secret key copy makes both 64-bit words available to the secret HASH. -/
theorem copy (image : Image) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) :
    ∃ final, OrdinarySteps image s 28 final ∧ final.pc = p+40 ∧
      (∀ i : Fin 4, final.getMem (Signing.wordAddress 0x80020 i.val) =
        s.getMem (Signing.wordAddress 0x20 i.val)) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80020 i.val) → final.getMem a = s.getMem a) := by
  have inv : CopyInvariant (p+16) 0x20 0x80020 4 4 (setup s) := by
    have regs := setup_regs s
    simp [CopyInvariant,setup_pc,pc,regs.1,regs.2.1,regs.2.2]
  obtain ⟨final,trace,done,content,frame,ra,sp⟩ :=
    copy_all_frame image (p+16) code.2.2.2.2 0x20 0x80020 4 (setup s) inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final,ordinary_trans image _ _ _ 4 24 (setup_block image p code s pc) trace,?_,?_,
    ra.trans (setup_stack s).1,sp.trans (setup_stack s).2,?_⟩
  · simpa [BitVec.add_assoc] using done.2.2.1
  · intro i
    rw [content i.val i.isLt,setup_mem]
  · intro a outside
    rw [frame a (fun i hi => outside ⟨i,hi⟩),setup_mem]

theorem keygen_code : Code keygen 0x1204 := by decide

end SigGolfCandidate.Hypertree.KeygenSecretKey

end

namespace SigGolfCandidate.Hypertree.KeygenSecret
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096

def Code (image : Image) (p : Word) : Prop :=
  KeygenSecretKey.Code image p ∧ KeygenSecretHeader.Code image (p+40) ∧
  instructionAt image (p+212) = some (.base .ECALL) ∧
  CopySetupCode image (p+216) 0x300 0x510 2 ∧ CopyCode image (p+236)

instance (image : Image) (p : Word) : Decidable (Code image p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- One complete secret HASH core, shared by key generation and signing. -/
theorem compute (image : Image) (hash : Hash) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) (level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (secretKey : SecretKey)
    (hlevel : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (hleaf : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side))
    (hchain : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (hindex : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (hsecretKey : ∀ i : Fin 4, s.getMem (Signing.wordAddress 0x20 i.val) =
      secretKey.extractLsb' (64*i.val) 64) :
    ∃ final, Trace hash image s 89 96 1 1 final ∧ final.pc = p+260 ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress 0x80510 i.val) =
        (Reference.secret hash secretKey level tree side chain).extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 8, a ≠ Signing.wordAddress 0x80000 i.val) →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) →
        (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80510 i.val) →
        final.getMem a = s.getMem a) := by
  obtain ⟨copied,pre,cpc,content,cra,csp,cframe⟩ :=
    KeygenSecretKey.copy image p code.1 s pc
  have levelEq : copied.getMem 0x80400 = BitVec.ofNat 64 level := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact hlevel
  have leafEq : copied.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side) := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact hleaf
  have chainEq : copied.getMem 0x80430 = BitVec.ofNat 64 chain.val := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact hchain
  have indexEq : ∀ i : Fin 3, copied.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    rw [cframe _ (by intro j; fin_cases i <;> fin_cases j <;> decide)]
    exact hindex i
  have valueEq : ∀ i : Fin 4, copied.getMem (Signing.wordAddress 0x80020 i.val) =
      secretKey.extractLsb' (64*i.val) 64 := by intro i; rw [content i]; exact hsecretKey i
  let prepared := KeygenSecretHeader.state copied
  have headTrace := KeygenSecretHeader.block image (p+40) code.2.1 copied cpc
  have hpc : prepared.pc = p+212 := by
    simp only [prepared,KeygenSecretHeader.pc,cpc]; simp [BitVec.add_assoc]
  obtain ⟨service,source,bits,destination⟩ := KeygenSecretHeader.regs copied
  have words := KeygenSecretHeader.words copied level tree (Reference.sideNumber side) chain.val secretKey
    levelEq leafEq chainEq indexEq valueEq
  have hf : fetch image prepared = some (.base .ECALL) := by
    simpa only [fetch_at,hpc] using code.2.2.1
  let hashed := writeHash prepared (hash (hashInput prepared))
  have hashTrace := KeygenDomain.secret_hash_trace image hash prepared hf service source bits destination
  have hashPC : hashed.pc = p+216 := by simp only [hashed,hash_pc,hpc]; simp [BitVec.add_assoc]
  have suffixCode : CopyCode image ((p+216)+20) := by
    simpa [BitVec.add_assoc] using code.2.2.2.2
  obtain ⟨final,post,fpc,result,fra,fsp,fframe⟩ :=
    copy_two image (p+216) 0x300 0x510 0x80300 0x80510 code.2.2.2.1 suffixCode
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hashed hashPC
  refine ⟨final,pre.trace.trans (headTrace.trace.trans (hashTrace.trans post.trace)),?_,?_,?_,?_,?_⟩
  · simpa [BitVec.add_assoc] using fpc
  · intro i
    rw [result i]
    exact KeygenDomain.secret_answer_words hash prepared level tree (Reference.sideNumber side) chain.val secretKey
      source bits destination words i
  · exact fra.trans ((hash_registers _ _ _).trans ((KeygenSecretHeader.stack copied).1.trans cra))
  · exact fsp.trans ((hash_registers _ _ _).trans ((KeygenSecretHeader.stack copied).2.trans csp))
  · intro a inputOutside answerOutside valueOutside
    rw [fframe a valueOutside,Signing.hash_answer_frame prepared _ destination a answerOutside]
    rw [KeygenSecretHeader.frame copied a (fun i => inputOutside ⟨i.val,by have := i.isLt; omega⟩)]
    apply cframe
    intro i
    have h := inputOutside ⟨i.val+4,by have := i.isLt; omega⟩
    simpa [Signing.wordAddress,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem keygen_code : Code keygen 0x1204 := by decide

/-- info: 'SigGolfCandidate.Hypertree.KeygenSecret.compute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compute

end SigGolfCandidate.Hypertree.KeygenSecret
