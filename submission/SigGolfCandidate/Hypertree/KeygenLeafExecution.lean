import SigGolfCandidate.Hypertree.KeygenCopyFrame
import SigGolfCandidate.Hypertree.KeygenLeafHeader
import SigGolfCandidate.Hypertree.KeygenSavePublic
import SigGolfCandidate.Hypertree.KeygenControl

/-! Inlined from SigGolfCandidate.Hypertree.KeygenEndpointCopy; its only importer was SigGolfCandidate.Hypertree.KeygenLeafExecution. -/
section
namespace SigGolfCandidate.Hypertree.KeygenEndpointCopy
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen

/-- Common five-instruction setup for copies between scratch buffers. -/
def CopySetupCode (image : Image) (p : Word) (source destination count : BitVec 12) : Prop :=
  instructionAt image p = some (.base (.LUI .x6 129)) ∧
  instructionAt image (p + 4) = some (.base (.ADDI .x6 .x6 source)) ∧
  instructionAt image (p + 8) = some (.base (.LUI .x7 128)) ∧
  instructionAt image (p + 12) = some (.base (.ADDI .x7 .x7 destination)) ∧
  instructionAt image (p + 16) = some (.base (.ADDI .x10 .x0 count))

instance (image : Image) (p : Word) (source destination count : BitVec 12) :
    Decidable (CopySetupCode image p source destination count) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def copySetup (s : MachineState) (source destination count : BitVec 12) : MachineState :=
  let s := execInstrBr s (.LUI .x6 129)
  let s := execInstrBr s (.ADDI .x6 .x6 source)
  let s := execInstrBr s (.LUI .x7 128)
  let s := execInstrBr s (.ADDI .x7 .x7 destination)
  execInstrBr s (.ADDI .x10 .x0 count)

theorem copy_setup_block (image : Image) (p : Word) (source destination count : BitVec 12)
    (code : CopySetupCode image p source destination count) (s : MachineState) (pc : s.pc = p) :
    OrdinarySteps image s 5 (copySetup s source destination count) := by
  obtain ⟨c0,c1,c2,c3,c4⟩ := code
  let s1 := execInstrBr s (.LUI .x6 129)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 source)
  let s3 := execInstrBr s2 (.LUI .x7 128)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 destination)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 129)) 4
  · simpa only [fetch_at, pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 source)) 3
  · simpa only [fetch_at, s1, execInstrBr, MachineState.setPC, pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 128)) 2
  · have hp : s2.pc = p + 8 := by simp [s1,s2,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 destination)) 1
  · have hp : s3.pc = p + 12 := by simp [s1,s2,s3,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 (copySetup s source destination count) _ (.base (.ADDI .x10 .x0 count)) 0
  · have hp : s4.pc = p + 16 := by simp [s1,s2,s3,s4,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem copy_setup_pc (s : MachineState) (source destination count : BitVec 12) :
    (copySetup s source destination count).pc = s.pc + 20 := by
  simp [copySetup,execInstrBr,BitVec.add_assoc]

theorem copy_setup_regs (s : MachineState) (source destination count : BitVec 12) :
    (copySetup s source destination count).getReg .x6 = 0x81000 + signExtend12 source ∧
    (copySetup s source destination count).getReg .x7 = 0x80000 + signExtend12 destination ∧
    (copySetup s source destination count).getReg .x10 = signExtend12 count := by
  simp [copySetup,execInstrBr,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem copy_setup_mem (s : MachineState) (source destination count : BitVec 12) (a : Word) :
    (copySetup s source destination count).getMem a = s.getMem a := by
  simp [copySetup,execInstrBr]

theorem copy_setup_stack (s : MachineState) (source destination count : BitVec 12) :
    (copySetup s source destination count).getReg .x1 = s.getReg .x1 ∧
    (copySetup s source destination count).getReg .x2 = s.getReg .x2 := by
  simp [copySetup,execInstrBr,MachineState.getReg_setReg_ne]

/-- The 92 endpoint words are copied into the complete leaf HASH payload. -/
theorem copy (image : Image) (p : Word)
    (setupCode : CopySetupCode image p 2048 32 92) (copyCode : CopyCode image (p+20))
    (s : MachineState) (pc : s.pc = p) :
    ∃ final, OrdinarySteps image s 557 final ∧ final.pc = p+44 ∧
      (∀ i : Fin 92, final.getMem (Signing.wordAddress 0x80020 i.val) =
        s.getMem (Signing.wordAddress 0x80800 i.val)) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 92, a ≠ Signing.wordAddress 0x80020 i.val) → final.getMem a = s.getMem a) := by
  let prepared := copySetup s 2048 32 92
  have pre := copy_setup_block image p 2048 32 92 setupCode s pc
  have inv : CopyInvariant (p+20) 0x80800 0x80020 92 92 prepared := by
    have regs := copy_setup_regs s 2048 32 92
    simp only [CopyInvariant,prepared,copy_setup_pc,pc,regs.1,regs.2.1,regs.2.2]
    simp [signExtend12]
  obtain ⟨final,trace,done,content,frame,ra,sp⟩ :=
    copy_all_frame image (p+20) copyCode 0x80800 0x80020 92 prepared inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final,ordinary_trans image _ _ _ 5 552 pre trace,?_,?_,
    ra.trans (copy_setup_stack s _ _ _).1,sp.trans (copy_setup_stack s _ _ _).2,?_⟩
  · simpa [BitVec.add_assoc] using done.2.2.1
  · intro i
    rw [content i.val i.isLt]
    exact copy_setup_mem s _ _ _ _
  · intro a outside
    rw [frame a (fun i hi => outside ⟨i,hi⟩)]
    exact copy_setup_mem s _ _ _ _

theorem keygen_setup_code : CopySetupCode keygen 0x1548 2048 32 92 := by decide

theorem keygen_copy_code : CopyCode keygen 0x155c := by decide

end SigGolfCandidate.Hypertree.KeygenEndpointCopy

end

namespace SigGolfCandidate.Hypertree.KeygenLeaf
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def Code (image : Image) (p : Word) : Prop :=
  KeygenEndpointCopy.CopySetupCode image p 2048 32 92 ∧ CopyCode image (p+20) ∧
  KeygenLeafHeader.Code image (p+44) ∧ instructionAt image (p+200) = some (.base .ECALL) ∧
  KeygenSavePublic.Code image (p+204)

instance (image : Image) (p : Word) : Decidable (Code image p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The full leaf-compression suffix writes the reference root into its selected public slot. -/
theorem compute (image : Image) (hash : Hash) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) (level tree : Nat) (side : Bool)
    (values : Reference.Chain → Reference.Digest)
    (hlevel : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (hleaf : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side))
    (hindex : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (hvalues : ∀ i : Fin 92, s.getMem (Signing.wordAddress 0x80800 i.val) =
      KeygenLeafHeader.endpointWord values i) :
    ∃ final, Trace hash image s 612 707 1 12 final ∧ final.pc = p+264 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.compressLeaf hash level tree side values).extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 96, a ≠ Signing.wordAddress 0x80000 i.val) →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) →
        (∀ i : Fin 2, a ≠ KeygenSavePublic.wordAddress side i.val) →
        final.getMem a = s.getMem a) := by
  obtain ⟨copied,pre,cpc,content,cra,csp,cframe⟩ :=
    KeygenEndpointCopy.copy image p code.1 code.2.1 s pc
  have levelEq : copied.getMem 0x80400 = BitVec.ofNat 64 level := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact hlevel
  have leafEq : copied.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side) := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact hleaf
  have indexEq : ∀ i : Fin 3, copied.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    rw [cframe _ (by intro j; fin_cases i <;> fin_cases j <;> decide)]
    exact hindex i
  have valuesEq : ∀ i : Fin 92, copied.getMem (Signing.wordAddress 0x80020 i.val) =
      KeygenLeafHeader.endpointWord values i := by intro i; rw [content i]; exact hvalues i
  let ready := KeygenLeafHeader.state copied
  have headTrace := KeygenLeafHeader.block image (p+44) code.2.2.1 copied cpc
  have hpc : ready.pc = p+200 := by
    simp only [ready,KeygenLeafHeader.pc,cpc]; simp [BitVec.add_assoc]
  obtain ⟨service,source,bits,destination⟩ := KeygenLeafHeader.regs copied
  have words := KeygenLeafHeader.words copied level tree (Reference.sideNumber side) values levelEq leafEq indexEq valuesEq
  have hf : fetch image ready = some (.base .ECALL) := by simpa only [fetch_at,hpc] using code.2.2.2.1
  let hashed := writeHash ready (hash (hashInput ready))
  have hashTrace := hash_trace image hash ready hf service source bits destination
  have hashPC : hashed.pc = p+204 := by simp only [hashed,hash_pc,hpc]; simp [BitVec.add_assoc]
  have hashLeaf : hashed.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side) := by
    rw [Signing.hash_answer_frame ready _ destination _ (by intro i; fin_cases i <;> decide),
      KeygenLeafHeader.frame copied _ (by intro i; fin_cases i <;> decide)]
    exact leafEq
  have safe := KeygenSavePublic.safe hashed side hashLeaf
  have post := KeygenSavePublic.block image (p+204) code.2.2.2.2 hashed hashPC safe.1 safe.2
  refine ⟨KeygenSavePublic.state hashed,pre.trace.trans (headTrace.trace.trans (hashTrace.trans post.trace)),?_,?_,?_,?_,?_⟩
  · rw [KeygenSavePublic.pc,hashPC]; simp [BitVec.add_assoc]
  · intro i
    rw [KeygenSavePublic.content hashed side hashLeaf i]
    exact answer_words hash ready level tree side values source bits destination words i
  · exact (KeygenSavePublic.stack hashed).1.trans ((hash_registers _ _ _).trans ((KeygenLeafHeader.stack copied).1.trans cra))
  · exact (KeygenSavePublic.stack hashed).2.trans ((hash_registers _ _ _).trans ((KeygenLeafHeader.stack copied).2.trans csp))
  · intro a inputOutside answerOutside publicOutside
    rw [KeygenSavePublic.frame hashed side hashLeaf a publicOutside,
      Signing.hash_answer_frame ready _ destination a answerOutside,
      KeygenLeafHeader.frame copied a (fun i => inputOutside ⟨i.val,by have := i.isLt; omega⟩)]
    apply cframe
    intro i
    have outside := inputOutside ⟨i.val+4,by have := i.isLt; omega⟩
    simpa [Signing.wordAddress,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using outside

theorem keygen_code : Code keygen 0x1548 := by decide

/-- The leaf-compression suffix including the protected return through the saved stack word. -/
theorem compute_return (image : Image) (hash : Hash) (p : Word) (code : Code image p)
    (returnCode : ReturnCode image (p+264))
    (s : MachineState) (pc : s.pc=p) (level tree : Nat) (side : Bool)
    (values : Reference.Chain → Reference.Digest)
    (hlevel : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (hleaf : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side))
    (hindex : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (hvalues : ∀ i : Fin 92, s.getMem (Signing.wordAddress 0x80800 i.val) =
      KeygenLeafHeader.endpointWord values i)
    (stack : accessValid (s.getReg .x2) 8 = true)
    (stackInput : ∀ i : Fin 96, s.getReg .x2 ≠ Signing.wordAddress 0x80000 i.val)
    (stackAnswer : ∀ i : Fin 4, s.getReg .x2 ≠ Signing.wordAddress 0x80300 i.val)
    (stackPublic : ∀ i : Fin 2, s.getReg .x2 ≠ KeygenSavePublic.wordAddress side i.val) :
    ∃ final, Trace hash image s 615 710 1 12 final ∧
      final.pc = s.getMem (s.getReg .x2) &&& ~~~1#64 ∧ final.getReg .x2=s.getReg .x2+16 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.compressLeaf hash level tree side values).extractLsb' (64*i.val) 64) ∧
      (∀ a, (∀ i : Fin 96, a ≠ Signing.wordAddress 0x80000 i.val) →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) →
        (∀ i : Fin 2, a ≠ KeygenSavePublic.wordAddress side i.val) → final.getMem a=s.getMem a) := by
  obtain ⟨body,trace,bpc,content,ra,sp,frame⟩ := compute image hash p code s pc level tree side values hlevel hleaf hindex hvalues
  have ret := return_block image (p+264) returnCode body bpc (by rw [sp]; exact stack)
  refine ⟨returnState body,trace.trans ret.trace,?_,?_,?_,?_⟩
  · rw [return_pc,sp,frame _ stackInput stackAnswer stackPublic]
  · rw [return_sp,sp]
  · intro i; rw [return_mem]; exact content i
  · intro a hi ha hp; rw [return_mem]; exact frame a hi ha hp

/-- info: 'SigGolfCandidate.Hypertree.KeygenLeaf.compute_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compute_return

end SigGolfCandidate.Hypertree.KeygenLeaf
