import SigGolfCandidate.Hypertree.VerifyLeafHeaderDirect
import SigGolfCandidate.Hypertree.VerifyLeafQueryDirect
import SigGolfCandidate.Hypertree.KeygenSavePublic
import SigGolfCandidate.Hypertree.KeygenControl

namespace SigGolfCandidate.Hypertree.VerifyLeafDirect
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen Signing
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- A jump bypasses the old endpoint copy; the header directly precedes the endpoint array. -/
def Code (image : Image) (p : Word) : Prop :=
  instructionAt image p = some (.base (.JAL .x0 44)) ∧
  VerifyLeafHeaderDirect.Code image (p+44) ∧
  instructionAt image (p+200) = some (.base .ECALL) ∧
  KeygenSavePublic.Code image (p+204)

instance (image : Image) (p : Word) : Decidable (Code image p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem verify_code : Code verify 0x1690 := by decide

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

theorem compute (image : Image) (hash : Hash) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) (level tree : Nat) (side : Bool)
    (values : Reference.Chain → Reference.Digest)
    (hlevel : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (hleaf : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side))
    (hindex : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (hvalues : ∀ i : Fin 92, s.getMem (Signing.wordAddress 0x80800 i.val) =
      VerifyLeafHeaderDirect.endpointWord values i) :
    ∃ final, Trace hash image s 56 151 1 12 final ∧ final.pc = p+264 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.compressLeaf hash level tree side values).extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 4, a ≠ Signing.wordAddress 0x807e0 i.val) →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) →
        (∀ i : Fin 2, a ≠ KeygenSavePublic.wordAddress side i.val) →
        final.getMem a = s.getMem a) := by
  let skipped := jumped s
  have pre := jump_block image p code.1 s pc
  have spc : skipped.pc = p+44 := by simp only [skipped, jump_pc, pc]
  have levelEq : skipped.getMem 0x80400 = BitVec.ofNat 64 level := by rw [jump_mem]; exact hlevel
  have leafEq : skipped.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side) := by
    rw [jump_mem]; exact hleaf
  have indexEq : ∀ i : Fin 3, skipped.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by intro i; rw [jump_mem]; exact hindex i
  have valuesEq : ∀ i : Fin 92, skipped.getMem (Signing.wordAddress 0x80800 i.val) =
      VerifyLeafHeaderDirect.endpointWord values i := by intro i; rw [jump_mem]; exact hvalues i
  let ready := VerifyLeafHeaderDirect.state skipped
  have headTrace := VerifyLeafHeaderDirect.block image (p+44) code.2.1 skipped spc
  have hpc : ready.pc = p+200 := by
    simp only [ready,VerifyLeafHeaderDirect.pc,spc]; simp [BitVec.add_assoc]
  obtain ⟨service,source,bits,destination⟩ := VerifyLeafHeaderDirect.regs skipped
  have words := VerifyLeafHeaderDirect.words skipped level tree (Reference.sideNumber side) values
    levelEq leafEq indexEq valuesEq
  have hf : fetch image ready = some (.base .ECALL) := by
    simpa only [fetch_at,hpc] using code.2.2.1
  let hashed := writeHash ready (hash (hashInput ready))
  have hashTrace := VerifyLeafQueryDirect.hash_trace image hash ready hf service source bits destination
  have hashPC : hashed.pc = p+204 := by simp only [hashed,hash_pc,hpc]; simp [BitVec.add_assoc]
  have hashLeaf : hashed.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side) := by
    rw [Signing.hash_answer_frame ready _ destination _ (by intro i; fin_cases i <;> decide),
      VerifyLeafHeaderDirect.frame skipped _ (by intro i; fin_cases i <;> decide)]
    exact leafEq
  have safe := KeygenSavePublic.safe hashed side hashLeaf
  have post := KeygenSavePublic.block image (p+204) code.2.2.2 hashed hashPC safe.1 safe.2
  refine ⟨KeygenSavePublic.state hashed,pre.trace.trans (headTrace.trace.trans (hashTrace.trans post.trace)),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [KeygenSavePublic.pc,hashPC]; simp [BitVec.add_assoc]
  · intro i
    rw [KeygenSavePublic.content hashed side hashLeaf i]
    exact VerifyLeafQueryDirect.answer_words hash ready level tree side values source bits destination words i
  · exact (KeygenSavePublic.stack hashed).1.trans ((hash_registers _ _ _).trans
      ((VerifyLeafHeaderDirect.stack skipped).1.trans (jump_stack s).1))
  · exact (KeygenSavePublic.stack hashed).2.trans ((hash_registers _ _ _).trans
      ((VerifyLeafHeaderDirect.stack skipped).2.trans (jump_stack s).2))
  · intro a headerOutside answerOutside publicOutside
    rw [KeygenSavePublic.frame hashed side hashLeaf a publicOutside,
      Signing.hash_answer_frame ready _ destination a answerOutside,
      VerifyLeafHeaderDirect.frame skipped a headerOutside,
      jump_mem]

theorem compute_return (image : Image) (hash : Hash) (p : Word) (code : Code image p)
    (returnCode : ReturnCode image (p+264))
    (s : MachineState) (pc : s.pc=p) (level tree : Nat) (side : Bool)
    (values : Reference.Chain → Reference.Digest)
    (hlevel : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (hleaf : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side))
    (hindex : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (hvalues : ∀ i : Fin 92, s.getMem (Signing.wordAddress 0x80800 i.val) =
      VerifyLeafHeaderDirect.endpointWord values i)
    (stack : accessValid (s.getReg .x2) 8 = true)
    (stackInput : ∀ i : Fin 4, s.getReg .x2 ≠ Signing.wordAddress 0x807e0 i.val)
    (stackAnswer : ∀ i : Fin 4, s.getReg .x2 ≠ Signing.wordAddress 0x80300 i.val)
    (stackPublic : ∀ i : Fin 2, s.getReg .x2 ≠ KeygenSavePublic.wordAddress side i.val) :
    ∃ final, Trace hash image s 59 154 1 12 final ∧
      final.pc = s.getMem (s.getReg .x2) &&& ~~~1#64 ∧ final.getReg .x2=s.getReg .x2+16 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.compressLeaf hash level tree side values).extractLsb' (64*i.val) 64) ∧
      (∀ a, (∀ i : Fin 4, a ≠ Signing.wordAddress 0x807e0 i.val) →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) →
        (∀ i : Fin 2, a ≠ KeygenSavePublic.wordAddress side i.val) → final.getMem a=s.getMem a) := by
  obtain ⟨body,trace,bpc,content,ra,sp,frame⟩ := compute image hash p code s pc level tree side values
    hlevel hleaf hindex hvalues
  have ret := return_block image (p+264) returnCode body bpc (by rw [sp]; exact stack)
  refine ⟨returnState body,trace.trans ret.trace,?_,?_,?_,?_⟩
  · rw [return_pc,sp,frame _ stackInput stackAnswer stackPublic]
  · rw [return_sp,sp]
  · intro i; rw [return_mem]; exact content i
  · intro a hi ha hp; rw [return_mem]; exact frame a hi ha hp

/-- info: 'SigGolfCandidate.Hypertree.VerifyLeafDirect.compute_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compute_return

end SigGolfCandidate.Hypertree.VerifyLeafDirect
