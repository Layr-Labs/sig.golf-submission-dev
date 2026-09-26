import SigGolfCandidate.Hypertree.KeygenTreeHelpers
import SigGolfCandidate.Hypertree.KeygenResourceInitial

/-! Inlined from SigGolfCandidate.Hypertree.KeygenTreeExecution; its only importer was SigGolfCandidate.Hypertree.KeygenFunctionalInitial. -/
section
namespace SigGolfCandidate.Hypertree.KeygenTree
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen KeygenSecretStart
set_option maxRecDepth 4096

/-- The exact generated keygen tree call refines the reference root for every hash and secret key. -/
theorem execute_framed (hash : Hash) (s : MachineState) (pc : s.pc=0x1048)
    (sp : s.getReg .x2=0x1000000) (level tree : Nat) (secretKey : SecretKey)
    (nonzero : BitVec.ofNat 64 level ≠ 0) (context : Context level tree false secretKey s) :
    ∃ final, Trace hash keygen s 77073 82422 739 761 final ∧
      final.pc=s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2=s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress 0x80500 i.val) =
        (Reference.treeRoot hash secretKey level tree).extractLsb' (64*i.val) 64) ∧
      (∀ a, a.toNat < 0x80000 → final.getMem a=s.getMem a) := by
  obtain ⟨ready,pre,rpc,rra,rsp,saved,rctx,preFrame⟩ := start_framed s pc sp level tree secretKey context
  obtain ⟨left,leftTrace,leftPC,leftSP,leftWords,leftFrame⟩ :=
    KeygenLeafCall.execute hash ready rpc rsp level tree false secretKey nonzero rctx
  have leftRet : left.pc=0x1064 := by rw [leftPC,rra]; decide
  have leftStack : left.getReg .x2=0xfffff0 := leftSP.trans rsp
  have leftCtx := context_after_leaf ready left level tree false secretKey rctx leftFrame
  let rightReady := KeygenTreeControl.state left 1 344
  have rightPre := KeygenTreeControl.block keygen 0x1064 1 344 KeygenTreeControl.right_code left leftRet
  have rrpc : rightReady.pc=0x11cc := by rw [KeygenTreeControl.pc,leftRet]; rfl
  have rrsp : rightReady.getReg .x2=0xfffff0 := (KeygenTreeControl.sp left 1 344).trans leftStack
  have rrra : rightReady.getReg .x1=0x1078 := by rw [KeygenTreeControl.ra,leftRet]; rfl
  have rrctx := control_context left false true 344 level tree secretKey leftCtx
  obtain ⟨right,rightTrace,rightPC,rightSP,rightWords,rightFrame⟩ :=
    KeygenLeafCall.execute hash rightReady rrpc rrsp level tree true secretKey nonzero rrctx
  have rightRet : right.pc=0x1078 := by rw [rightPC,rrra]; decide
  have rightStack : right.getReg .x2=0xfffff0 := rightSP.trans rrsp
  have rightCtx := context_after_leaf rightReady right level tree true secretKey rrctx rightFrame
  obtain ⟨nodeReady,skip,nodePC,nodeMem,nodeSP⟩ :=
    Signing.capture_disabled keygen 0x1078 92 skip_code right rightRet rightCtx.modeWord
  have npc : nodeReady.pc=0x10e0 := nodePC
  have nsp : nodeReady.getReg .x2=0xfffff0 := nodeSP.trans rightStack
  have levelEq : nodeReady.getMem 0x80400=BitVec.ofNat 64 level := by rw [nodeMem]; exact rightCtx.levelWord
  have indexEq : ∀ i : Fin 3, nodeReady.getMem (Signing.wordAddress 0x80408 i.val)=
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by intro i; rw [nodeMem]; exact rightCtx.indexWords i
  have leftPair : ∀ i : Fin 2, nodeReady.getMem (KeygenSavePublic.wordAddress false i.val)=
      (Reference.leafRoot hash secretKey level tree false).extractLsb' (64*i.val) 64 := by
    intro i
    rw [nodeMem,rightFrame _ (by fin_cases i <;> decide),KeygenTreeControl.mem,
      if_neg (by fin_cases i <;> decide)]
    exact leftWords i
  have rightPair : ∀ i : Fin 2, nodeReady.getMem (KeygenSavePublic.wordAddress true i.val)=
      (Reference.leafRoot hash secretKey level tree true).extractLsb' (64*i.val) 64 := by
    intro i; rw [nodeMem]; exact rightWords i
  have children : ∀ i : Fin 4, nodeReady.getMem (Signing.wordAddress 0x80520 i.val)=
      if i.val<2 then (Reference.leafRoot hash secretKey level tree false).extractLsb' (64*i.val) 64
      else (Reference.leafRoot hash secretKey level tree true).extractLsb' (64*(i.val-2)) 64 := by
    intro i
    fin_cases i
    · exact leftPair 0
    · exact leftPair 1
    · exact rightPair 0
    · exact rightPair 1
  have nsaved : nodeReady.getMem 0xfffff0=s.getReg .x1 := by
    rw [nodeMem,rightFrame _ (by decide),KeygenTreeControl.mem,if_neg (by decide),
      leftFrame _ (by decide),saved]
  obtain ⟨final,tail,fpc,fsp,words,frame⟩ :=
    KeygenNode.compute_return keygen hash 0x10e0 KeygenNode.keygen_body_code keygen_tree_return nodeReady npc
      level tree (Reference.leafRoot hash secretKey level tree false) (Reference.leafRoot hash secretKey level tree true)
      levelEq indexEq children (by rw [nsp]; decide) (by rw [nsp]; decide) (by rw [nsp]; decide) (by rw [nsp]; decide)
  refine ⟨final,pre.trace.trans (leftTrace.trans (rightPre.trace.trans (rightTrace.trans (skip.trace.trans tail)))),?_,?_,words,?_⟩
  · rw [fpc,nsp,nsaved]
  · rw [fsp,nsp,sp]; rfl

  · intro a low
    have hl : a ≠ 0x80428 := by intro eq; rw [eq] at low; change 0x80428 < 0x80000 at low; omega
    rw [frame a (low_ne_word a low _ _ (by decide) (by decide))
      (low_ne_word a low _ _ (by decide) (by decide)) (low_ne_word a low _ _ (by decide) (by decide)),
      nodeMem,rightFrame a (low_outside_leaf true a low),KeygenTreeControl.mem,if_neg hl,
      leftFrame a (low_outside_leaf false a low),preFrame a low]

theorem execute (hash : Hash) (s : MachineState) (pc : s.pc=0x1048)
    (sp : s.getReg .x2=0x1000000) (level tree : Nat) (secretKey : SecretKey)
    (nonzero : BitVec.ofNat 64 level ≠ 0) (context : Context level tree false secretKey s) :
    ∃ final, Trace hash keygen s 77073 82422 739 761 final ∧
      final.pc=s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2=s.getReg .x2 ∧
      ∀ i : Fin 2, final.getMem (Signing.wordAddress 0x80500 i.val) =
        (Reference.treeRoot hash secretKey level tree).extractLsb' (64*i.val) 64 := by
  obtain ⟨final,run,fpc,fsp,words,frame⟩ := execute_framed hash s pc sp level tree secretKey nonzero context
  exact ⟨final,run,fpc,fsp,words⟩

/-- info: 'SigGolfCandidate.Hypertree.KeygenTree.execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms execute

end SigGolfCandidate.Hypertree.KeygenTree

end

namespace SigGolfCandidate.Hypertree.KeygenFunctional
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen KeygenResource KeygenSecretStart
set_option maxRecDepth 4096

theorem secretKey_byte (secretKey : SecretKey) (i : Nat) (hi : i<32) :
    (secretKeyState secretKey).getByte (BitVec.ofNat 64 (0x20+i))=secretKey.extractLsb' (8*i) 8 := by
  simp only [secretKeyState,Memory.getByte_setReg]
  exact Memory.write_value_byte _ 0x20 32 secretKey i (by decide) (by decide) hi

theorem secretKey_word (secretKey : SecretKey) (i : Fin 4) :
    (secretKeyState secretKey).getMem (Signing.wordAddress 0x20 i.val)=secretKey.extractLsb' (64*i.val) 64 := by
  apply eq_of_forall_extractByte
  intro j hj
  have hi := i.isLt
  have whole : 8*i.val+j<32 := by omega
  have quot : (8*i.val+j)/8=i.val := by omega
  have rem : (8*i.val+j)%8=j := by omega
  have h := secretKey_byte secretKey (8*i.val+j) whole
  rw [Signing.getByte_word _ 0x20 (8*i.val+j) (by decide) (by omega)] at h
  simp only [quot,rem] at h
  rw [h]
  symm
  simpa only [quot,rem] using KeygenNode.extractByte_slice secretKey (8*i.val+j)

theorem secretKey_zero (secretKey : SecretKey) (a : Word) (outside : 0x40≤a.toNat) :
    (secretKeyState secretKey).getMem a=0 := by
  simp only [secretKeyState,MachineState.getMem_setReg]
  rw [Memory.write_preserves _ 0x20 (bytes secretKey) a (by simp [bytes]) (by right; simpa [bytes] using outside)]
  rfl

theorem secretKey_pc (secretKey : SecretKey) : (secretKeyState secretKey).pc=0x1000 := by
  simp only [secretKeyState,MachineState.pc_setReg,MachineState.pc_writeBytesAsWords]
  rfl

theorem secretKey_sp (secretKey : SecretKey) : (secretKeyState secretKey).getReg .x2=0x1000000 := by
  simp only [secretKeyState,MachineState.getReg_setReg_eq (by decide : Reg.x2≠Reg.x0)]
  rfl

theorem prefix_context (secretKey : SecretKey) :
    Context 159 0 false secretKey (prefixState (secretKeyState secretKey)) := by
  constructor
  · rw [prefix_mem,if_pos rfl]; rfl
  · rw [prefix_mem,if_neg (by decide),secretKey_zero _ _ (by decide)]; rfl
  · intro i
    rw [prefix_mem,if_neg (by fin_cases i <;> decide),secretKey_zero _ _ (by fin_cases i <;> decide)]
    fin_cases i <;> rfl
  · intro i
    rw [prefix_mem,if_neg (by fin_cases i <;> decide)]
    exact secretKey_word secretKey i
  · rw [prefix_mem,if_neg (by decide),secretKey_zero _ _ (by decide)]

end SigGolfCandidate.Hypertree.KeygenFunctional
