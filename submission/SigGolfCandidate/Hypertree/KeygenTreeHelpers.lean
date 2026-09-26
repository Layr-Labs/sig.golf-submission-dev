import SigGolfCandidate.Hypertree.KeygenLeafLoop
import SigGolfCandidate.Hypertree.KeygenLeafEntry
import SigGolfCandidate.Hypertree.KeygenTreeControl
import SigGolfCandidate.Hypertree.KeygenNodeExecution
import SigGolfCandidate.Hypertree.SignCapture

/-! Inlined from SigGolfCandidate.Hypertree.KeygenLeafPrologue; its only importer was SigGolfCandidate.Hypertree.KeygenTreeHelpers. -/
section
namespace SigGolfCandidate.Hypertree.KeygenLeafPrologue
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen KeygenSecretStart
set_option maxRecDepth 4096

def ready (s : MachineState) := KeygenLeafEntry.state (enterState s) 1116

theorem frame (s : MachineState) (sp : s.getReg .x2=0xfffff0)
    (a : Word) (hs : a≠0xffffe0) (hc : a≠0x80430) (ht : a≠0x80438) :
    (ready s).getMem a=s.getMem a  := by
  unfold ready
  rw [KeygenLeafEntry.mem,if_neg ht,if_neg hc,enter_mem,sp]
  exact if_neg hs


theorem stack (s : MachineState) (sp : s.getReg .x2=0xfffff0) :
    (ready s).getReg .x2=0xffffe0  := by
  unfold ready
  rw [(KeygenLeafEntry.stack _ _).2,enter_sp,sp]; rfl


theorem saved (s : MachineState) (sp : s.getReg .x2=0xfffff0) :
    (ready s).getMem 0xffffe0=s.getReg .x1  := by
  unfold ready
  rw [KeygenLeafEntry.mem,if_neg (by decide),if_neg (by decide),enter_mem,sp,if_pos (by decide)]


theorem pc (s : MachineState) (pc : s.pc=0x11cc) (sp : s.getReg .x2=0xfffff0)
    (level : Nat) (nonzero : BitVec.ofNat 64 level ≠ 0) (hl : s.getMem 0x80400=BitVec.ofNat 64 level) :
    (ready s).pc=0x1204 := by
  have levelEq : (enterState s).getMem 0x80400=BitVec.ofNat 64 level := by
    rw [enter_mem,sp,if_neg (by decide)]
    exact hl
  unfold ready
  rw [KeygenLeafEntry.pc,levelEq,if_neg nonzero,enter_pc,pc]; rfl


theorem context (s : MachineState) (sp : s.getReg .x2=0xfffff0)
    (level tree : Nat) (side : Bool) (secretKey : SecretKey) (context : Context level tree side secretKey s) :
    Context level tree side secretKey (ready s) := by
  constructor
  · rw [frame _ sp _ (by decide) (by decide) (by decide)]; exact context.levelWord
  · rw [frame _ sp _ (by decide) (by decide) (by decide)]; exact context.leafWord
  · intro i
    rw [frame _ sp _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact context.indexWords i
  · intro i
    rw [frame _ sp _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact context.secretKeyWords i
  · rw [frame _ sp _ (by decide) (by decide) (by decide)]; exact context.modeWord

theorem counter (s : MachineState) : (ready s).getMem 0x80430=0 := by
  unfold ready
  rw [KeygenLeafEntry.mem,if_neg (by decide),if_pos rfl]

theorem block (s : MachineState) (pc : s.pc=0x11cc) (sp : s.getReg .x2=0xfffff0) :
    OrdinarySteps keygen s 14 (ready s) := by
  have entered := enter_block keygen 0x11cc keygen_leaf_enter s pc (by rw [sp]; decide)
  have epc : (enterState s).pc=0x11d4 := by rw [enter_pc,pc]; rfl
  have entry := KeygenLeafEntry.block keygen 0x11d4 1116 KeygenLeafEntry.keygen_code (enterState s) epc
  exact ordinary_trans keygen _ _ _ 2 12 entered entry

theorem prepare (s : MachineState) (atPC : s.pc=0x11cc) (sp : s.getReg .x2=0xfffff0)
    (level tree : Nat) (side : Bool) (secretKey : SecretKey)
    (nonzero : BitVec.ofNat 64 level ≠ 0) (ctx : Context level tree side secretKey s) :
    ∃ final, OrdinarySteps keygen s 14 final ∧ final.pc=0x1204 ∧
      Context level tree side secretKey final ∧ final.getMem 0x80430=0 ∧
      final.getReg .x2=0xffffe0 ∧ final.getMem 0xffffe0=s.getReg .x1 ∧
      (∀ a, a≠0xffffe0 → a≠0x80430 → a≠0x80438 → final.getMem a=s.getMem a) := by
  exact ⟨ready s,block s atPC sp,pc s atPC sp level nonzero ctx.levelWord,
    context s sp level tree side secretKey ctx,counter s,stack s sp,saved s sp,frame s sp⟩

end SigGolfCandidate.Hypertree.KeygenLeafPrologue
end

namespace SigGolfCandidate.Hypertree.KeygenLeafCall
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen KeygenSecretStart
set_option maxRecDepth 4096

def Outside (side : Bool) (a : Word) : Prop :=
  a ≠ 0xffffe0 ∧ KeygenLeafLoop.Outside a ∧
    (∀ i : Fin 96, a ≠ Signing.wordAddress 0x80000 i.val) ∧
    ∀ i : Fin 2, a ≠ KeygenSavePublic.wordAddress side i.val

instance (side : Bool) (a : Word) : Decidable (Outside side a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- A complete upper-leaf call, with the exact generated keygen entry and return. -/
theorem execute (hash : Hash) (s : MachineState) (pc : s.pc=0x11cc)
    (sp : s.getReg .x2=0xfffff0) (level tree : Nat) (side : Bool) (secretKey : SecretKey)
    (nonzero : BitVec.ofNat 64 level ≠ 0) (context : Context level tree side secretKey s) :
    ∃ final, Trace hash keygen s 38487 41158 369 380 final ∧
      final.pc=s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2=s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.leafRoot hash secretKey level tree side).extractLsb' (64*i.val) 64) ∧
      (∀ a, Outside side a → final.getMem a=s.getMem a) := by
  obtain ⟨ready,pre,rpc,rcontext,rchain,rsp,saved,entryFrame⟩ :=
    KeygenLeafPrologue.prepare s pc sp level tree side secretKey nonzero context
  obtain ⟨ended,rounds,endPC,endContext,endCounter,endpoints,endRA,endSP,endFrame⟩ :=
    KeygenLeafLoop.loop hash 46 ready 0 level tree side secretKey (by decide) rpc rcontext rchain
      (by intro chain lt; omega)
  have esp : ended.getReg .x2=0xffffe0 := endSP.trans rsp
  have esaved : ended.getMem 0xffffe0=s.getReg .x1 := by
    rw [endFrame _ (by decide),saved]
  obtain ⟨final,tail,fpc,fsp,words,frame⟩ :=
    KeygenLeaf.compute_return keygen hash 0x1548 KeygenLeaf.keygen_code keygen_leaf_return ended endPC
      level tree side (Reference.endpoint hash secretKey level tree side)
      endContext.levelWord endContext.leafWord endContext.indexWords
      (KeygenLeafLoop.endpoint_words hash secretKey level tree side ended endpoints)
      (by rw [esp]; decide)
      (by rw [esp]; decide)
      (by rw [esp]; decide)
      (by rw [esp]; cases side <;> decide)
  refine ⟨final,pre.trace.trans (rounds.trans tail),?_,?_,?_,?_⟩
  · rw [fpc,esp,esaved]
  · rw [fsp,esp,sp]; rfl
  · intro i
    have nz : level≠0 := by intro eq; apply nonzero; rw [eq]; rfl
    simpa only [Reference.leafRoot,if_neg nz] using words i
  · intro a outside
    obtain ⟨hs,loopOutside,inputOutside,publicOutside⟩ := outside
    rw [frame a inputOutside loopOutside.2.1.2.2.1 publicOutside,endFrame a loopOutside,
      entryFrame a hs loopOutside.1 loopOutside.2.1.1]

/-- info: 'SigGolfCandidate.Hypertree.KeygenLeafCall.execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms execute

end SigGolfCandidate.Hypertree.KeygenLeafCall


namespace SigGolfCandidate.Hypertree.KeygenTree
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen KeygenSecretStart
set_option maxRecDepth 4096

theorem context_after_leaf (s t : MachineState) (level tree : Nat) (side : Bool) (secretKey : SecretKey)
    (ctx : Context level tree side secretKey s)
    (frame : ∀ a, KeygenLeafCall.Outside side a → t.getMem a=s.getMem a) :
    Context level tree side secretKey t := by
  constructor
  · rw [frame _ (by cases side <;> decide)]; exact ctx.levelWord
  · rw [frame _ (by cases side <;> decide)]; exact ctx.leafWord
  · intro i; rw [frame _ (by cases side <;> fin_cases i <;> decide)]; exact ctx.indexWords i
  · intro i; rw [frame _ (by cases side <;> fin_cases i <;> decide)]; exact ctx.secretKeyWords i
  · rw [frame _ (by cases side <;> decide)]; exact ctx.modeWord

theorem control_context (s : MachineState) (old side : Bool) (jump : BitVec 21)
    (level tree : Nat) (secretKey : SecretKey) (ctx : Context level tree old secretKey s) :
    Context level tree side secretKey (KeygenTreeControl.state s (BitVec.ofNat 12 (Reference.sideNumber side)) jump) := by
  constructor
  · rw [KeygenTreeControl.mem,if_neg (by decide)]; exact ctx.levelWord
  · rw [KeygenTreeControl.mem,if_pos rfl]; cases side <;> decide
  · intro i
    rw [KeygenTreeControl.mem,if_neg (by fin_cases i <;> decide)]
    exact ctx.indexWords i
  · intro i
    rw [KeygenTreeControl.mem,if_neg (by fin_cases i <;> decide)]
    exact ctx.secretKeyWords i
  · rw [KeygenTreeControl.mem,if_neg (by decide)]; exact ctx.modeWord

def entered (s : MachineState) : MachineState := enterState s

theorem entered_context (s : MachineState) (sp : s.getReg .x2=0x1000000)
    (level tree : Nat) (secretKey : SecretKey) (ctx : Context level tree false secretKey s) :
    Context level tree false secretKey (entered s) := by
  constructor
  · rw [entered,enter_mem,sp,if_neg (by decide)]; exact ctx.levelWord
  · rw [entered,enter_mem,sp,if_neg (by decide)]; exact ctx.leafWord
  · intro i
    rw [entered,enter_mem,sp,if_neg (by fin_cases i <;> decide)]
    exact ctx.indexWords i
  · intro i
    rw [entered,enter_mem,sp,if_neg (by fin_cases i <;> decide)]
    exact ctx.secretKeyWords i
  · rw [entered,enter_mem,sp,if_neg (by decide)]; exact ctx.modeWord

def leftState (s : MachineState) := KeygenTreeControl.state (entered s) 0 364

theorem left_block (s : MachineState) (pc : s.pc=0x1048) (sp : s.getReg .x2=0x1000000) :
    OrdinarySteps keygen s 7 (leftState s) := by
  have entry := enter_block keygen 0x1048 keygen_tree_enter s pc (by rw [sp]; decide)
  have epc : (entered s).pc=0x1050 := by rw [entered,enter_pc,pc]; rfl
  have setup := KeygenTreeControl.block keygen 0x1050 0 364 KeygenTreeControl.left_code (entered s) epc
  exact ordinary_trans keygen _ _ _ 2 5 entry setup

theorem left_pc (s : MachineState) (pc : s.pc=0x1048) : (leftState s).pc=0x11cc := by
  rw [leftState,KeygenTreeControl.pc,entered,enter_pc,pc]; rfl

theorem left_ra (s : MachineState) (pc : s.pc=0x1048) : (leftState s).getReg .x1=0x1064 := by
  rw [leftState,KeygenTreeControl.ra,entered,enter_pc,pc]; rfl

theorem left_sp (s : MachineState) (sp : s.getReg .x2=0x1000000) : (leftState s).getReg .x2=0xfffff0 := by
  rw [leftState,KeygenTreeControl.sp,entered,enter_sp,sp]; rfl

theorem left_saved (s : MachineState) (sp : s.getReg .x2=0x1000000) :
    (leftState s).getMem 0xfffff0=s.getReg .x1 := by
  rw [leftState,KeygenTreeControl.mem,if_neg (by decide),entered,enter_mem,sp,if_pos (by decide)]

theorem left_context (s : MachineState) (sp : s.getReg .x2=0x1000000)
    (level tree : Nat) (secretKey : SecretKey) (ctx : Context level tree false secretKey s) :
    Context level tree false secretKey (leftState s) :=
  control_context (entered s) false false 364 level tree secretKey (entered_context s sp level tree secretKey ctx)

theorem start (s : MachineState) (pc : s.pc=0x1048) (sp : s.getReg .x2=0x1000000)
    (level tree : Nat) (secretKey : SecretKey) (ctx : Context level tree false secretKey s) :
    ∃ ready, OrdinarySteps keygen s 7 ready ∧ ready.pc=0x11cc ∧ ready.getReg .x1=0x1064 ∧
      ready.getReg .x2=0xfffff0 ∧ ready.getMem 0xfffff0=s.getReg .x1 ∧ Context level tree false secretKey ready := by
  exact ⟨leftState s,left_block s pc sp,left_pc s pc,left_ra s pc,left_sp s sp,left_saved s sp,left_context s sp level tree secretKey ctx⟩

theorem skip_code : Signing.captureModeCode keygen 0x1078 92 := by
  intro s i pc
  simp only [fetch,pc]
  fin_cases i <;> decide

theorem low_ne_word (a : Word) (low : a.toNat < 0x80000)
    (base n : Nat) (lower : 0x80000 ≤ base) (upper : base+8*n < 2^64) (i : Fin n) :
    a ≠ Signing.wordAddress base i.val := by
  intro eq
  have h := congrArg BitVec.toNat eq
  have hi := i.isLt
  change a.toNat = (base+8*i.val)%2^64 at h
  omega

theorem low_outside_leaf (side : Bool) (a : Word) (low : a.toNat < 0x80000) :
    KeygenLeafCall.Outside side a := by
  have ne (n : Nat) (hn : 0x80000 ≤ n) (small : n < 2^64) : a ≠ BitVec.ofNat 64 n := by
    intro eq
    have h := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at h
    omega
  unfold KeygenLeafCall.Outside KeygenLeafLoop.Outside KeygenChainLoop.Outside
  refine ⟨ne _ (by decide) (by decide), ⟨ne _ (by decide) (by decide),
    ⟨ne _ (by decide) (by decide), ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · exact low_ne_word a low _ _ (by decide) (by decide)
  · exact low_ne_word a low _ _ (by decide) (by decide)
  · exact low_ne_word a low _ _ (by decide) (by decide)
  · exact low_ne_word a low _ _ (by decide) (by decide)
  · exact low_ne_word a low _ _ (by decide) (by decide)
  · cases side <;> exact low_ne_word a low _ _ (by decide) (by decide)

theorem left_low_frame (s : MachineState) (sp : s.getReg .x2=0x1000000)
    (a : Word) (low : a.toNat < 0x80000) : (leftState s).getMem a=s.getMem a := by
  have hs : a ≠ 0xfffff0 := by intro eq; rw [eq] at low; change 0xfffff0 < 0x80000 at low; omega
  have hl : a ≠ 0x80428 := by intro eq; rw [eq] at low; change 0x80428 < 0x80000 at low; omega
  rw [leftState,KeygenTreeControl.mem,if_neg hl,entered,enter_mem,sp]
  exact if_neg hs

theorem start_framed (s : MachineState) (pc : s.pc=0x1048) (sp : s.getReg .x2=0x1000000)
    (level tree : Nat) (secretKey : SecretKey) (ctx : Context level tree false secretKey s) :
    ∃ ready, OrdinarySteps keygen s 7 ready ∧ ready.pc=0x11cc ∧ ready.getReg .x1=0x1064 ∧
      ready.getReg .x2=0xfffff0 ∧ ready.getMem 0xfffff0=s.getReg .x1 ∧ Context level tree false secretKey ready ∧
      (∀ a, a.toNat < 0x80000 → ready.getMem a=s.getMem a) := by
  exact ⟨leftState s,left_block s pc sp,left_pc s pc,left_ra s pc,left_sp s sp,left_saved s sp,
    left_context s sp level tree secretKey ctx,left_low_frame s sp⟩

end SigGolfCandidate.Hypertree.KeygenTree
