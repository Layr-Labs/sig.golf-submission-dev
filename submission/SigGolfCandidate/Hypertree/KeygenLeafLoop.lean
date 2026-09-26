import SigGolfCandidate.Hypertree.KeygenSecretExecution
import SigGolfCandidate.Hypertree.KeygenStepZero
import SigGolfCandidate.Hypertree.ChainLoopControl
import SigGolfCandidate.Hypertree.SignCapture
import SigGolfCandidate.Hypertree.EndpointStore
import SigGolfCandidate.Hypertree.KeygenLeafExecution

/-! Inlined from SigGolfCandidate.Hypertree.KeygenChainLoop; its only importer was SigGolfCandidate.Hypertree.KeygenLeafLoop. -/
section
namespace SigGolfCandidate.Hypertree.KeygenChainLoop
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen ChainLoopControl
set_option maxRecDepth 4096

structure Invariant (level tree step : Nat) (side : Bool) (chain : Reference.Chain)
    (value : Reference.Digest) (s : MachineState) : Prop where
  levelWord : s.getMem 0x80400 = BitVec.ofNat 64 level
  leafWord : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side)
  chainWord : s.getMem 0x80430 = BitVec.ofNat 64 chain.val
  stepWord : s.getMem 0x80438 = BitVec.ofNat 64 step
  indexWords : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
    (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64
  valueWords : ∀ i : Fin 2, s.getMem (Signing.wordAddress 0x80510 i.val) = value.extractLsb' (64*i.val) 64
  modeWord : s.getMem 0x80440 = 0

theorem Invariant.of_mem_eq {level tree step : Nat} {side : Bool} {chain : Reference.Chain}
    {value : Reference.Digest} {s t : MachineState} (h : Invariant level tree step side chain value s)
    (eq : ∀ a, t.getMem a = s.getMem a) : Invariant level tree step side chain value t := by
  constructor
  · rw [eq]; exact h.levelWord
  · rw [eq]; exact h.leafWord
  · rw [eq]; exact h.chainWord
  · rw [eq]; exact h.stepWord
  · intro i; rw [eq]; exact h.indexWords i
  · intro i; rw [eq]; exact h.valueWords i
  · rw [eq]; exact h.modeWord

/-- Addresses outside every word modified by a keygen chain loop. -/
def Outside (a : Word) : Prop :=
  a ≠ 0x80438 ∧ (∀ i : Fin 8, a ≠ Signing.wordAddress 0x80000 i.val) ∧
    (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) ∧
    (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80510 i.val)

instance (a : Word) : Decidable (Outside a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem check_code : CheckCode keygen 0x13a4 := by decide

theorem increment_code : IncrementCode keygen 0x14d4 (-472) := by decide

def guarded (s : MachineState) : MachineState := check (Signing.captureModeState 128 s)

theorem guard (s : MachineState) (pc : s.pc = 0x1318) (mode : s.getMem 0x80440 = 0) :
    OrdinarySteps keygen s 9 (guarded s) ∧
      (guarded s).pc = (if s.getMem 0x80438 = 7 then 0x14f4 else 0x13b8) ∧
      (∀ a, (guarded s).getMem a = s.getMem a) ∧
      (guarded s).getReg .x1 = s.getReg .x1 ∧ (guarded s).getReg .x2 = s.getReg .x2 := by
  have skip := Signing.captureMode_block keygen 0x1318 128 Signing.keygen_upper_mode_code s pc
  have skipPC : (Signing.captureModeState 128 s).pc = 0x13a4 := by
    rw [Signing.captureMode_pc,if_pos mode,pc]; decide
  have next := check_block keygen 0x13a4 check_code _ skipPC
  refine ⟨ordinary_trans keygen _ _ _ 4 5 skip next,?_,?_,?_,?_⟩
  · simp only [guarded,check_pc,skipPC,Signing.captureMode_mem]
    split <;> decide
  · intro a; rw [guarded,check_mem,Signing.captureMode_mem]
  · rw [guarded,(check_stack _).1]
    simp [Signing.captureModeState,execInstrBr,MachineState.getReg_setReg_ne]
  · rw [guarded,(check_stack _).2,Signing.captureMode_sp]

/-- A nonterminal iteration performs one position-tweaked chain hash. -/
theorem step (hash : Hash) (s : MachineState) (pc : s.pc = 0x1318)
    (level tree n : Nat) (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (bound : n < 7) (inv : Invariant level tree n side chain value s) :
    ∃ final, Trace hash keygen s 100 107 1 1 final ∧ final.pc = 0x1318 ∧
      Invariant level tree (n+1) side chain (Reference.chainHash hash level tree side chain n value) final ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, Outside a → final.getMem a = s.getMem a) := by
  obtain ⟨pre,gpc,gmem,gra,gsp⟩ := guard s pc inv.modeWord
  have distinct : s.getMem 0x80438 ≠ 7 := by
    rw [inv.stepWord]
    intro eq
    have natEq := congrArg BitVec.toNat eq
    change n % 18446744073709551616 = 7 at natEq
    omega
  rw [if_neg distinct] at gpc
  have gi := inv.of_mem_eq gmem
  obtain ⟨hashed,ht,hpc,words,ra,sp,frame⟩ :=
    KeygenChain.compute keygen hash 0x13b8 KeygenChain.keygen_code (guarded s) gpc
      level tree n side chain value gi.levelWord gi.leafWord gi.chainWord gi.stepWord gi.indexWords gi.valueWords
  have inc := increment_block keygen 0x14d4 (-472) increment_code hashed hpc
  have metadata (a : Word) (outside : Outside a) : hashed.getMem a = s.getMem a := by
    rw [frame a (fun i : Fin 6 => outside.2.1 ⟨i.val, by omega⟩) outside.2.2.1 outside.2.2.2,gmem]
  have stepMem : hashed.getMem 0x80438 = BitVec.ofNat 64 n := by
    rw [frame _ (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide),gmem]
    exact inv.stepWord
  refine ⟨increment hashed (-472),pre.trace.trans (ht.trans inc.trace),?_,?_,
    (increment_stack _ _).1.trans (ra.trans gra),(increment_stack _ _).2.trans (sp.trans gsp),?_⟩
  · rw [increment_pc,hpc]; decide
  · constructor
    · rw [increment_mem]; simp only [show (0x80400:Word) ≠ 0x80438 by decide,↓reduceIte]
      rw [metadata _ (by decide)]; exact inv.levelWord
    · rw [increment_mem]; simp only [show (0x80428:Word) ≠ 0x80438 by decide,↓reduceIte]
      rw [metadata _ (by decide)]; exact inv.leafWord
    · rw [increment_mem]; simp only [show (0x80430:Word) ≠ 0x80438 by decide,↓reduceIte]
      rw [metadata _ (by decide)]; exact inv.chainWord
    · rw [increment_mem,if_pos rfl,stepMem]
      exact (BitVec.ofNat_add n 1).symm
    · intro i
      have outside : Outside (Signing.wordAddress 0x80408 i.val) := by fin_cases i <;> decide
      rw [increment_mem,if_neg outside.1,metadata _ outside]
      exact inv.indexWords i
    · intro i
      have ne : Signing.wordAddress 0x80510 i.val ≠ (0x80438:Word) := by fin_cases i <;> decide
      rw [increment_mem,if_neg ne]
      exact words i
    · rw [increment_mem]; simp only [show (0x80440:Word) ≠ 0x80438 by decide,↓reduceIte]
      rw [metadata _ (by decide)]; exact inv.modeWord
  · intro a outside
    rw [increment_mem,if_neg outside.1,metadata a outside]

/-- All remaining keygen chain rounds, including the final loop-exit guard. -/
theorem run (hash : Hash) (count : Nat) (s : MachineState) (pc : s.pc = 0x1318)
    (level tree start : Nat) (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (bound : start + count = 7) (inv : Invariant level tree start side chain value s) :
    ∃ final, Trace hash keygen s (100*count+9) (107*count+9) count count final ∧
      final.pc = 0x14f4 ∧
      Invariant level tree 7 side chain (walk (Reference.chainHash hash level tree side chain) start count value) final ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, Outside a → final.getMem a = s.getMem a) := by
  induction count generalizing s start value with
  | zero =>
    have startEq : start = 7 := by omega
    subst start
    obtain ⟨trace,gpc,gmem,ra,sp⟩ := guard s pc inv.modeWord
    refine ⟨guarded s,trace.trace,?_,?_,ra,sp,fun a _ => gmem a⟩
    · have eq : s.getMem 0x80438 = 7 := inv.stepWord
      rw [if_pos eq] at gpc
      exact gpc
    · exact inv.of_mem_eq gmem
  | succ count ih =>
    obtain ⟨next,trace,nextPC,nextInv,ra,sp,frame⟩ :=
      step hash s pc level tree start side chain value (by omega) inv
    obtain ⟨final,tail,finalPC,finalInv,finalRA,finalSP,finalFrame⟩ :=
      ih next nextPC (start+1) (Reference.chainHash hash level tree side chain start value)
        (by omega) nextInv
    refine ⟨final,?_,finalPC,finalInv,finalRA.trans ra,finalSP.trans sp,?_⟩
    · simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using trace.trans tail
    · intro a outside
      rw [finalFrame a outside,frame a outside]

/-- info: 'SigGolfCandidate.Hypertree.KeygenChainLoop.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run

end SigGolfCandidate.Hypertree.KeygenChainLoop
end

namespace SigGolfCandidate.Hypertree.KeygenSecretStart
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096

/-- Static inputs preserved throughout the upper-leaf chain generation loop. -/
structure Context (level tree : Nat) (side : Bool) (secretKey : SecretKey) (s : MachineState) : Prop where
  levelWord : s.getMem 0x80400 = BitVec.ofNat 64 level
  leafWord : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side)
  indexWords : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
    (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64
  secretKeyWords : ∀ i : Fin 4, s.getMem (Signing.wordAddress 0x20 i.val) = secretKey.extractLsb' (64*i.val) 64
  modeWord : s.getMem 0x80440 = 0

/-- Secret derivation followed by STEP=0 establishes the complete chain-loop invariant. -/
theorem prepare (hash : Hash) (s : MachineState) (pc : s.pc=0x1204)
    (level tree : Nat) (side : Bool) (chain : Reference.Chain) (secretKey : SecretKey)
    (context : Context level tree side secretKey s)
    (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val) :
    ∃ final, Trace hash keygen s 93 100 1 1 final ∧ final.pc=0x1318 ∧
      KeygenChainLoop.Invariant level tree 0 side chain (Reference.secret hash secretKey level tree side chain) final ∧
      final.getReg .x1=s.getReg .x1 ∧ final.getReg .x2=s.getReg .x2 ∧
      (∀ a, KeygenChainLoop.Outside a → final.getMem a=s.getMem a) := by
  obtain ⟨secret,trace,spc,words,ra,sp,frame⟩ :=
    KeygenSecret.compute keygen hash 0x1204 KeygenSecret.keygen_code s pc level tree side chain secretKey
      context.levelWord context.leafWord counter context.indexWords context.secretKeyWords
  have reset := KeygenStepZero.block keygen 0x1308 KeygenStepZero.keygen_code secret spc
  have finalFrame (a : Word) (outside : KeygenChainLoop.Outside a) :
      (KeygenStepZero.state secret).getMem a=s.getMem a := by
    rw [KeygenStepZero.mem,if_neg outside.1,frame a outside.2.1 outside.2.2.1 outside.2.2.2]
  refine ⟨KeygenStepZero.state secret,trace.trans reset.trace,?_,?_,
    (KeygenStepZero.stack secret).1.trans ra,(KeygenStepZero.stack secret).2.trans sp,finalFrame⟩
  · rw [KeygenStepZero.pc,spc]; rfl
  · constructor
    · rw [finalFrame _ (by decide)]; exact context.levelWord
    · rw [finalFrame _ (by decide)]; exact context.leafWord
    · rw [finalFrame _ (by decide)]; exact counter
    · rw [KeygenStepZero.mem,if_pos rfl]; rfl
    · intro i
      rw [finalFrame _ (by fin_cases i <;> decide)]
      exact context.indexWords i
    · intro i
      rw [KeygenStepZero.mem,if_neg (by fin_cases i <;> decide)]
      exact words i
    · rw [finalFrame _ (by decide)]; exact context.modeWord

end SigGolfCandidate.Hypertree.KeygenSecretStart


namespace SigGolfCandidate.Hypertree.KeygenLeafLoop
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen KeygenSecretStart
set_option maxRecDepth 4096

/-- Memory unaffected by generating all46chain endpoints. -/
def Outside (a : Word) : Prop :=
  a ≠ 0x80430 ∧ KeygenChainLoop.Outside a ∧
    ∀ i : Fin 92, a ≠ Signing.wordAddress 0x80800 i.val

instance (a : Word) : Decidable (Outside a) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem endpoint_outside_work (chain : Reference.Chain) (i : Fin 2) :
    KeygenChainLoop.Outside (KeygenEndpoint.endpointAddress chain.val i.val) := by
  have hc := chain.isLt
  have hi := i.isLt
  constructor
  · intro eq
    have h := congrArg BitVec.toNat eq
    change (0x80800+16*chain.val+8*i.val)%2^64=0x80438 at h
    omega
  constructor
  · intro j eq
    have hj := j.isLt
    have h := congrArg BitVec.toNat eq
    change (0x80800+16*chain.val+8*i.val)%2^64=(0x80000+8*j.val)%2^64 at h
    omega
  constructor
  · intro j eq
    have hj := j.isLt
    have h := congrArg BitVec.toNat eq
    change (0x80800+16*chain.val+8*i.val)%2^64=(0x80300+8*j.val)%2^64 at h
    omega
  · intro j eq
    have hj := j.isLt
    have h := congrArg BitVec.toNat eq
    change (0x80800+16*chain.val+8*i.val)%2^64=(0x80510+8*j.val)%2^64 at h
    omega

theorem endpoint_ne_chain (chain : Reference.Chain) (i : Fin 2) :
    KeygenEndpoint.endpointAddress chain.val i.val ≠ 0x80430 := by
  intro eq
  have h := congrArg BitVec.toNat eq
  change (0x80800+16*chain.val+8*i.val)%2^64=0x80430 at h
  have := chain.isLt
  have := i.isLt
  omega

theorem endpoint_separate (left right : Reference.Chain) (i j : Fin 2) (ne : left.val≠right.val) :
    KeygenEndpoint.endpointAddress left.val i.val ≠ KeygenEndpoint.endpointAddress right.val j.val := by
  intro eq
  have h := congrArg BitVec.toNat eq
  change (0x80800+16*left.val+8*i.val)%2^64=(0x80800+16*right.val+8*j.val)%2^64 at h
  have := left.isLt
  have := right.isLt
  have := i.isLt
  have := j.isLt
  omega

def Endpoints (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool) (n : Nat) (s : MachineState) : Prop :=
  ∀ chain : Reference.Chain, chain.val<n → ∀ i : Fin 2,
    s.getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
      (Reference.endpoint hash secretKey level tree side chain).extractLsb' (64*i.val) 64

/-- One outer iteration derives a secret, performs seven chain rounds, and saves its endpoint. -/
theorem iteration (hash : Hash) (s : MachineState) (pc : s.pc=0x1204)
    (level tree : Nat) (side : Bool) (chain : Reference.Chain) (secretKey : SecretKey)
    (context : Context level tree side secretKey s)
    (counter : s.getMem 0x80430=BitVec.ofNat 64 chain.val)
    (before : Endpoints hash secretKey level tree side chain.val s) :
    ∃ final, Trace hash keygen s 823 879 8 8 final ∧
      final.pc=(if chain.val+1=46 then 0x1548 else 0x1204) ∧
      Context level tree side secretKey final ∧ final.getMem 0x80430=BitVec.ofNat 64 (chain.val+1) ∧
      Endpoints hash secretKey level tree side (chain.val+1) final ∧
      final.getReg .x1=s.getReg .x1 ∧ final.getReg .x2=s.getReg .x2 ∧
      (∀ a, Outside a → final.getMem a=s.getMem a) := by
  obtain ⟨ready,pre,rpc,inv,rra,rsp,rframe⟩ := KeygenSecretStart.prepare hash s pc level tree side chain secretKey context counter
  obtain ⟨ended,rounds,epc,einv,era,esp,eframe⟩ :=
    KeygenChainLoop.run hash 7 ready rpc level tree 0 side chain _ (by decide) inv
  obtain ⟨final,post,fpc,fcounter,words,fra,fsp,fframe⟩ :=
    KeygenEndpoint.store_endpoint keygen 0x14f4 (-832) KeygenEndpoint.keygen_code ended chain
      (Reference.endpoint hash secretKey level tree side chain) epc einv.chainWord einv.valueWords
  have finalFrame (a : Word) (outside : Outside a) : final.getMem a=s.getMem a := by
    rw [fframe a outside.1 (by
      intro i
      have h := outside.2.2 ⟨2*chain.val+i.val,by have := chain.isLt; have := i.isLt; omega⟩
      simpa [Signing.wordAddress,KeygenEndpoint.endpointAddress,Nat.mul_add,← Nat.mul_assoc,Nat.add_assoc] using h),
      eframe a outside.2.1,rframe a outside.2.1]
  refine ⟨final,pre.trans (rounds.trans post.trace),?_,?_,fcounter,?_,fra.trans (era.trans rra),fsp.trans (esp.trans rsp),finalFrame⟩
  · exact fpc
  · constructor
    · rw [finalFrame _ (by decide)]; exact context.levelWord
    · rw [finalFrame _ (by decide)]; exact context.leafWord
    · intro i; rw [finalFrame _ (by fin_cases i <;> decide)]; exact context.indexWords i
    · intro i; rw [finalFrame _ (by fin_cases i <;> decide)]; exact context.secretKeyWords i
    · rw [finalFrame _ (by decide)]; exact context.modeWord
  · intro old lt i
    by_cases eq : old=chain
    · subst old; exact words i
    · have ne : old.val≠chain.val := by intro he; apply eq; exact Fin.ext he
      rw [fframe _ (endpoint_ne_chain old i) (fun j => endpoint_separate old chain i j ne),
        eframe _ (endpoint_outside_work old i),rframe _ (endpoint_outside_work old i)]
      exact before old (by omega) i

/-- All46endpoint slots are populated with their exact reference values. -/
theorem loop (hash : Hash) (count : Nat) (s : MachineState) (n level tree : Nat)
    (side : Bool) (secretKey : SecretKey) (length : n+count=46)
    (pc : s.pc=(if n=46 then 0x1548 else 0x1204))
    (context : Context level tree side secretKey s)
    (counter : s.getMem 0x80430=BitVec.ofNat 64 n)
    (before : Endpoints hash secretKey level tree side n s) :
    ∃ final, Trace hash keygen s (823*count) (879*count) (8*count) (8*count) final ∧
      final.pc=0x1548 ∧ Context level tree side secretKey final ∧
      final.getMem 0x80430=46 ∧ Endpoints hash secretKey level tree side 46 final ∧
      final.getReg .x1=s.getReg .x1 ∧ final.getReg .x2=s.getReg .x2 ∧
      (∀ a, Outside a → final.getMem a=s.getMem a) := by
  induction count generalizing s n with
  | zero =>
    have hn : n=46 := by omega
    subst n
    refine ⟨s,Trace.refl _,?_,context,counter,before,rfl,rfl,fun _ _ => rfl⟩
    simpa using pc
  | succ count ih =>
    have hn : n<46 := by omega
    obtain ⟨next,pre,npc,ncontext,ncounter,nendpoints,nra,nsp,nframe⟩ :=
      iteration hash s (by simpa [show n≠46 by omega] using pc) level tree side ⟨n,hn⟩ secretKey context counter before
    obtain ⟨final,tail,fpc,fcontext,fcounter,fendpoints,fra,fsp,fframe⟩ :=
      ih next (n+1) (by omega) npc ncontext ncounter nendpoints
    refine ⟨final,?_,fpc,fcontext,fcounter,fendpoints,fra.trans nra,fsp.trans nsp,?_⟩
    · simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using pre.trans tail
    · intro a outside; rw [fframe a outside,nframe a outside]

/-- The endpoint invariant is exactly the92-word layout expected by leaf compression. -/
theorem endpoint_words (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool) (s : MachineState)
    (all : Endpoints hash secretKey level tree side 46 s) :
    ∀ i : Fin 92, s.getMem (Signing.wordAddress 0x80800 i.val) =
      KeygenLeafHeader.endpointWord (Reference.endpoint hash secretKey level tree side) i := by
  intro i
  have hc : i.val/2<46 := by have := i.isLt; omega
  have hw : i.val%2<2 := by omega
  have h := all ⟨i.val/2,hc⟩ hc ⟨i.val%2,hw⟩
  have addr : KeygenEndpoint.endpointAddress (i.val/2) (i.val%2)=Signing.wordAddress 0x80800 i.val := by
    unfold KeygenEndpoint.endpointAddress Signing.wordAddress
    congr 1
    omega
  rw [addr] at h
  exact h

/-- info: 'SigGolfCandidate.Hypertree.KeygenLeafLoop.loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop

end SigGolfCandidate.Hypertree.KeygenLeafLoop
