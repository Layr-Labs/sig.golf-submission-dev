import SigGolfCandidate.Hypertree.ResourceTransfer


namespace SigGolfCandidate.Resources
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- HASH overwrites exactly four words; their values become unknown. -/
def forgetHash (a : AbstractState) (destination : Word) : AbstractState :=
  let a := a.setMem destination none
  let a := a.setMem (destination + 8) none
  let a := a.setMem (destination + 16) none
  let a := a.setMem (destination + 24) none
  a.setPC (a.pc + 4)

theorem forgetHash_models {a : AbstractState} {s : MachineState} (h : a.Models s)
    (destination : Word) (hd : s.getReg .x12 = destination) (answer : BitVec 256) :
    (forgetHash a destination).Models (writeHash s answer) := by
  have m1 := h.setMem destination (Knows.none (answer.extractLsb' 0 64))
  have m2 := m1.setMem (destination + 8) (Knows.none (answer.extractLsb' 64 64))
  have m3 := m2.setMem (destination + 16) (Knows.none (answer.extractLsb' 128 64))
  have m4 := m3.setMem (destination + 24) (Knows.none (answer.extractLsb' 192 64))
  simpa [forgetHash, AbstractState.setMem, writeHash, MachineState.writeWords,
    hd, h.pc, BitVec.add_assoc] using m4.setPC (a.pc + 4)

def hashGuard (source bits destination : Word) : Bool :=
  decide (source.toNat % 8 = 0) && rangeValid source ((bits.toNat + 7) / 8) &&
    accessValid destination 8 && rangeValid destination 32

def hashTransfer (a : AbstractState) : Option (AbstractState × Nat) := do
  let source ← a.getReg .x10
  let bits ← a.getReg .x11
  let destination ← a.getReg .x12
  if hashGuard source bits destination then
    some (forgetHash a destination, compressions bits.toNat)
  else none

theorem hashTransfer_sound {a next : AbstractState} {s : MachineState} {blocks : Nat}
    (h : a.Models s) (step : hashTransfer a = some (next, blocks)) (answer : BitVec 256) :
    hashArgumentsValid s = true ∧ blocks = compressions (hashInput s).1 ∧
      next.Models (writeHash s answer) := by
  unfold hashTransfer at step
  cases hsrc : a.getReg .x10 with
  | none => simp [hsrc] at step
  | some source =>
    cases hbits : a.getReg .x11 with
    | none => simp [hsrc, hbits] at step
    | some bits =>
      cases hdst : a.getReg .x12 with
      | none => simp [hsrc, hbits, hdst] at step
      | some destination =>
        by_cases valid : hashGuard source bits destination = true
        · simp [hsrc, hbits, hdst, valid] at step
          rcases step with ⟨rfl, rfl⟩
          have esrc := h.regs .x10 source hsrc
          have ebits := h.regs .x11 bits hbits
          have edst := h.regs .x12 destination hdst
          refine ⟨?_, ?_, forgetHash_models h destination edst answer⟩
          · simpa only [hashArgumentsValid, hashGuard, esrc, ebits, edst] using valid
          · simp only [hashInput, ebits]
        · simp [hsrc, hbits, hdst, valid] at step

end SigGolfCandidate.Resources


namespace SigGolfCandidate.Resources
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp

structure Summary where
  next : AbstractState
  cycles : Nat
  calls : Nat
  blocks : Nat
  deriving DecidableEq, Repr

def baseAt (image : Image) (pc : Word) : Option Instr := do
  match ← Hypertree.Keygen.instructionAt image pc with
  | .base instruction => some instruction
  | _ => none

theorem baseAt_some (image : Image) (a : AbstractState) (s : MachineState) (h : a.Models s)
    (instruction : Instr) (decoded : baseAt image a.pc = some instruction) :
    fetch image s = some (.base instruction) := by
  unfold baseAt at decoded
  cases hf : Hypertree.Keygen.instructionAt image a.pc with
  | none => simp [hf] at decoded
  | some i =>
    cases i with
    | base i =>
      simp [hf] at decoded
      subst i
      simpa only [Hypertree.Keygen.fetch_at, h.pc] using hf
    | word op rd rs1 rs2 => simp [hf] at decoded
    | sraiw rd rs n => simp [hf] at decoded

/-- HALT is deliberately excluded from prefixes and certified separately. -/
def stepTransfer (image : Image) (a : AbstractState) : Option Summary := do
  let instruction ← baseAt image a.pc
  if instruction = .ECALL then
    if a.getReg .x5 = some 1 then
      let (next, blocks) ← hashTransfer a
      some ⟨next, 8 * blocks, 1, blocks⟩
    else none
  else
    let next ← ordinaryTransfer a instruction
    some ⟨next, 1, 0, 0⟩

theorem stepTransfer_sound {image : Image} {a : AbstractState} {result : Summary}
    (hash : Hash) (s : MachineState) (h : a.Models s)
    (step : stepTransfer image a = some result) :
    ∃ t, Trace hash image s 1 result.cycles result.calls result.blocks t ∧ result.next.Models t := by
  unfold stepTransfer at step
  cases hi : baseAt image a.pc with
  | none => simp [hi] at step
  | some instruction =>
    have hf := baseAt_some image a s h instruction hi
    by_cases he : instruction = .ECALL
    · subst instruction
      by_cases hs : a.getReg .x5 = some 1
      · cases ht : hashTransfer a with
        | none => simp [hi, hs, ht] at step
        | some pair =>
          rcases pair with ⟨next, blocks⟩
          simp [hi, hs, ht] at step
          subst result
          obtain ⟨valid, cost, model⟩ := hashTransfer_sound h ht (hash (hashInput s))
          refine ⟨writeHash s (hash (hashInput s)), ?_, model⟩
          have trace := Trace.hash (hash := hash) s (writeHash s (hash (hashInput s)))
            0 0 0 0 hf (h.regs .x5 1 hs) valid (Trace.refl _)
          simpa only [cost, Nat.zero_add] using trace
      · simp [hi] at step
        exact (hs step.1).elim
    · cases ht : ordinaryTransfer a instruction with
      | none => simp [hi, he, ht] at step
      | some next =>
        simp [hi, he, ht] at step
        subst result
        obtain ⟨valid, model⟩ := ordinaryTransfer_sound h instruction ht
        exact ⟨execInstrBr s instruction,
          Trace.ordinary s (execInstrBr s instruction) _ (.base instruction)
            0 0 0 0 hf valid (Trace.refl _), model⟩

/-- A bounded abstract prefix evaluator. Every accepted step has a concrete proof rule. -/
def runPrefix : Nat → Image → AbstractState → Option Summary
  | 0, _, a => some ⟨a, 0, 0, 0⟩
  | n + 1, image, a => do
      let first ← stepTransfer image a
      let rest ← runPrefix n image first.next
      some ⟨rest.next, first.cycles + rest.cycles,
        first.calls + rest.calls, first.blocks + rest.blocks⟩

theorem runPrefix_sound {image : Image} {a : AbstractState} {result : Summary}
    (n : Nat) (hash : Hash) (s : MachineState) (h : a.Models s)
    (run : runPrefix n image a = some result) :
    ∃ t, Trace hash image s n result.cycles result.calls result.blocks t ∧ result.next.Models t := by
  induction n generalizing a s result with
  | zero =>
    simp only [runPrefix, Option.some.injEq] at run
    subst result
    exact ⟨s, Trace.refl _, h⟩
  | succ n ih =>
    simp only [runPrefix] at run
    cases hs : stepTransfer image a with
    | none => simp [hs] at run
    | some first =>
      cases hr : runPrefix n image first.next with
      | none => simp [hs, hr] at run
      | some rest =>
        simp [hs, hr] at run
        subst result
        obtain ⟨mid, firstTrace, hm⟩ := stepTransfer_sound hash s h hs
        obtain ⟨t, restTrace, ht⟩ := ih mid hm hr
        refine ⟨t, ?_, ht⟩
        simpa only [Nat.add_comm 1 n] using firstTrace.trans restTrace

/-- A resource-exact prefix certificate, universally quantified over concrete state and oracle. -/
def CertifiedPrefix (image : Image) (a b : AbstractState) (steps cycles calls blocks : Nat) : Prop :=
  ∀ (hash : Hash) (s : MachineState), a.Models s →
    ∃ t, Trace hash image s steps cycles calls blocks t ∧ b.Models t

theorem CertifiedPrefix.of_run {image : Image} {a : AbstractState} {result : Summary} {n : Nat}
    (checked : runPrefix n image a = some result) :
    CertifiedPrefix image a result.next n result.cycles result.calls result.blocks := by
  intro hash s h
  exact runPrefix_sound n hash s h checked

theorem CertifiedPrefix.trans {image : Image} {a b c : AbstractState}
    {n cycles calls blocks m moreCycles moreCalls moreBlocks : Nat}
    (first : CertifiedPrefix image a b n cycles calls blocks)
    (second : CertifiedPrefix image b c m moreCycles moreCalls moreBlocks) :
    CertifiedPrefix image a c (n + m) (cycles + moreCycles) (calls + moreCalls) (blocks + moreBlocks) := by
  intro hash s h
  obtain ⟨mid, trace1, hm⟩ := first hash s h
  obtain ⟨t, trace2, ht⟩ := second hash mid hm
  exact ⟨t, trace1.trans trace2, ht⟩

/-- info: 'SigGolfCandidate.Resources.runPrefix_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runPrefix_sound

end SigGolfCandidate.Resources
