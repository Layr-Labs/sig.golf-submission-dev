import SigGolfCandidate.Hypertree.KeygenBlocks
import SigGolfCandidate.Hypertree.KeygenTrace

/-! Inlined from SigGolfCandidate.Hypertree.ResourceAbstract; its only importer was SigGolfCandidate.Hypertree.ResourceTransfer. -/
section
namespace SigGolfCandidate.Resources
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- A finite map of known values; omitted entries carry no information. -/
def lookup {α : Type} [DecidableEq α] (key : α) : List (α × Word) → Option Word
  | [] => none
  | (k, v) :: rest => if key = k then some v else lookup key rest

def update {α : Type} [DecidableEq α] (key : α) (value : Option Word)
    (entries : List (α × Word)) : List (α × Word) :=
  let rest := entries.filter fun entry => decide (entry.1 ≠ key)
  match value with
  | none => rest
  | some value => (key, value) :: rest

theorem lookup_filter {α : Type} [DecidableEq α] (key other : α) (entries : List (α × Word)) :
    lookup other (entries.filter fun entry => decide (entry.1 ≠ key)) =
      if other = key then none else lookup other entries := by
  induction entries with
  | nil => simp [lookup]
  | cons entry entries ih =>
    rcases entry with ⟨k,v⟩
    by_cases h : k = key <;> by_cases h' : other = key <;> by_cases h'' : other = k <;>
      simp_all [lookup]

theorem lookup_update {α : Type} [DecidableEq α] (key other : α) (value : Option Word)
    (entries : List (α × Word)) :
    lookup other (update key value entries) = if other = key then value else lookup other entries := by
  cases value <;> simp only [update, lookup, lookup_filter]
  split <;> rfl

/-- Known control data, separated from arbitrary input and oracle-dependent words. -/
structure AbstractState where
  pc : Word
  regs : List (Reg × Word)
  mem : List (Word × Word)
  deriving DecidableEq, Repr

def AbstractState.getReg (a : AbstractState) (r : Reg) : Option Word :=
  if r = .x0 then some 0 else lookup r a.regs

def AbstractState.setReg (a : AbstractState) (r : Reg) (v : Option Word) : AbstractState :=
  { a with regs := update r v a.regs }

def AbstractState.setMem (a : AbstractState) (p : Word) (v : Option Word) : AbstractState :=
  { a with mem := update p v a.mem }

def AbstractState.setPC (a : AbstractState) (p : Word) : AbstractState := { a with pc := p }

def Knows (a : Option Word) (v : Word) : Prop := ∀ w, a = some w → v = w

structure AbstractState.Models (a : AbstractState) (s : MachineState) : Prop where
  pc : s.pc = a.pc
  regs : ∀ r, Knows (a.getReg r) (s.getReg r)
  mem : ∀ p, Knows (lookup p a.mem) (s.getMem p)

theorem Knows.none (v : Word) : Knows none v := by intro w h; cases h

theorem Knows.some (v : Word) : Knows (some v) v := by intro w h; exact Option.some.inj h

theorem Knows.map (f : Word → Word) {v : Option Word} {w : Word} (h : Knows v w) :
    Knows (v.map f) (f w) := by
  cases v with
  | none => exact Knows.none _
  | some v => have hv := h v rfl; subst w; exact Knows.some _

def map₂ (f : Word → Word → Word) (a b : Option Word) : Option Word := do
  return f (← a) (← b)

theorem Knows.map₂ (f : Word → Word → Word) {a b : Option Word} {v w : Word}
    (ha : Knows a v) (hb : Knows b w) : Knows (map₂ f a b) (f v w) := by
  cases a with
  | none => exact Knows.none _
  | some a =>
    cases b with
    | none => exact Knows.none _
    | some b =>
      have h₁ := ha a rfl; have h₂ := hb b rfl
      subst v; subst w; exact Knows.some _

theorem AbstractState.Models.setPC {a : AbstractState} {s : MachineState}
    (h : a.Models s) (p : Word) : (a.setPC p).Models (s.setPC p) := by
  exact ⟨rfl, h.regs, h.mem⟩

theorem AbstractState.Models.setReg {a : AbstractState} {s : MachineState}
    (h : a.Models s) (r : Reg) {v : Option Word} {w : Word} (known : Knows v w) :
    (a.setReg r v).Models (s.setReg r w) := by
  refine ⟨by simpa [AbstractState.setReg] using h.pc, ?_, ?_⟩
  · intro other value eq
    by_cases hz : other = .x0
    · subst other
      simp [AbstractState.getReg] at eq
      subst value
      rfl
    · by_cases hr : other = r
      · subst other
        have hv : v = some value := by
          simpa [AbstractState.getReg, hz, AbstractState.setReg, lookup_update] using eq
        rw [MachineState.getReg_setReg_eq hz]
        exact known value hv
      · have hv : a.getReg other = some value := by
          simpa [AbstractState.getReg, hz, hr, AbstractState.setReg, lookup_update] using eq
        rw [MachineState.getReg_setReg_ne s r other w (Ne.symm hr)]
        exact h.regs other value hv
  · intro p
    simpa only [AbstractState.setReg, MachineState.getMem_setReg] using h.mem p

theorem AbstractState.Models.setMem {a : AbstractState} {s : MachineState}
    (h : a.Models s) (p : Word) {v : Option Word} {w : Word} (known : Knows v w) :
    (a.setMem p v).Models (s.setMem p w) := by
  refine ⟨h.pc, ?_, ?_⟩
  · intro r
    simpa only [AbstractState.setMem, AbstractState.getReg, Hypertree.Expansion.reg_setMem] using h.regs r
  · intro other value eq
    by_cases hp : other = p
    · subst other
      have hv : v = some value := by simpa [AbstractState.setMem, lookup_update] using eq
      rw [Hypertree.Expansion.mem_setMem, if_pos rfl]
      exact known value hv
    · have hv : lookup other a.mem = some value := by
        simpa [AbstractState.setMem, lookup_update, hp] using eq
      rw [Hypertree.Expansion.mem_setMem, if_neg hp]
      exact h.mem other value hv

end SigGolfCandidate.Resources
end

namespace SigGolfCandidate.Resources
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp

private def nextReg (a : AbstractState) (rd : Reg) (value : Option Word) : AbstractState :=
  (a.setReg rd value).setPC (a.pc + 4)

private theorem nextReg_models {a : AbstractState} {s : MachineState} (h : a.Models s)
    (rd : Reg) {value : Option Word} {v : Word} (known : Knows value v) :
    (nextReg a rd value).Models ((s.setReg rd v).setPC (s.pc + 4)) := by
  simpa only [nextReg, h.pc] using (h.setReg rd known).setPC (a.pc + 4)

/-- A deliberately partial transfer function: unknown branch conditions or addresses are rejected. -/
def ordinaryTransfer (a : AbstractState) : Instr → Option AbstractState
  | .ADD rd r1 r2 => some (nextReg a rd (map₂ (· + ·) (a.getReg r1) (a.getReg r2)))
  | .ADDI rd rs off => some (nextReg a rd ((a.getReg rs).map (· + signExtend12 off)))
  | .SLLI rd rs n => some (nextReg a rd ((a.getReg rs).map (fun v : Word => v <<< n.toNat)))
  | .SRLI rd rs n => some (nextReg a rd ((a.getReg rs).map (fun v : Word => v >>> n.toNat)))
  | .ANDI rd rs imm => some (nextReg a rd ((a.getReg rs).map (· &&& signExtend12 imm)))
  | .XORI rd rs imm => some (nextReg a rd ((a.getReg rs).map (· ^^^ signExtend12 imm)))
  | .LUI rd imm => some (nextReg a rd (some (((imm.zeroExtend 32) <<< 12).signExtend 64)))
  | .LD rd rs off => do
      let base ← a.getReg rs
      let p := base + signExtend12 off
      if accessValid p 8 then some (nextReg a rd (lookup p a.mem)) else none
  | .SD rs data off => do
      let base ← a.getReg rs
      let p := base + signExtend12 off
      if accessValid p 8 then some ((a.setMem p (a.getReg data)).setPC (a.pc + 4)) else none
  | .BEQ r1 r2 off => do
      let v1 ← a.getReg r1
      let v2 ← a.getReg r2
      some (a.setPC (if v1 == v2 then a.pc + signExtend13 off else a.pc + 4))
  | .BNE r1 r2 off => do
      let v1 ← a.getReg r1
      let v2 ← a.getReg r2
      some (a.setPC (if v1 != v2 then a.pc + signExtend13 off else a.pc + 4))
  | .JAL rd off => some ((a.setReg rd (some (a.pc + 4))).setPC (a.pc + signExtend21 off))
  | .JALR rd rs off => do
      let base ← a.getReg rs
      some ((a.setReg rd (some (a.pc + 4))).setPC ((base + signExtend12 off) &&& ~~~1#64))
  | _ => none

/-- Every successful abstract ordinary step is a valid concrete step and preserves its information. -/
theorem ordinaryTransfer_sound {a next : AbstractState} {s : MachineState} (h : a.Models s)
    (instruction : Instr) (step : ordinaryTransfer a instruction = some next) :
    ordinaryStep s (.base instruction) = some (execInstrBr s instruction) ∧
      next.Models (execInstrBr s instruction) := by
  cases instruction <;> simp only [ordinaryTransfer, reduceCtorEq, Option.some.injEq] at step
  case ADD rd r1 r2 =>
    subst next
    exact ⟨rfl, nextReg_models h rd (Knows.map₂ _ (h.regs r1) (h.regs r2))⟩
  case ADDI rd rs off =>
    subst next
    exact ⟨rfl, nextReg_models h rd ((h.regs rs).map _)⟩
  case SLLI rd rs n =>
    subst next
    exact ⟨rfl, nextReg_models h rd ((h.regs rs).map _)⟩
  case SRLI rd rs n =>
    subst next
    exact ⟨rfl, nextReg_models h rd ((h.regs rs).map _)⟩
  case ANDI rd rs n =>
    subst next
    exact ⟨rfl, nextReg_models h rd ((h.regs rs).map _)⟩
  case XORI rd rs n =>
    subst next
    exact ⟨rfl, nextReg_models h rd ((h.regs rs).map _)⟩
  case LUI rd imm =>
    subst next
    exact ⟨rfl, nextReg_models h rd (Knows.some _)⟩
  case LD rd rs off =>
    cases hr : a.getReg rs with
    | none => simp [hr] at step
    | some base =>
      have eq := h.regs rs base hr
      by_cases valid : accessValid (base + signExtend12 off) 8 = true
      · simp [hr, valid] at step
        subst next
        refine ⟨by simp [ordinaryStep, memoryArgumentsValid, eq, valid], ?_⟩
        simpa only [execInstrBr, eq] using nextReg_models h rd (h.mem (base + signExtend12 off))
      · simp [hr, valid] at step
  case SD rs data off =>
    cases hr : a.getReg rs with
    | none => simp [hr] at step
    | some base =>
      have eq := h.regs rs base hr
      by_cases valid : accessValid (base + signExtend12 off) 8 = true
      · simp [hr, valid] at step
        subst next
        refine ⟨by simp [ordinaryStep, memoryArgumentsValid, eq, valid], ?_⟩
        simpa [execInstrBr, eq, h.pc] using
          (h.setMem (base + signExtend12 off) (h.regs data)).setPC (a.pc + 4)
      · simp [hr, valid] at step
  case BEQ r1 r2 off =>
    cases h1 : a.getReg r1 with
    | none => simp [h1] at step
    | some v1 =>
      cases h2 : a.getReg r2 with
      | none => simp [h1, h2] at step
      | some v2 =>
        simp [h1, h2] at step
        subst next
        refine ⟨rfl, ?_⟩
        have eq1 := h.regs r1 v1 h1
        have eq2 := h.regs r2 v2 h2
        by_cases e : v1 = v2
        · simpa [execInstrBr, eq1, eq2, e, h.pc] using h.setPC (a.pc + signExtend13 off)
        · simpa [execInstrBr, eq1, eq2, e, h.pc] using h.setPC (a.pc + 4)
  case BNE r1 r2 off =>
    cases h1 : a.getReg r1 with
    | none => simp [h1] at step
    | some v1 =>
      cases h2 : a.getReg r2 with
      | none => simp [h1, h2] at step
      | some v2 =>
        simp [h1, h2] at step
        subst next
        refine ⟨rfl, ?_⟩
        have eq1 := h.regs r1 v1 h1
        have eq2 := h.regs r2 v2 h2
        by_cases e : v1 = v2
        · simpa [execInstrBr, eq1, eq2, e, h.pc] using h.setPC (a.pc + 4)
        · simpa [execInstrBr, eq1, eq2, e, h.pc] using h.setPC (a.pc + signExtend13 off)
  case JAL rd off =>
    subst next
    refine ⟨rfl, ?_⟩
    simpa [execInstrBr, h.pc] using
      (h.setReg rd (Knows.some (s.pc + 4))).setPC (a.pc + signExtend21 off)
  case JALR rd rs off =>
    cases hr : a.getReg rs with
    | none => simp [hr] at step
    | some base =>
      simp [hr] at step
      subst next
      refine ⟨rfl, ?_⟩
      have eq := h.regs rs base hr
      simpa [execInstrBr, eq, h.pc] using
        (h.setReg rd (Knows.some (s.pc + 4))).setPC ((base + signExtend12 off) &&& ~~~1#64)

end SigGolfCandidate.Resources
