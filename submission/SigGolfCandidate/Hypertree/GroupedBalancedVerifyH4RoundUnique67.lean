import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexRound67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreePost67

/-! A completed H4 round has a unique instruction count and final state. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4RoundUnique67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

private theorem trace_one_more {hash : Hash} {image : Image}
    {s t u : MachineState} {n c q b C Q B : Nat}
    (short : Trace hash image s n c q b t)
    (long : Trace hash image s (n+1) C Q B u) :
    ∃ c' q' b', Trace hash image t 1 c' q' b' u := by
  induction short generalizing u C Q B with
  | refl state =>
      exact ⟨C,Q,B,by simpa using long⟩
  | ordinary state next final instruction steps cycles calls blocks hf hs tail ih =>
      cases long with
      | ordinary _ other _ otherInstruction _ _ _ _ hf' hs' tail' =>
          have instr := Option.some.inj (hf.symm.trans hf')
          subst otherInstruction
          have nextEq := Option.some.inj (hs.symm.trans hs')
          subst other
          exact ih tail'
      | hash _ _ _ _ _ _ hf' _ _ _ =>
          have instr := Option.some.inj (hf.symm.trans hf')
          simp [instr,ordinaryStep] at hs
  | hash state final steps cycles calls blocks hf hs hv tail ih =>
      cases long with
      | ordinary _ other _ otherInstruction _ _ _ _ hf' hs' _ =>
          have instr := Option.some.inj (hf'.symm.trans hf)
          simp [instr,ordinaryStep] at hs'
      | hash _ _ _ _ _ _ _ _ _ tail' =>
          exact ih tail'

private theorem code_1290 :
    Keygen.instructionAt image 0x1290 =
      some (.base (.LUI .x28 0x81)) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

private theorem code_14f4 :
    Keygen.instructionAt image 0x14f4 =
      some (.base (.ADDI .x6 .x0 0)) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

private theorem one_step_exit (hash : Hash) (s t : MachineState)
    (pc : s.pc = 0x1290 ∨ s.pc = 0x14f4)
    {cycles calls blocks : Nat}
    (run : Trace hash image s 1 cycles calls blocks t) :
    t.pc ≠ s.pc := by
  rcases pc with pc | pc
  · have fetched : fetch image s = some (.base (.LUI .x28 0x81)) := by
      simpa only [Keygen.fetch_at,pc] using code_1290
    have step : ordinaryStep s (.base (.LUI .x28 0x81)) =
        some (execInstrBr s (.LUI .x28 0x81)) := rfl
    have built : Trace hash image s 1 1 0 0
        (execInstrBr s (.LUI .x28 0x81)) := by
      simpa using Trace.ordinary s _ _ _ 0 0 0 0
        fetched step (Trace.refl _)
    have same := Trace.deterministic run built
    rw [same]
    simp [execInstrBr,pc]
  · have fetched : fetch image s = some (.base (.ADDI .x6 .x0 0)) := by
      simpa only [Keygen.fetch_at,pc] using code_14f4
    have step : ordinaryStep s (.base (.ADDI .x6 .x0 0)) =
        some (execInstrBr s (.ADDI .x6 .x0 0)) := rfl
    have built : Trace hash image s 1 1 0 0
        (execInstrBr s (.ADDI .x6 .x0 0)) := by
      simpa using Trace.ordinary s _ _ _ 0 0 0 0
        fetched step (Trace.refl _)
    have same := Trace.deterministic run built
    rw [same]
    simp [execInstrBr,pc]

theorem round_unique (hash : Hash) (s first second : MachineState)
    (c : Word) (m n cm cn qm qn bm bn : Nat)
    (hm : m = 162 ∨ m = 163) (hn : n = 162 ∨ n = 163)
    (firstRun : Trace hash image s m cm qm bm first)
    (secondRun : Trace hash image s n cn qn bn second)
    (firstPC : first.pc = if c+1 ≠ (10 : Word) then 0x1290 else 0x14f4)
    (secondPC : second.pc = if c+1 ≠ (10 : Word) then 0x1290 else 0x14f4) :
    m = n ∧ first = second := by
  have exitPC (state : MachineState)
      (atExit : state.pc =
        if c+1 ≠ (10 : Word) then 0x1290 else 0x14f4) :
      state.pc = 0x1290 ∨ state.pc = 0x14f4 := by
    by_cases stop : c+1 ≠ (10 : Word)
    · left
      simpa only [if_pos stop] using atExit
    · right
      simpa only [if_neg stop] using atExit
  rcases hm with hm | hm <;> rcases hn with hn | hn
  · subst m
    subst n
    exact ⟨rfl,Trace.deterministic firstRun secondRun⟩
  · subst m
    subst n
    obtain ⟨c',q',b',step⟩ := trace_one_more firstRun secondRun
    have ne := one_step_exit hash first second
      (exitPC first firstPC) step
    exact False.elim (ne (secondPC.trans firstPC.symm))
  · subst m
    subst n
    obtain ⟨c',q',b',step⟩ := trace_one_more secondRun firstRun
    have ne := one_step_exit hash second first
      (exitPC second secondPC) step
    exact False.elim (ne (firstPC.trans secondPC.symm))
  · subst m
    subst n
    exact ⟨rfl,Trace.deterministic firstRun secondRun⟩

#print axioms round_unique
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4RoundUnique67
