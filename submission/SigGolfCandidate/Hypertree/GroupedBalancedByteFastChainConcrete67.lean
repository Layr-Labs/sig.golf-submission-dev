import SigGolfCandidate.Hypertree.GroupedBalancedByteFastIteration67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainReady67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainFold67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainConcrete67. -/
section
/-! Resource preserving induction for the 67 concrete WOTS chain transitions. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

private def chainAt (i : Nat) : Fin 67 :=
  ⟨i % 67, Nat.mod_lt _ (by decide)⟩

theorem chainAt_eq (i : Nat) (hi : i < 67) :
    chainAt i = ⟨i,hi⟩ := by
  apply Fin.ext
  simp [chainAt,Nat.mod_eq_of_lt hi]

def gapAt (message : Reference.Digest) (i : Nat) : Nat :=
  GroupedBalancedChecksum67.maxDigit (chainAt i) -
    (GroupedBalancedChecksum67.digit message (chainAt i)).val

def overheadAt (i : Nat) : Nat :=
  GroupedBalancedByteFastIteration67.overhead (chainAt i)

def stepsAt (message : Reference.Digest) (i : Nat) : Nat :=
  4 * gapAt message i + overheadAt i

def cyclesAt (message : Reference.Digest) (i : Nat) : Nat :=
  11 * gapAt message i + overheadAt i

def prefixGap (message : Reference.Digest) (n : Nat) : Nat :=
  (Finset.range n).sum (gapAt message)

def prefixSteps (message : Reference.Digest) (n : Nat) : Nat :=
  (Finset.range n).sum (stepsAt message)

def prefixCycles (message : Reference.Digest) (n : Nat) : Nat :=
  (Finset.range n).sum (cyclesAt message)

theorem gap_sum (message : Reference.Digest) :
    prefixGap message 67 = GroupedBalancedChecksum67.suffixCost message := by
  unfold prefixGap GroupedBalancedChecksum67.suffixCost
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp [gapAt,chainAt,Nat.mod_eq_of_lt i.isLt]

theorem overhead_sum :
    (Finset.range 67).sum overheadAt = 1221 := by
  rw [← Fin.sum_univ_eq_sum_range]
  have h := GroupedBalancedByteFastIteration67.overhead_sum
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  simp [overheadAt,chainAt,Nat.mod_eq_of_lt i.isLt]

theorem steps_sum (message : Reference.Digest) :
    prefixSteps message 67 =
      4 * GroupedBalancedChecksum67.suffixCost message + 1221 := by
  unfold prefixSteps stepsAt
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  change 4 * prefixGap message 67 +
    (Finset.range 67).sum overheadAt = _
  rw [gap_sum,overhead_sum]

theorem cycles_sum (message : Reference.Digest) :
    prefixCycles message 67 =
      11 * GroupedBalancedChecksum67.suffixCost message + 1221 := by
  unfold prefixCycles cyclesAt
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  change 11 * prefixGap message 67 +
    (Finset.range 67).sum overheadAt = _
  rw [gap_sum,overhead_sum]

theorem fold_prefix (hash : Hash) (image : Image)
    (message : Reference.Digest)
    (P : Nat → MachineState → Prop)
    (start : MachineState) (initial : P 0 start)
    (step : ∀ i : Nat, i < 67 → ∀ s : MachineState, P i s →
      ∃ t : MachineState,
        Trace hash image s
          (stepsAt message i) (cyclesAt message i)
          (gapAt message i) (gapAt message i) t ∧
        P (i+1) t)
    (n : Nat) (hn : n ≤ 67) :
    ∃ final : MachineState,
      Trace hash image start
        (prefixSteps message n) (prefixCycles message n)
        (prefixGap message n) (prefixGap message n) final ∧
      P n final := by
  induction n with
  | zero =>
    refine ⟨start, ?_, initial⟩
    simpa [prefixSteps,prefixCycles,prefixGap] using
      (Trace.refl (hash := hash) (image := image) start)
  | succ n ih =>
    have small : n < 67 := by omega
    obtain ⟨mid, first, inv⟩ := ih (by omega)
    obtain ⟨final, second, next⟩ := step n small mid inv
    refine ⟨final, ?_, next⟩
    have total := first.trans second
    simpa [prefixSteps,prefixCycles,prefixGap,
      Finset.sum_range_succ] using total

theorem fold_all (hash : Hash) (image : Image)
    (message : Reference.Digest)
    (P : Nat → MachineState → Prop)
    (start : MachineState) (initial : P 0 start)
    (step : ∀ i : Nat, i < 67 → ∀ s : MachineState, P i s →
      ∃ t : MachineState,
        Trace hash image s
          (stepsAt message i) (cyclesAt message i)
          (gapAt message i) (gapAt message i) t ∧
        P (i+1) t) :
    ∃ final : MachineState,
      Trace hash image start
        (4 * GroupedBalancedChecksum67.suffixCost message + 1221)
        (11 * GroupedBalancedChecksum67.suffixCost message + 1221)
        (GroupedBalancedChecksum67.suffixCost message)
        (GroupedBalancedChecksum67.suffixCost message) final ∧
      P 67 final := by
  obtain ⟨final, trace, inv⟩ := fold_prefix hash image message P start
    initial step 67 (by decide)
  refine ⟨final, ?_, inv⟩
  simpa only [steps_sum,cycles_sum,gap_sum] using trace

#print axioms fold_all

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainFold67

end

/-! Concrete 67-chain Fast2Byte WOTS execution, including all three special
radix transitions. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainConcrete67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastLimit67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainReady67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainFold67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem step_short (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (chain : Fin 67)
    (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (short : chain.val < 64)
    (ready : Ready s base leaf start chain message values) :
    ∃ final,
      Trace hash image s
        (4 * (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) + 18)
        (11 * (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) + 18)
        (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val)
        (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) final ∧
      Ready final base leaf start ⟨chain.val+1,by omega⟩
        message values := by
  obtain ⟨copied,first,after,_⟩ := run_to_after_copy hash s
    base leaf start chain message values safe baseBound ready
  obtain ⟨second,next⟩ := after_copy_short copied base leaf start
    chain message values short after
  refine ⟨advanceState copied,?_,next⟩
  convert first.trans second.trace using 1 <;> omega

theorem step_64 (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (ready : Ready s base leaf start (64 : Fin 67) message values) :
    ∃ final,
      Trace hash image s
        (4 * (3 - (GroupedBalancedChecksum67.digit message (64 : Fin 67)).val) + 22)
        (11 * (3 - (GroupedBalancedChecksum67.digit message (64 : Fin 67)).val) + 22)
        (3 - (GroupedBalancedChecksum67.digit message (64 : Fin 67)).val)
        (3 - (GroupedBalancedChecksum67.digit message (64 : Fin 67)).val)
        final ∧
      Ready final base leaf start (65 : Fin 67) message values := by
  obtain ⟨copied,first,after,_⟩ := run_to_after_copy hash s
    base leaf start (64 : Fin 67) message values safe baseBound ready
  obtain ⟨second,next⟩ := after_copy_64 copied base leaf start
    message values after
  refine ⟨next65State copied,?_,next⟩
  simp [GroupedBalancedChecksum67.maxDigit] at first
  convert first.trans second.trace using 1 <;> omega

theorem step_65 (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (ready : Ready s base leaf start (65 : Fin 67) message values) :
    ∃ final,
      Trace hash image s
        (4 * (8 - (GroupedBalancedChecksum67.digit message (65 : Fin 67)).val) + 24)
        (11 * (8 - (GroupedBalancedChecksum67.digit message (65 : Fin 67)).val) + 24)
        (8 - (GroupedBalancedChecksum67.digit message (65 : Fin 67)).val)
        (8 - (GroupedBalancedChecksum67.digit message (65 : Fin 67)).val)
        final ∧
      Ready final base leaf start (66 : Fin 67) message values := by
  obtain ⟨copied,first,after,_⟩ := run_to_after_copy hash s
    base leaf start (65 : Fin 67) message values safe baseBound ready
  obtain ⟨second,next⟩ := after_copy_65 copied base leaf start
    message values after
  refine ⟨next66State copied,?_,next⟩
  simp [GroupedBalancedChecksum67.maxDigit] at first
  convert first.trans second.trace using 1 <;> omega

theorem step_66 (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (ready : Ready s base leaf start (66 : Fin 67) message values) :
    ∃ final,
      Trace hash image s
        (4 * (10 - (GroupedBalancedChecksum67.digit message (66 : Fin 67)).val) + 23)
        (11 * (10 - (GroupedBalancedChecksum67.digit message (66 : Fin 67)).val) + 23)
        (10 - (GroupedBalancedChecksum67.digit message (66 : Fin 67)).val)
        (10 - (GroupedBalancedChecksum67.digit message (66 : Fin 67)).val)
        final ∧
      Done final base leaf start message values := by
  obtain ⟨copied,first,after,_⟩ := run_to_after_copy hash s
    base leaf start (66 : Fin 67) message values safe baseBound ready
  obtain ⟨second,next⟩ := after_copy_66 copied base leaf start
    message values after
  refine ⟨nextDoneState copied,?_,next⟩
  simp [GroupedBalancedChecksum67.maxDigit] at first
  convert first.trans second.trace using 1 <;> omega

theorem gap_at_eq (message : Reference.Digest)
    (i : Nat) (hi : i < 67) :
    gapAt message i =
      GroupedBalancedChecksum67.maxDigit ⟨i,hi⟩ -
        (GroupedBalancedChecksum67.digit message ⟨i,hi⟩).val := by
  simpa only [gapAt,chainAt_eq i hi]

theorem overhead_at_eq (i : Nat) (hi : i < 67) :
    overheadAt i =
      GroupedBalancedByteFastIteration67.overhead ⟨i,hi⟩ := by
  simpa only [overheadAt,chainAt_eq i hi]

def Invariant (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (i : Nat) (s : MachineState) : Prop :=
  if hi : i < 67 then
    Ready s base leaf start ⟨i,hi⟩ message values
  else
    i = 67 ∧ Done s base leaf start message values

theorem concrete_step (hash : Hash)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (i : Nat) (hi : i < 67) (s : MachineState)
    (inv : Invariant base leaf start message values i s) :
    ∃ final,
      Trace hash image s
        (stepsAt message i) (cyclesAt message i)
        (gapAt message i) (gapAt message i) final ∧
      Invariant base leaf start message values (i+1) final := by
  have ready : Ready s base leaf start ⟨i,hi⟩ message values := by
    simpa [Invariant,hi] using inv
  by_cases short : i < 64
  · obtain ⟨final,trace,next⟩ := step_short hash s base leaf start
      ⟨i,hi⟩ message values safe baseBound short ready
    have hnext : i+1 < 67 := by omega
    refine ⟨final,?_,?_⟩
    · have hgap := gap_at_eq message i hi
      have hover := overhead_at_eq i hi
      simpa [stepsAt,cyclesAt,hgap,hover,
        GroupedBalancedByteFastIteration67.overhead,short] using trace
    · simpa [Invariant,hnext] using next
  · have cases : i = 64 ∨ i = 65 ∨ i = 66 := by omega
    rcases cases with eq64 | eq65 | eq66
    · subst i
      obtain ⟨final,trace,next⟩ := step_64 hash s base leaf start
        message values safe baseBound (by simpa using ready)
      refine ⟨final,?_,?_⟩
      · simpa [stepsAt,cyclesAt,gap_at_eq,overhead_at_eq,
          GroupedBalancedByteFastIteration67.overhead,
          GroupedBalancedChecksum67.maxDigit] using trace
      · simpa [Invariant] using next
    · subst i
      obtain ⟨final,trace,next⟩ := step_65 hash s base leaf start
        message values safe baseBound (by simpa using ready)
      refine ⟨final,?_,?_⟩
      · simpa [stepsAt,cyclesAt,gap_at_eq,overhead_at_eq,
          GroupedBalancedByteFastIteration67.overhead,
          GroupedBalancedChecksum67.maxDigit] using trace
      · simpa [Invariant] using next
    · subst i
      obtain ⟨final,trace,done⟩ := step_66 hash s base leaf start
        message values safe baseBound (by simpa using ready)
      refine ⟨final,?_,?_⟩
      · simpa [stepsAt,cyclesAt,gap_at_eq,overhead_at_eq,
          GroupedBalancedByteFastIteration67.overhead,
          GroupedBalancedChecksum67.maxDigit] using trace
      · simpa [Invariant] using done

/-- Full concrete 67-chain WOTS execution from PC 0x1608 to PC 0x1684.
The exact cycle count includes every chain branch and hash call. -/
theorem all_wots (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (ready : Ready s base leaf start (0 : Fin 67) message values) :
    ∃ final,
      Trace hash image s
        (4 * GroupedBalancedChecksum67.suffixCost message + 1221)
        (11 * GroupedBalancedChecksum67.suffixCost message + 1221)
        (GroupedBalancedChecksum67.suffixCost message)
        (GroupedBalancedChecksum67.suffixCost message) final ∧
      Done final base leaf start message values := by
  have initial : Invariant base leaf start message values 0 s := by
    simpa [Invariant] using ready
  obtain ⟨final,trace,inv⟩ := fold_all hash image message
    (Invariant base leaf start message values) s initial
    (fun i hi s proof => concrete_step hash base leaf start message
      values safe baseBound i hi s proof)
  refine ⟨final,trace,?_⟩
  simpa [Invariant] using inv

#print axioms step_short
#print axioms step_64
#print axioms step_65
#print axioms step_66
#print axioms all_wots

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainConcrete67
