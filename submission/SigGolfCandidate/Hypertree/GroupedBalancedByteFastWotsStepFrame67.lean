import SigGolfCandidate.Hypertree.GroupedBalancedByteFastWotsProtected67

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastWotsStepFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedByteFastChainReady67
open GroupedBalancedByteFastChainEndpoints67
open GroupedBalancedByteFastChainConcrete67
open GroupedBalancedByteFastEndpointAccum67
open GroupedBalancedByteFastLimit67
open GroupedBalancedByteFastSuffixLoop67
open GroupedBalancedByteFastWotsProtected67
open GroupedBalancedByteFastChainFold67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem short_step_frame (hash : Hash)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (i : Nat) (hi : i < 67) (short : i < 64) (s : MachineState)
    (inv : StrongInvariant hash base leaf start message values i s)
    (a : Word) (safeAddr : Protected a) :
    ∃ final,
      Trace hash image s (stepsAt message i) (cyclesAt message i)
        (gapAt message i) (gapAt message i) final ∧
      StrongInvariant hash base leaf start message values (i+1) final ∧
      final.getMem a = s.getMem a := by
  have ready : StrongReady hash s base leaf start ⟨i,hi⟩
      message values := by
    simpa [StrongInvariant,hi] using inv
  obtain ⟨copied,first,after,current,frame⟩ :=
    run_to_after_copy hash s base leaf start ⟨i,hi⟩
      message values safe baseBound ready.1
  have endpoints := endpoint_words_copy hash s copied base leaf message
    values ⟨i,hi⟩ ready.1.outputPtr ready.2 current frame
  obtain ⟨second,next⟩ := after_copy_short copied base leaf start
      ⟨i,hi⟩ message values short after
  have hnext : i+1 < 67 := by omega
  refine ⟨advanceState copied,?_,?_,?_⟩
  · have hgap := gap_at_eq message i hi
    have hover := overhead_at_eq i hi
    simpa [stepsAt,cyclesAt,hgap,hover,
      GroupedBalancedByteFastIteration67.overhead,short] using
        first.trans (OrdinarySteps.trace (hash := hash) second)
  · have nextReady : StrongReady hash (advanceState copied) base leaf start
        ⟨i+1,hnext⟩ message values := ⟨next,
      endpoint_words_mem hash copied (advanceState copied) base leaf
        message values _ endpoints (advance_mem copied)⟩
    simpa [StrongInvariant,hnext] using nextReady
  · rw [advance_mem]
    exact copied_frame hash s copied base leaf start ⟨i,hi⟩
      message values ready.1 frame a safeAddr

#print axioms short_step_frame


theorem step64_frame (hash : Hash)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (s : MachineState)
    (inv : StrongInvariant hash base leaf start message values 64 s)
    (a : Word) (safeAddr : Protected a) :
    ∃ final,
      Trace hash image s (stepsAt message 64) (cyclesAt message 64)
        (gapAt message 64) (gapAt message 64) final ∧
      StrongInvariant hash base leaf start message values 65 final ∧
      final.getMem a = s.getMem a := by
  have ready : StrongReady hash s base leaf start (64 : Fin 67)
      message values := by simpa [StrongInvariant] using inv
  obtain ⟨copied,first,after,current,frame⟩ :=
    run_to_after_copy hash s base leaf start (64 : Fin 67)
      message values safe baseBound ready.1
  have endpoints := endpoint_words_copy hash s copied base leaf message
    values (64 : Fin 67) ready.1.outputPtr ready.2 current frame
  obtain ⟨second,next⟩ := after_copy_64 copied base leaf start
      message values after
  refine ⟨next65State copied,?_,?_,?_⟩
  · simp [GroupedBalancedChecksum67.maxDigit] at first
    simpa [stepsAt,cyclesAt,gap_at_eq,overhead_at_eq,
      GroupedBalancedByteFastIteration67.overhead,
      GroupedBalancedChecksum67.maxDigit] using
        first.trans (OrdinarySteps.trace (hash := hash) second)
  · have nextReady : StrongReady hash (next65State copied) base leaf start
        (65 : Fin 67) message values := ⟨next,
      endpoint_words_mem hash copied (next65State copied) base leaf
        message values _ endpoints (next65_mem copied)⟩
    simpa [StrongInvariant] using nextReady
  · rw [next65_mem]
    exact copied_frame hash s copied base leaf start (64 : Fin 67)
      message values ready.1 frame a safeAddr

#print axioms step64_frame
theorem step65_frame (hash : Hash)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (s : MachineState)
    (inv : StrongInvariant hash base leaf start message values 65 s)
    (a : Word) (safeAddr : Protected a) :
    ∃ final,
      Trace hash image s (stepsAt message 65) (cyclesAt message 65)
        (gapAt message 65) (gapAt message 65) final ∧
      StrongInvariant hash base leaf start message values 66 final ∧
      final.getMem a = s.getMem a := by
  have ready : StrongReady hash s base leaf start (65 : Fin 67)
      message values := by simpa [StrongInvariant] using inv
  obtain ⟨copied,first,after,current,frame⟩ :=
    run_to_after_copy hash s base leaf start (65 : Fin 67)
      message values safe baseBound ready.1
  have endpoints := endpoint_words_copy hash s copied base leaf message
    values (65 : Fin 67) ready.1.outputPtr ready.2 current frame
  obtain ⟨second,next⟩ := after_copy_65 copied base leaf start
      message values after
  refine ⟨next66State copied,?_,?_,?_⟩
  · simp [GroupedBalancedChecksum67.maxDigit] at first
    simpa [stepsAt,cyclesAt,gap_at_eq,overhead_at_eq,
      GroupedBalancedByteFastIteration67.overhead,
      GroupedBalancedChecksum67.maxDigit] using
        first.trans (OrdinarySteps.trace (hash := hash) second)
  · have nextReady : StrongReady hash (next66State copied) base leaf start
        (66 : Fin 67) message values := ⟨next,
      endpoint_words_mem hash copied (next66State copied) base leaf
        message values _ endpoints (next66_mem copied)⟩
    simpa [StrongInvariant] using nextReady
  · rw [next66_mem]
    exact copied_frame hash s copied base leaf start (65 : Fin 67)
      message values ready.1 frame a safeAddr

theorem step66_frame (hash : Hash)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (s : MachineState)
    (inv : StrongInvariant hash base leaf start message values 66 s)
    (a : Word) (safeAddr : Protected a) :
    ∃ final,
      Trace hash image s (stepsAt message 66) (cyclesAt message 66)
        (gapAt message 66) (gapAt message 66) final ∧
      StrongInvariant hash base leaf start message values 67 final ∧
      final.getMem a = s.getMem a := by
  have ready : StrongReady hash s base leaf start (66 : Fin 67)
      message values := by simpa [StrongInvariant] using inv
  obtain ⟨copied,first,after,current,frame⟩ :=
    run_to_after_copy hash s base leaf start (66 : Fin 67)
      message values safe baseBound ready.1
  have endpoints := endpoint_words_copy hash s copied base leaf message
    values (66 : Fin 67) ready.1.outputPtr ready.2 current frame
  obtain ⟨second,next⟩ := after_copy_66 copied base leaf start
      message values after
  refine ⟨nextDoneState copied,?_,?_,?_⟩
  · simp [GroupedBalancedChecksum67.maxDigit] at first
    simpa [stepsAt,cyclesAt,gap_at_eq,overhead_at_eq,
      GroupedBalancedByteFastIteration67.overhead,
      GroupedBalancedChecksum67.maxDigit] using
        first.trans (OrdinarySteps.trace (hash := hash) second)
  · have nextDone : StrongDone hash (nextDoneState copied) base leaf start
        message values := ⟨next,
      endpoint_words_mem hash copied (nextDoneState copied) base leaf
        message values _ endpoints (next_done_mem copied)⟩
    simpa [StrongInvariant] using nextDone
  · rw [next_done_mem]
    exact copied_frame hash s copied base leaf start (66 : Fin 67)
      message values ready.1 frame a safeAddr

#print axioms step65_frame
#print axioms step66_frame

/-- One WOTS chain leaves the low sibling area and high caller area unchanged. -/
theorem strong_step_frame (hash : Hash)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (i : Nat) (hi : i < 67) (s : MachineState)
    (inv : StrongInvariant hash base leaf start message values i s)
    (a : Word) (safeAddr : Protected a) :
    ∃ final,
      Trace hash image s (stepsAt message i) (cyclesAt message i)
        (gapAt message i) (gapAt message i) final ∧
      StrongInvariant hash base leaf start message values (i+1) final ∧
      final.getMem a = s.getMem a := by
  by_cases short : i < 64
  · exact short_step_frame hash base leaf start message values
      safe baseBound i hi short s inv a safeAddr
  · have cases : i = 64 ∨ i = 65 ∨ i = 66 := by omega
    rcases cases with eq64 | eq65 | eq66
    · subst i
      exact step64_frame hash base leaf start message values
        safe baseBound s inv a safeAddr
    · subst i
      exact step65_frame hash base leaf start message values
        safe baseBound s inv a safeAddr
    · subst i
      exact step66_frame hash base leaf start message values
        safe baseBound s inv a safeAddr

#print axioms strong_step_frame
end SigGolfCandidate.Hypertree.GroupedBalancedByteFastWotsStepFrame67
