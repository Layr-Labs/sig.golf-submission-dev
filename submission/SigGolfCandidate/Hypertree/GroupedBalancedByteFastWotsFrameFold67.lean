import SigGolfCandidate.Hypertree.GroupedBalancedByteFastWotsProtected67

/-! The whole 67-chain loop preserves protected caller memory. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastWotsFrameFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedByteFastChainReady67
open GroupedBalancedByteFastChainEndpoints67
open GroupedBalancedByteFastChainFold67
open GroupedBalancedByteFastWotsProtected67
open GroupedBalancedByteFastSuffixLoop67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem one_address_of_step (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (ready : Ready s base leaf start (0 : Fin 67) message values)
    (a : Word) (safeAddr : Protected a)
    (stepFrame : ∀ i : Nat, i < 67 → ∀ t : MachineState,
      StrongInvariant hash base leaf start message values i t →
      ∃ u : MachineState,
        Trace hash image t (stepsAt message i) (cyclesAt message i)
          (gapAt message i) (gapAt message i) u ∧
        StrongInvariant hash base leaf start message values (i+1) u ∧
        u.getMem a = t.getMem a) :
    ∃ final,
      Trace hash image s
        (4 * GroupedBalancedChecksum67.suffixCost message + 1221)
        (11 * GroupedBalancedChecksum67.suffixCost message + 1221)
        (GroupedBalancedChecksum67.suffixCost message)
        (GroupedBalancedChecksum67.suffixCost message) final ∧
      StrongDone hash final base leaf start message values ∧
      final.getMem a = s.getMem a := by
  let P (i : Nat) (t : MachineState) : Prop :=
    StrongInvariant hash base leaf start message values i t ∧
    t.getMem a = s.getMem a
  have initial : P 0 s := by
    constructor
    · simpa [StrongInvariant,StrongReady] using
        And.intro ready
          (GroupedBalancedByteFastEndpointAccum67.initial_endpoints
            hash s base leaf message values)
    · rfl
  have step : ∀ i : Nat, i < 67 → ∀ t : MachineState, P i t →
      ∃ u : MachineState,
        Trace hash image t (stepsAt message i) (cyclesAt message i)
          (gapAt message i) (gapAt message i) u ∧ P (i+1) u := by
    intro i hi t p
    obtain ⟨u,trace,next,frame⟩ := stepFrame i hi t p.1
    exact ⟨u,trace,next,frame.trans p.2⟩
  obtain ⟨final,trace,inv,frame⟩ :=
    fold_all hash image message P s initial step
  refine ⟨final,trace,?_,frame⟩
  simpa [StrongInvariant] using inv

theorem all_addresses_of_step (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (ready : Ready s base leaf start (0 : Fin 67) message values)
    (stepFrame : ∀ (a : Word), Protected a →
      ∀ i : Nat, i < 67 → ∀ t : MachineState,
      StrongInvariant hash base leaf start message values i t →
      ∃ u : MachineState,
        Trace hash image t (stepsAt message i) (cyclesAt message i)
          (gapAt message i) (gapAt message i) u ∧
        StrongInvariant hash base leaf start message values (i+1) u ∧
        u.getMem a = t.getMem a) :
    ∃ final,
      Trace hash image s
        (4 * GroupedBalancedChecksum67.suffixCost message + 1221)
        (11 * GroupedBalancedChecksum67.suffixCost message + 1221)
        (GroupedBalancedChecksum67.suffixCost message)
        (GroupedBalancedChecksum67.suffixCost message) final ∧
      StrongDone hash final base leaf start message values ∧
      (∀ a : Word, Protected a → final.getMem a = s.getMem a) := by
  obtain ⟨final,trace,done⟩ := all_wots_endpoints hash s
    base leaf start message values safe baseBound ready
  refine ⟨final,trace,done,?_⟩
  intro a safeAddr
  obtain ⟨other,otherTrace,_,frame⟩ := one_address_of_step hash s
    base leaf start message values safe baseBound ready a safeAddr
      (stepFrame a safeAddr)
  have same : final = other := Trace.deterministic trace otherTrace
  rw [same]
  exact frame

#print axioms one_address_of_step
#print axioms all_addresses_of_step
end SigGolfCandidate.Hypertree.GroupedBalancedByteFastWotsFrameFold67
