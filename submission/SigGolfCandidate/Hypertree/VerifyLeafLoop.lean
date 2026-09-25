import SigGolfCandidate.Hypertree.VerifyLeafStep
import SigGolfCandidate.Hypertree.VerifyHoistWord
import SigGolfCandidate.Hypertree.GroupedBalanced

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

/-- Remaining HASH calls in a prefix of the 46 verifier chains. -/
def chainPrefixFast (message : Reference.Digest) (count : Nat) : Nat :=
  ∑ i ∈ Finset.range count,
    (7-(Reference.digit message ⟨i%46, Nat.mod_lt _ (by decide)⟩).val)

theorem chainPrefixFast_zero (message : Reference.Digest) :
    chainPrefixFast message 0 = 0 := by simp [chainPrefixFast]

theorem chainPrefixFast_succ (message : Reference.Digest) (n : Nat) (bound : n < 46) :
    chainPrefixFast message (n+1) =
      chainPrefixFast message n + (7-(Reference.digit message ⟨n,bound⟩).val) := by
  simp [chainPrefixFast, Finset.sum_range_succ, Nat.mod_eq_of_lt bound]

theorem chainPrefixFast_message (message : Reference.Digest) :
    chainPrefixFast message 43 = Reference.checksum message := by
  unfold chainPrefixFast Reference.checksum
  rw [← Fin.sum_univ_eq_sum_range]
  have terms : (∑ i : Fin 43,
      (7 - (Reference.digit message ⟨i.val % 46, Nat.mod_lt _ (by decide)⟩).val)) =
      ∑ i : Fin 43, (7 - Reference.payloadDigit message i) := by
    apply Finset.sum_congr rfl
    intro i _
    have hi : Reference.payloadDigit message i < 8 := by
      exact Balanced.payload_digit_lt_eight message i
    simp [Reference.digit, Nat.mod_eq_of_lt (by omega : i.val < 46),
      Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt hi]
  rw [terms, Finset.sum_tsub_distrib]
  · simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, Reference.payloadSum]
    rfl
  · intro i _
    have hi : Reference.payloadDigit message i < 8 := by
      exact Balanced.payload_digit_lt_eight message i
    omega

theorem chainPrefixFast_bound_balanced (message : Reference.Digest) :
    chainPrefixFast message 46 ≤ 161 := by
  change Balanced.chainPrefix message 46 ≤ 161
  exact Balanced.chain_prefix_bound message

theorem chainPrefixFast_bound (message : Reference.Digest) :
    chainPrefixFast message 46 ≤ 308 := by
  have bound := chainPrefixFast_bound_balanced message
  omega

def EndpointPrefix (s : MachineState) (values : Reference.Chain → Reference.Digest) (n : Nat) : Prop :=
  ∀ chain : Reference.Chain, chain.val < n → ∀ i : Fin 2,
    s.getMem (KeygenEndpoint.endpointAddress chain.val i.val) = (values chain).extractLsb' (64*i.val) 64

/-- Composes any certified hoisted chain step across all remaining chains.
The local step hypothesis is discharged by the concrete RISC-V proof below. -/
theorem leaf_loop_fast_core (hash : Hash) (s : MachineState) (level tree : Nat)
    (side : Bool) (base : Nat) (message : Reference.Digest)
    (values : Reference.Chain → Reference.Digest) (start remaining : Nat)
    (length : start+remaining = 46)
    (pc : s.pc = if start = 46 then 0x1690 else 0x1490)
    (data : LeafData s level tree side base message values)
    (counter : s.getMem 0x80430 = BitVec.ofNat 64 start)
    (completed : EndpointPrefix s (recoveredEndpoint hash level tree side message values) start)
    (ready : Hoist.HeaderReadyWord s level tree (Reference.sideNumber side) start)
    (stepHyp : ∀ (t : MachineState) (chain : Reference.Chain),
      t.pc = 0x1490 →
      LeafData t level tree side base message values →
      t.getMem 0x80430 = BitVec.ofNat 64 chain.val →
      Hoist.HeaderReadyWord t level tree (Reference.sideNumber side) chain.val →
      ∃ next steps cycles calls,
        Trace hash verify t steps cycles calls calls next ∧
        steps ≤ cycles ∧
        cycles ≤ 11*calls+45+(if chain.val = 0 then 47 else 0) ∧
        calls = 7-(Reference.digit message chain).val ∧
        next.pc = (if chain.val+1 = 46 then 0x1690 else 0x1490) ∧
        next.getMem 0x80430 = BitVec.ofNat 64 (chain.val+1) ∧
        LeafData next level tree side base message values ∧
        (∀ i : Fin 2, next.getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
          (recoveredEndpoint hash level tree side message values chain).extractLsb' (64*i.val) 64) ∧
        Hoist.HeaderWordCarry next level tree (Reference.sideNumber side) ∧
        next.getReg .x1 = t.getReg .x1 ∧ next.getReg .x2 = t.getReg .x2 ∧
        (∀ a, OutsideChainWork a → a ≠ 0x80430 →
          (∀ i : Fin 2, a ≠ KeygenEndpoint.endpointAddress chain.val i.val) →
          next.getMem a = t.getMem a)) :
    ∃ final steps cycles calls, Trace hash verify s steps cycles calls calls final ∧
      steps ≤ cycles ∧
      cycles ≤ 11*calls+45*remaining+(if start = 0 then 47 else 0) ∧
      calls + chainPrefixFast message start = chainPrefixFast message 46 ∧
      final.pc = 0x1690 ∧ final.getMem 0x80430 = 46 ∧
      LeafData final level tree side base message values ∧
      EndpointPrefix final (recoveredEndpoint hash level tree side message values) 46 ∧
      Hoist.HeaderWordCarry final level tree (Reference.sideNumber side) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideLeafWork a → final.getMem a = s.getMem a) := by
  induction remaining generalizing s start with
  | zero =>
    have startEq : start = 46 := by omega
    subst start
    have carry : Hoist.HeaderWordCarry s level tree (Reference.sideNumber side) := by
      rcases ready with h | h
      · omega
      · exact h
    refine ⟨s, 0, 0, 0, Trace.refl s, by omega, by simp, ?_, ?_, ?_,
      data, completed, carry, rfl, rfl, ?_⟩
    · simp [chainPrefixFast]
    · simpa using pc
    · exact counter
    · intro _ _; rfl
  | succ remaining ih =>
    have startLt : start < 46 := by omega
    let chain : Reference.Chain := ⟨start, startLt⟩
    have atLoop : s.pc = 0x1490 := by
      simpa only [if_neg (by omega : start ≠ 46)] using pc
    obtain ⟨next, preSteps, preCycles, preCalls, pre, preStepBound, preCycleBound,
      preCallsEq, nextPC, nextCounter, nextData, output, nextCarry, nextRA, nextSP,
      nextFrame⟩ :=
      stepHyp s chain atLoop data counter ready
    have nextReady : Hoist.HeaderReadyWord next level tree (Reference.sideNumber side) (start+1) :=
      Or.inr nextCarry
    have nextPrefix : EndpointPrefix next (recoveredEndpoint hash level tree side message values) (start+1) := by
      intro c hc i
      by_cases same : c.val = start
      · have eq : c = chain := Fin.ext same
        subst c
        exact output i
      · have before : c.val < start := by omega
        have neCounter : KeygenEndpoint.endpointAddress c.val i.val ≠ 0x80430 := by
          intro eq
          have h := congrArg BitVec.toNat eq
          have hc := c.isLt
          have hi := i.isLt
          change (0x80800+16*c.val+8*i.val) % 2^64 = 0x80430 at h
          omega
        rw [nextFrame _ (endpoint_outside_chain c i) neCounter]
        · exact completed c before i
        · intro j
          exact endpointAddress_ne c chain i j (fun eq => same (congrArg Fin.val eq))
    obtain ⟨final, tailSteps, tailCycles, tailCalls, tail, tailStepBound, tailCycleBound,
      tailCallsEq, finalPC, finalCounter, finalData, finalPrefix, finalCarry,
      finalRA, finalSP, finalFrame⟩ :=
      ih next (start+1) (by omega) nextPC nextData nextCounter nextPrefix nextReady
    have noTailSurcharge : start+1 ≠ 0 := by omega
    simp only [if_neg noTailSurcharge] at tailCycleBound
    have callsEq : preCalls = 7-(Reference.digit message chain).val := preCallsEq
    have prefixSucc := chainPrefixFast_succ message start startLt
    rw [prefixSucc] at tailCallsEq
    refine ⟨final, preSteps+tailSteps, preCycles+tailCycles, preCalls+tailCalls,
      pre.trans tail, by omega, ?_, ?_, finalPC, finalCounter, finalData,
      finalPrefix, finalCarry, finalRA.trans nextRA, finalSP.trans nextSP, ?_⟩
    · change preCycles ≤ 11*preCalls+45+(if start=0 then 47 else 0) at preCycleBound
      omega
    · change preCalls = 7-(Reference.digit message ⟨start,startLt⟩).val at callsEq
      omega
    · intro a outside
      exact (finalFrame a outside).trans (nextFrame a (outside_leaf_chain a outside)
        outside.2.2.2.2.1 (outside_leaf_endpoint a outside chain))

/-- info: 'SigGolfCandidate.Hypertree.Verifying.leaf_loop_fast_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leaf_loop_fast_core

/-- A local verifier chain theorem strong enough for exact cross-chain accounting. -/
def FastLeafStepSpec (hash : Hash) (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (values : Reference.Chain → Reference.Digest) : Prop :=
  ∀ (t : MachineState) (chain : Reference.Chain),
    t.pc = 0x1490 →
    LeafData t level tree side base message values →
    t.getMem 0x80430 = BitVec.ofNat 64 chain.val →
    Hoist.HeaderReadyWord t level tree (Reference.sideNumber side) chain.val →
    ∃ next steps cycles calls,
      Trace hash verify t steps cycles calls calls next ∧
      steps ≤ cycles ∧
      cycles ≤ 11*calls+45+(if chain.val = 0 then 47 else 0) ∧
      calls = 7-(Reference.digit message chain).val ∧
      next.pc = (if chain.val+1 = 46 then 0x1690 else 0x1490) ∧
      next.getMem 0x80430 = BitVec.ofNat 64 (chain.val+1) ∧
      LeafData next level tree side base message values ∧
      (∀ i : Fin 2, next.getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
        (recoveredEndpoint hash level tree side message values chain).extractLsb' (64*i.val) 64) ∧
      Hoist.HeaderWordCarry next level tree (Reference.sideNumber side) ∧
      next.getReg .x1 = t.getReg .x1 ∧ next.getReg .x2 = t.getReg .x2 ∧
      (∀ a, OutsideChainWork a → a ≠ 0x80430 →
        (∀ i : Fin 2, a ≠ KeygenEndpoint.endpointAddress chain.val i.val) →
        next.getMem a = t.getMem a)

/-- Exact full-leaf accounting follows from one reusable chain theorem. -/
theorem recover_all_chains_fast_core (hash : Hash) (s : MachineState)
    (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (values : Reference.Chain → Reference.Digest)
    (pc : s.pc = 0x1490) (data : LeafData s level tree side base message values)
    (counter : s.getMem 0x80430 = 0)
    (stepHyp : FastLeafStepSpec hash level tree side base message values) :
    ∃ final steps cycles calls, Trace hash verify s steps cycles calls calls final ∧
      steps ≤ cycles ∧ cycles ≤ 11*calls+2117 ∧ calls ≤ 308 ∧
      calls = chainPrefixFast message 46 ∧
      final.pc = 0x1690 ∧ final.getMem 0x80430 = 46 ∧
      LeafData final level tree side base message values ∧
      (∀ chain : Reference.Chain, ∀ i : Fin 2,
        final.getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
          (recoveredEndpoint hash level tree side message values chain).extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideLeafWork a → final.getMem a = s.getMem a) := by
  obtain ⟨final, steps, cycles, calls, run, hsteps, hcycles, hexact, finalPC,
    finalCounter, finalData, endpoints, _, finalRA, finalSP, frame⟩ :=
    leaf_loop_fast_core hash s level tree side base message values 0 46 rfl pc
      data counter (by intro c hc; omega) (Or.inl rfl) stepHyp
  have exactCalls : calls = chainPrefixFast message 46 := by
    simpa only [chainPrefixFast_zero, Nat.add_zero] using hexact
  refine ⟨final, steps, cycles, calls, run, hsteps, ?_, ?_, exactCalls,
    finalPC, finalCounter, finalData, fun c => endpoints c c.isLt,
    finalRA, finalSP, frame⟩
  · norm_num at hcycles
    exact hcycles
  · rw [exactCalls]
    exact chainPrefixFast_bound message

/-- info: 'SigGolfCandidate.Hypertree.Verifying.recover_all_chains_fast_core' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms recover_all_chains_fast_core

/-- Exact ordered endpoint recovery with the hoisted verifier header. -/
theorem recover_all_chains_fast (hash : Hash) (s : MachineState)
    (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (values : Reference.Chain → Reference.Digest)
    (small : level < 160)
    (pc : s.pc = 0x1490) (data : LeafData s level tree side base message values)
    (counter : s.getMem 0x80430 = 0)
    (aligned : base % 8 = 0) (bound : base+736 ≤ 0x80000) :
    ∃ final steps cycles calls, Trace hash verify s steps cycles calls calls final ∧
      steps ≤ cycles ∧ cycles ≤ 11*calls+2117 ∧ calls ≤ 308 ∧
      calls = chainPrefixFast message 46 ∧
      final.pc = 0x1690 ∧ final.getMem 0x80430 = 46 ∧
      LeafData final level tree side base message values ∧
      (∀ chain : Reference.Chain, ∀ i : Fin 2,
        final.getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
          (recoveredEndpoint hash level tree side message values chain).extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideLeafWork a → final.getMem a = s.getMem a) := by
  have stepHyp : FastLeafStepSpec hash level tree side base message values := by
    intro t chain tPC tData tCounter tReady
    exact leaf_step_fast hash t level tree side base message values chain
      (by omega) tPC tData tCounter tReady aligned bound
  exact recover_all_chains_fast_core hash s level tree side base message values
    pc data counter stepHyp

/-- The original loose resource interface follows from the sharper certificate. -/
theorem recover_all_chains (hash : Hash) (s : MachineState)
    (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (values : Reference.Chain → Reference.Digest)
    (small : level < 160)
    (pc : s.pc = 0x1490) (data : LeafData s level tree side base message values)
    (counter : s.getMem 0x80430 = 0)
    (aligned : base % 8 = 0) (bound : base+736 ≤ 0x80000) :
    ∃ final steps cycles calls, Trace hash verify s steps cycles calls calls final ∧
      steps ≤ 33166 ∧ cycles ≤ 35420 ∧ calls ≤ 322 ∧ final.pc = 0x1690 ∧
      final.getMem 0x80430 = 46 ∧ LeafData final level tree side base message values ∧
      (∀ chain : Reference.Chain, ∀ i : Fin 2,
        final.getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
          (recoveredEndpoint hash level tree side message values chain).extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideLeafWork a → final.getMem a = s.getMem a) := by
  obtain ⟨final,steps,cycles,calls,run,hsteps,hcycles,hcalls,_,finalPC,
    finalCounter,finalData,endpoints,finalRA,finalSP,frame⟩ :=
    recover_all_chains_fast hash s level tree side base message values
      small pc data counter aligned bound
  exact ⟨final,steps,cycles,calls,run,by omega,by omega,by omega,
    finalPC,finalCounter,finalData,endpoints,finalRA,finalSP,frame⟩

/-- info: 'SigGolfCandidate.Hypertree.Verifying.recover_all_chains_fast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms recover_all_chains_fast

end SigGolfCandidate.Hypertree.Verifying
