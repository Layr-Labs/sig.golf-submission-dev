import SigGolfCandidate.Hypertree.VerifyLeafState

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

def recoveredEndpoint (hash : Hash) (level tree : Nat) (side : Bool) (message : Reference.Digest)
    (values : Reference.Chain → Reference.Digest) (chain : Reference.Chain) : Reference.Digest :=
  walk (Reference.chainHash hash level tree side chain) (Reference.digit message chain).val
    (7-(Reference.digit message chain).val) (values chain)

/-- The endpoint-store composition for a hoisted chain fragment.
The concrete fragment proof supplies the witness-loading and HASH trace. -/
theorem leaf_step_fast_core (hash : Hash) (s : MachineState) (level tree : Nat)
    (side : Bool) (base : Nat) (message : Reference.Digest)
    (values : Reference.Chain → Reference.Digest) (chain : Reference.Chain)
    (data : LeafData s level tree side base message values)
    (_aligned : base % 8 = 0) (bound : base+736 ≤ 0x80000)
    (fragment : ∃ recovered steps cycles calls,
      Trace hash verify s steps cycles calls calls recovered ∧
      steps ≤ cycles ∧
      cycles ≤ 11*calls+22+(if chain.val=0 then 49 else 0) ∧
      calls = 7-(Reference.digit message chain).val ∧
      recovered.pc = 0x163c ∧
      recovered.getMem 0x80430 = BitVec.ofNat 64 chain.val ∧
      (∀ i : Fin 2, recovered.getMem (wordAddress 0x80020 i.val) =
        (recoveredEndpoint hash level tree side message values chain).extractLsb' (64*i.val) 64) ∧
      Hoist.HeaderWordCarry recovered level tree (Reference.sideNumber side) ∧
      recovered.getReg .x1 = s.getReg .x1 ∧
      recovered.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → recovered.getMem a = s.getMem a)) :
    ∃ final steps cycles calls, Trace hash verify s steps cycles calls calls final ∧
      steps ≤ cycles ∧
      cycles ≤ 11*calls+37+(if chain.val=0 then 49 else 0) ∧
      calls = 7-(Reference.digit message chain).val ∧
      ChainEntry final (chain.val+1) ∧
      final.getMem 0x80430 = BitVec.ofNat 64 (chain.val+1) ∧
      LeafData final level tree side base message values ∧
      (∀ i : Fin 2, final.getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
        (recoveredEndpoint hash level tree side message values chain).extractLsb' (64*i.val) 64) ∧
      Hoist.HeaderWordCarry final level tree (Reference.sideNumber side) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → a ≠ 0x80430 →
        (∀ i : Fin 2, a ≠ KeygenEndpoint.endpointAddress chain.val i.val) →
        final.getMem a = s.getMem a) := by
  obtain ⟨recovered, fragSteps, fragCycles, fragCalls, frag, fragStepBound,
    fragCycleBound, fragCallsEq, recoveredPC, recoveredCounter, words, carry,
    recoveredRA, recoveredSP, recoveredFrame⟩ := fragment
  obtain ⟨final, store, finalEntry, finalCounter, endpoints, storeRA, storeSP,
    storeFrame, finalCarry⟩ :=
    store_endpoint_with_word_carry recovered level tree (Reference.sideNumber side)
      chain (recoveredEndpoint hash level tree side message values chain)
      recoveredPC recoveredCounter words carry
  have frame (a : Word) (outside : OutsideChainWork a) (notCounter : a ≠ 0x80430)
      (notEndpoint : ∀ i : Fin 2, a ≠ KeygenEndpoint.endpointAddress chain.val i.val) :
      final.getMem a = s.getMem a :=
    (storeFrame a notCounter notEndpoint).trans (recoveredFrame a outside)
  refine ⟨final, fragSteps+15, fragCycles+15, fragCalls, frag.trans store.trace,
    by omega, by omega, fragCallsEq, finalEntry, finalCounter, ?_, endpoints,
    finalCarry, storeRA.trans recoveredRA, storeSP.trans recoveredSP, frame⟩
  exact data.transfer s final level tree side base message values bound (fun a outside =>
    frame a (outside_leaf_chain a outside) outside.2.2.2.2.1
      (outside_leaf_endpoint a outside chain))

/-- One certified verifier chain, including the endpoint store and reusable header. -/
theorem leaf_step_fast (hash : Hash) (s : MachineState) (level tree : Nat)
    (side : Bool) (base : Nat) (message : Reference.Digest)
    (values : Reference.Chain → Reference.Digest) (chain : Reference.Chain)
    (small : level < 256)
    (entry : ChainEntry s chain.val)
    (data : LeafData s level tree side base message values)
    (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (ready : Hoist.HeaderReadyWord s level tree (Reference.sideNumber side) chain.val)
    (aligned : base % 8 = 0) (bound : base+736 ≤ 0x80000) :
    ∃ final steps cycles calls, Trace hash verify s steps cycles calls calls final ∧
      steps ≤ cycles ∧
      cycles ≤ 11*calls+37+(if chain.val=0 then 49 else 0) ∧
      calls = 7-(Reference.digit message chain).val ∧
      ChainEntry final (chain.val+1) ∧
      final.getMem 0x80430 = BitVec.ofNat 64 (chain.val+1) ∧
      LeafData final level tree side base message values ∧
      (∀ i : Fin 2, final.getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
        (recoveredEndpoint hash level tree side message values chain).extractLsb' (64*i.val) 64) ∧
      Hoist.HeaderWordCarry final level tree (Reference.sideNumber side) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → a ≠ 0x80430 →
        (∀ i : Fin 2, a ≠ KeygenEndpoint.endpointAddress chain.val i.val) →
        final.getMem a = s.getMem a) := by
  have safe := chainSource_safe s base chain data.pointerEq counter aligned (by
    have := chain.isLt
    simp only [MEMORY_BYTES]
    omega)
  have source := chainSource_eq s base chain data.pointerEq counter
  have value0 : s.getMem (chainSourceFast s) =
      (values chain).extractLsb' 0 64 := by
    rw [source]
    simpa only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] using data.valueEq chain 0
  have value8 : s.getMem (chainSourceFast s+8) =
      (values chain).extractLsb' 64 64 := by
    rw [source]
    have add : BitVec.ofNat 64 (base+16*chain.val)+8 =
        BitVec.ofNat 64 (base+16*chain.val+8) :=
      (BitVec.ofNat_add _ _).symm
    rw [add]
    simpa only [Fin.val_one,Nat.mul_one] using data.valueEq chain 1
  have fragment := recover_chain_fragment_fast hash s level tree side chain
    (Reference.digit message chain) (values chain) small entry safe.1 safe.2
    data.levelEq data.leafEq counter data.indexEq value0 value8
    (data.digitEq chain) ready
  exact leaf_step_fast_core hash s level tree side base message values chain
    data aligned bound fragment

/-- info: 'SigGolfCandidate.Hypertree.Verifying.leaf_step_fast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leaf_step_fast

end SigGolfCandidate.Hypertree.Verifying
