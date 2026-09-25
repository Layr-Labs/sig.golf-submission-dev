import SigGolfCandidate.Hypertree.EndpointStore
import SigGolfCandidate.Hypertree.VerifyChainRecovery
import SigGolfCandidate.Hypertree.VerifyHoistHeader
import SigGolfCandidate.Hypertree.VerifyHoistWord

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing

/-- The shared endpoint-store theorem instantiated for the verifier’s chain loop. -/
theorem store_endpoint (s : MachineState) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x163c) (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (valueWords : ∀ i : Fin 2, s.getMem (wordAddress 0x80020 i.val) = value.extractLsb' (64*i.val) 64) :
    ∃ final, OrdinarySteps verify s 21 final ∧
      final.pc = (if chain.val+1 = 46 then 0x1690 else 0x1490) ∧
      final.getMem 0x80430 = BitVec.ofNat 64 (chain.val+1) ∧
      (∀ i : Fin 2, final.getMem (KeygenEndpoint.endpointAddress chain.val i.val) = value.extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, a ≠ 0x80430 → (∀ i : Fin 2, a ≠ KeygenEndpoint.endpointAddress chain.val i.val) → final.getMem a = s.getMem a) := by
  have src0 : ((0x80000 : Word) + signExtend12 (32 : BitVec 12)) =
      wordAddress 0x80020 0 := by decide
  have src8 : ((0x80000 : Word) + signExtend12 (40 : BitVec 12)) =
      wordAddress 0x80020 1 := by decide
  exact KeygenEndpoint.store_endpoint_at verify 0x163c (-508) 32 40 (by decide)
    s chain value pc counter (by decide) (by decide)
    (by rw [src0]; exact valueWords 0) (by rw [src8]; exact valueWords 1)

/-- The endpoint store leaves the persistent HASH header and sticky registers intact. -/
theorem endpoint_header_carry (s template : MachineState)
    (chain : Reference.Chain) (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (carry : Hoist.HeaderCarry s template) :
    Hoist.HeaderCarry (KeygenEndpoint.stateAt s (-508) 32 40) template := by
  let final := KeygenEndpoint.stateAt s (-508) 32 40
  have frame (j : Nat) (hj : j < 4) :
      final.getMem (wordAddress 0x80000 j) = s.getMem (wordAddress 0x80000 j) := by
    rw [KeygenEndpoint.memAt]
    have counterNe : wordAddress 0x80000 j ≠ 0x80430 := by
      intro same
      have h := congrArg BitVec.toNat same
      change (0x80000+8*j) % 2^64 = 0x80430 at h
      omega
    have endpointNe (i : Fin 2) :
        wordAddress 0x80000 j ≠ KeygenEndpoint.endpointAddress chain.val i.val := by
      intro same
      have h := congrArg BitVec.toNat same
      change (0x80000+8*j) % 2^64 =
        (0x80800+16*chain.val+8*i.val) % 2^64 at h
      have hc := chain.isLt
      have hi := i.isLt
      omega
    have addr := KeygenEndpoint.address_eq s chain.val counter
    rw [if_neg counterNe, addr]
    have h0 : wordAddress 0x80000 j ≠ BitVec.ofNat 64 (0x80800+16*chain.val) := by
      simpa [KeygenEndpoint.endpointAddress] using
        endpointNe (0 : Fin 2)
    have h1 : wordAddress 0x80000 j ≠ BitVec.ofNat 64 (0x80800+16*chain.val)+8 := by
      have addr8 : BitVec.ofNat 64 (0x80800+16*chain.val)+8 =
          KeygenEndpoint.endpointAddress chain.val 1 := by
        simp [KeygenEndpoint.endpointAddress, BitVec.ofNat_add, Nat.add_comm]
        ac_rfl
      rw [addr8]
      exact endpointNe 1
    rw [if_neg h1, if_neg h0]
  rcases carry with ⟨fixed, service, destination, seven⟩
  obtain ⟨r5, r12, r31⟩ := KeygenEndpoint.stickyRegsAt s (-508) 32 40
  refine ⟨?_, r5.trans service, r12.trans destination, r31.trans seven⟩
  intro a notChain notStep upper lower
  let i := a.toNat - 0x80000
  have hi : i < 32 := by dsimp [i]; omega
  have addr : a = BitVec.ofNat 64 (0x80000+i) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    dsimp [i]
    omega
  have bytes := Signing.bytes_eq_of_words s final 0x80000 0x80000 32
    (by decide) (by decide) (by omega) (by omega) frame i hi
  rw [← addr] at bytes
  exact bytes.trans (fixed a notChain notStep upper lower)

/-- Endpoint storage together with the persistent header invariant for the next chain. -/
theorem store_endpoint_with_carry (s template : MachineState)
    (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x163c) (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (valueWords : ∀ i : Fin 2,
      s.getMem (wordAddress 0x80020 i.val) = value.extractLsb' (64*i.val) 64)
    (carry : Hoist.HeaderCarry s template) :
    ∃ final, OrdinarySteps verify s 21 final ∧
      final.pc = (if chain.val+1 = 46 then 0x1690 else 0x1490) ∧
      final.getMem 0x80430 = BitVec.ofNat 64 (chain.val+1) ∧
      (∀ i : Fin 2, final.getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
        value.extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, a ≠ 0x80430 → (∀ i : Fin 2,
        a ≠ KeygenEndpoint.endpointAddress chain.val i.val) → final.getMem a = s.getMem a) ∧
      Hoist.HeaderCarry final template := by
  have src0 : ((0x80000 : Word) + signExtend12 (32 : BitVec 12)) =
      wordAddress 0x80020 0 := by decide
  have src8 : ((0x80000 : Word) + signExtend12 (40 : BitVec 12)) =
      wordAddress 0x80020 1 := by decide
  let final := KeygenEndpoint.stateAt s (-508) 32 40
  obtain ⟨run, finalPC, finalCounter, endpoints, ra, sp, frame⟩ :=
    KeygenEndpoint.store_endpoint_at_state verify 0x163c (-508) 32 40 (by decide)
      s chain value pc counter (by decide) (by decide)
      (by rw [src0]; exact valueWords 0) (by rw [src8]; exact valueWords 1)
  exact ⟨final, run, by
    simpa only [show (0x163c : Word)+84=0x1690 by decide,
      show (0x163c : Word)+80+signExtend13 (-508 : BitVec 13)=0x1490 by decide]
      using finalPC, finalCounter, endpoints,
    ra, sp, frame, endpoint_header_carry s template chain counter carry⟩

private theorem endpoint_header_word_frame (s : MachineState) (chain : Reference.Chain)
    (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (j : Nat) (hj : j < 4) :
    (KeygenEndpoint.stateAt s (-508) 32 40).getMem (wordAddress 0x80000 j) =
      s.getMem (wordAddress 0x80000 j) := by
  rw [KeygenEndpoint.memAt]
  have counterNe : wordAddress 0x80000 j ≠ 0x80430 := by
    intro same
    have h := congrArg BitVec.toNat same
    change (0x80000+8*j) % 2^64 = 0x80430 at h
    omega
  have endpointNe (i : Fin 2) :
      wordAddress 0x80000 j ≠ KeygenEndpoint.endpointAddress chain.val i.val := by
    intro same
    have h := congrArg BitVec.toNat same
    change (0x80000+8*j) % 2^64 =
      (0x80800+16*chain.val+8*i.val) % 2^64 at h
    have hc := chain.isLt
    have hi := i.isLt
    omega
  have addr := KeygenEndpoint.address_eq s chain.val counter
  rw [if_neg counterNe, addr]
  have h0 : wordAddress 0x80000 j ≠ BitVec.ofNat 64 (0x80800+16*chain.val) := by
    simpa [KeygenEndpoint.endpointAddress] using endpointNe (0 : Fin 2)
  have h1 : wordAddress 0x80000 j ≠ BitVec.ofNat 64 (0x80800+16*chain.val)+8 := by
    have addr8 : BitVec.ofNat 64 (0x80800+16*chain.val)+8 =
        KeygenEndpoint.endpointAddress chain.val 1 := by
      simp [KeygenEndpoint.endpointAddress, BitVec.ofNat_add, Nat.add_comm]
      ac_rfl
    rw [addr8]
    exact endpointNe 1
  rw [if_neg h1, if_neg h0]

/-- The stronger word-level hoisted header invariant survives endpoint storage. -/
theorem endpoint_header_word_carry (s : MachineState) (level tree leaf : Nat)
    (chain : Reference.Chain) (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (carry : Hoist.HeaderWordCarry s level tree leaf) :
    Hoist.HeaderWordCarry (KeygenEndpoint.stateAt s (-508) 32 40) level tree leaf := by
  rcases carry with ⟨oldChain, oldStep, hc, hs, header, index, service, destination, seven⟩
  obtain ⟨r5, r12, r31⟩ := KeygenEndpoint.stickyRegsAt s (-508) 32 40
  refine ⟨oldChain, oldStep, hc, hs, ?_, ?_, r5.trans service,
    r12.trans destination, r31.trans seven⟩
  · simpa [wordAddress] using
      (endpoint_header_word_frame s chain counter 0 (by decide)).trans header
  · intro i
    have addr : wordAddress 0x80008 i.val = wordAddress 0x80000 (i.val+1) := by
      unfold wordAddress
      apply congrArg (BitVec.ofNat 64)
      omega
    rw [addr, endpoint_header_word_frame s chain counter (i.val+1)
      (by have := i.isLt; omega)]
    simpa only [← addr] using index i

/-- Store one endpoint while retaining the canonical header words for the next chain. -/
theorem store_endpoint_with_word_carry (s : MachineState) (level tree leaf : Nat)
    (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x163c) (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (valueWords : ∀ i : Fin 2,
      s.getMem (wordAddress 0x80020 i.val) = value.extractLsb' (64*i.val) 64)
    (carry : Hoist.HeaderWordCarry s level tree leaf) :
    ∃ final, OrdinarySteps verify s 21 final ∧
      final.pc = (if chain.val+1 = 46 then 0x1690 else 0x1490) ∧
      final.getMem 0x80430 = BitVec.ofNat 64 (chain.val+1) ∧
      (∀ i : Fin 2, final.getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
        value.extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, a ≠ 0x80430 → (∀ i : Fin 2,
        a ≠ KeygenEndpoint.endpointAddress chain.val i.val) → final.getMem a = s.getMem a) ∧
      Hoist.HeaderWordCarry final level tree leaf := by
  have src0 : ((0x80000 : Word) + signExtend12 (32 : BitVec 12)) =
      wordAddress 0x80020 0 := by decide
  have src8 : ((0x80000 : Word) + signExtend12 (40 : BitVec 12)) =
      wordAddress 0x80020 1 := by decide
  let final := KeygenEndpoint.stateAt s (-508) 32 40
  obtain ⟨run, finalPC, finalCounter, endpoints, ra, sp, frame⟩ :=
    KeygenEndpoint.store_endpoint_at_state verify 0x163c (-508) 32 40 (by decide)
      s chain value pc counter (by decide) (by decide)
      (by rw [src0]; exact valueWords 0) (by rw [src8]; exact valueWords 1)
  exact ⟨final, run, by
    simpa only [show (0x163c : Word)+84=0x1690 by decide,
      show (0x163c : Word)+80+signExtend13 (-508 : BitVec 13)=0x1490 by decide]
      using finalPC, finalCounter, endpoints, ra, sp, frame,
    endpoint_header_word_carry s level tree leaf chain counter carry⟩

/-- info: 'SigGolfCandidate.Hypertree.Verifying.store_endpoint_with_word_carry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms store_endpoint_with_word_carry

end SigGolfCandidate.Hypertree.Verifying
