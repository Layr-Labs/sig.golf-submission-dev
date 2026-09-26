import SigGolfCandidate.Hypertree.SignIteration

/-! Inlined from SigGolfCandidate.Hypertree.SignLeafInvariant; its only importer was SigGolfCandidate.Hypertree.SignLeafLoop. -/
section
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def LeafSignatureSettings (s : MachineState) (pointer : Nat) (message : Reference.Digest) : Prop :=
  ∀ chain, CaptureSettings s pointer chain (Reference.digit message chain)

def EndpointsBefore (s : MachineState) (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool)
    (count : Nat) : Prop := ∀ chain : Reference.Chain, chain.val < count → ∀ i : Fin 2,
      s.getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
        (Reference.endpoint hash secretKey level tree side chain).extractLsb' (64*i.val) 64

def SignatureBefore (s : MachineState) (hash : Hash) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (message : Reference.Digest) (count : Nat) : Prop :=
  ∀ chain : Reference.Chain, chain.val < count →
    CapturedValue s pointer chain ((Reference.signLayer hash secretKey level tree side message).values chain)

def OutsideLeafWork (a : Word) : Prop := OutsideChainWork a ∧ a ≠ 0x80430 ∧
  ∀ chain : Reference.Chain, ∀ i : Fin 2, a ≠ KeygenEndpoint.endpointAddress chain.val i.val

theorem iteration_high_frame (s final : MachineState) (pointer : Nat) (current : Reference.Chain)
    (valid : CapturePointerValid pointer)
    (frame : ∀ a, OutsideIteration current a →
      (∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * current.val) i.val) → final.getMem a = s.getMem a)
    (a : Word) (outside : OutsideIteration current a) (high : 0x80000 ≤ a.toNat) :
    final.getMem a = s.getMem a := by
  apply frame a outside
  intro i eq
  have cb := current.isLt
  have ib := i.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  have h := congrArg BitVec.toNat eq
  simp only [wordAddress, BitVec.toNat_ofNat] at h
  omega

theorem LeafSignatureSettings.iteration (s final : MachineState) (pointer : Nat) (current : Reference.Chain)
    (message : Reference.Digest) (valid : CapturePointerValid pointer)
    (settings : LeafSignatureSettings s pointer message)
    (frame : ∀ a, OutsideIteration current a →
      (∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * current.val) i.val) → final.getMem a = s.getMem a) :
    LeafSignatureSettings final pointer message := by
  have keep := iteration_high_frame s final pointer current valid frame
  intro chain
  constructor
  · rw [keep _ (outsideIteration_metadata current _ (by decide) (by unfold OutsideChainWork; decide) (by decide)) (by decide)]
    exact (settings chain).pointerEq
  · rw [keep _ (outsideIteration_metadata current _ (by decide) (by unfold OutsideChainWork; decide) (by decide)) (by decide)]
    exact (settings chain).enabled
  · rw [keep _ (outsideIteration_metadata current _ (by decide) (by unfold OutsideChainWork; decide) (by decide)) (by decide),
      keep _ (outsideIteration_metadata current _ (by decide) (by unfold OutsideChainWork; decide) (by decide)) (by decide)]
    exact (settings chain).selected
  · have cb := chain.isLt
    rw [getByte_word final 0x80600 chain.val (by decide) (by omega)]
    rw [keep]
    · rw [← getByte_word s 0x80600 chain.val (by decide) (by omega)]
      exact (settings chain).digitEq
    · apply outsideIteration_metadata current
      · simp only [wordAddress, BitVec.toNat_ofNat]; omega
      · unfold OutsideChainWork
        refine ⟨?_, ?_, ?_, ?_⟩
        all_goals (first | intro j eq | intro eq)
        all_goals have h := congrArg BitVec.toNat eq
        all_goals simp [wordAddress] at h
        all_goals omega
      · intro eq
        have h := congrArg BitVec.toNat eq
        simp [wordAddress] at h
        omega
    · simp only [wordAddress, BitVec.toNat_ofNat]; omega

theorem endpoint_distinct (chain other : Reference.Chain) (i j : Fin 2) (different : chain ≠ other) :
    KeygenEndpoint.endpointAddress chain.val i.val ≠ KeygenEndpoint.endpointAddress other.val j.val := by
  intro eq
  have h := congrArg BitVec.toNat eq
  have cb := chain.isLt
  have ob := other.isLt
  have ib := i.isLt
  have jb := j.isLt
  have ne : chain.val ≠ other.val := by intro same; exact different (Fin.ext same)
  simp only [KeygenEndpoint.endpointAddress, BitVec.toNat_ofNat] at h
  omega

theorem endpoint_outside_chain (chain : Reference.Chain) (i : Fin 2) :
    OutsideChainWork (KeygenEndpoint.endpointAddress chain.val i.val) ∧
      KeygenEndpoint.endpointAddress chain.val i.val ≠ 0x80430 := by
  have cb := chain.isLt
  have ib := i.isLt
  unfold OutsideChainWork
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals (first | intro j eq | intro eq)
  all_goals have h := congrArg BitVec.toNat eq
  all_goals simp [KeygenEndpoint.endpointAddress, wordAddress] at h
  all_goals omega

theorem signature_distinct (pointer : Nat) (chain other : Reference.Chain) (i j : Fin 2)
    (valid : CapturePointerValid pointer) (different : chain ≠ other) :
    wordAddress (pointer + 16 * chain.val) i.val ≠ wordAddress (pointer + 16 * other.val) j.val := by
  intro eq
  have h := congrArg BitVec.toNat eq
  have cb := chain.isLt
  have ob := other.isLt
  have ib := i.isLt
  have jb := j.isLt
  have ne : chain.val ≠ other.val := by intro same; exact different (Fin.ext same)
  rcases valid with ⟨lower, upper, aligned⟩
  simp only [wordAddress, BitVec.toNat_ofNat] at h
  omega

theorem signature_outside_iteration (pointer : Nat) (chain current : Reference.Chain)
    (valid : CapturePointerValid pointer) (i : Fin 2) :
    OutsideIteration current (wordAddress (pointer + 16 * chain.val) i.val) := by
  refine ⟨capture_output_outside_work pointer chain valid i, (signature_outside_endpoint pointer chain valid i).1, ?_⟩
  intro j eq
  have h := congrArg BitVec.toNat eq
  have cb := chain.isLt
  have ob := current.isLt
  have ib := i.isLt
  have jb := j.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  simp only [wordAddress, KeygenEndpoint.endpointAddress, BitVec.toNat_ofNat] at h
  omega

end SigGolfCandidate.Hypertree.Signing
end

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

/-- Previously completed endpoint and signature slots survive the next chain iteration. -/
theorem iteration_prefixes (s final : MachineState) (hash : Hash) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (message : Reference.Digest) (current : Reference.Chain)
    (valid : CapturePointerValid pointer)
    (oldEndpoints : EndpointsBefore s hash secretKey level tree side current.val)
    (oldSignature : SignatureBefore s hash secretKey pointer level tree side message current.val)
    (endpoint : ∀ i : Fin 2, final.getMem (KeygenEndpoint.endpointAddress current.val i.val) =
      (Reference.endpoint hash secretKey level tree side current).extractLsb' (64*i.val) 64)
    (captured : CapturedValue final pointer current ((Reference.signLayer hash secretKey level tree side message).values current))
    (frame : ∀ a, OutsideIteration current a →
      (∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * current.val) i.val) → final.getMem a = s.getMem a) :
    EndpointsBefore final hash secretKey level tree side (current.val+1) ∧
      SignatureBefore final hash secretKey pointer level tree side message (current.val+1) := by
  constructor
  · intro chain less i
    by_cases same : chain = current
    · subst chain; exact endpoint i
    · have prior : chain.val < current.val := by
        have ne : chain.val ≠ current.val := by intro eq; exact same (Fin.ext eq)
        omega
      have outside := endpoint_outside_chain chain i
      rw [iteration_high_frame s final pointer current valid frame _
        ⟨outside.1, outside.2, fun j => endpoint_distinct chain current i j same⟩]
      · exact oldEndpoints chain prior i
      · have cb := chain.isLt
        have ib := i.isLt
        simp only [KeygenEndpoint.endpointAddress, BitVec.toNat_ofNat]
        omega
  · intro chain less
    by_cases same : chain = current
    · subst chain; exact captured
    · have prior : chain.val < current.val := by
        have ne : chain.val ≠ current.val := by intro eq; exact same (Fin.ext eq)
        omega
      intro i
      rw [frame _ (signature_outside_iteration pointer chain current valid i)
        (fun j => signature_distinct pointer chain current i j valid same)]
      exact oldSignature chain prior i

/-- Complete the remaining upper-leaf chains for the selected leaf, retaining both
endpoint and signature prefixes and counting every compression exactly. -/
theorem sign_selected_leaf_loop (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree start remaining : Nat)
    (side : Bool) (message : Reference.Digest)
    (pc : s.pc = if start = 46 then 0x18c8 else 0x1584) (length : start + remaining = 46)
    (upper : level ≠ 0) (valid : CapturePointerValid pointer)
    (data : LeafData s secretKey level tree side start) (settings : LeafSignatureSettings s pointer message)
    (endpoints : EndpointsBefore s hash secretKey level tree side start)
    (signature : SignatureBefore s hash secretKey pointer level tree side message start) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles (8*remaining) (8*remaining) final ∧
      instructions ≤ 1071 * remaining ∧ cycles ≤ 1127 * remaining ∧ final.pc = 0x18c8 ∧
      LeafData final secretKey level tree side 46 ∧
      EndpointsBefore final hash secretKey level tree side 46 ∧
      SignatureBefore final hash secretKey pointer level tree side message 46 ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideLeafWork a →
        (∀ chain : Reference.Chain, ∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) → final.getMem a = s.getMem a) := by
  induction remaining generalizing s start with
  | zero =>
    have eq : start = 46 := by omega
    subst start
    refine ⟨s, 0, 0, Trace.refl s, by omega, by omega, ?_, data, endpoints, signature, rfl, rfl, ?_⟩
    · simpa using pc
    · intro a _ _; rfl
  | succ remaining ih =>
    have bound : start < 46 := by omega
    let chain : Reference.Chain := ⟨start, bound⟩
    have prePC : s.pc = 0x1584 := by rw [pc, if_neg (by omega)]
    obtain ⟨next, steps, cycles, pre, stepsBound, cyclesBound, nextPC, nextData, endpoint,
      captured, nextRA, nextSP, nextFrame⟩ := sign_selected_iteration hash s secretKey pointer level tree side chain message
        prePC upper valid data (settings chain)
    have nextSettings := settings.iteration s next pointer chain message valid nextFrame
    obtain ⟨nextEndpoints, nextSignature⟩ := iteration_prefixes s next hash secretKey pointer level tree side message chain
      valid endpoints signature endpoint captured nextFrame
    obtain ⟨final, finalSteps, finalCycles, tail, finalStepsBound, finalCyclesBound, finalPC, finalData,
      finalEndpoints, finalSignature, finalRA, finalSP, finalFrame⟩ := ih next (start+1) nextPC (by omega)
        nextData nextSettings nextEndpoints nextSignature
    refine ⟨final, steps + finalSteps, cycles + finalCycles, ?_, by omega, by omega, finalPC,
      finalData, finalEndpoints, finalSignature, finalRA.trans nextRA, finalSP.trans nextSP, ?_⟩
    · convert pre.trans tail using 1 <;> omega
    · intro a outside signatureOutside
      rw [finalFrame a outside signatureOutside, nextFrame a ⟨outside.1, outside.2.1, outside.2.2 chain⟩ (signatureOutside chain)]

/-- All46selected-chain signatures and endpoints are generated by the actual signer bytecode. -/
theorem sign_selected_leaf_chains (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (message : Reference.Digest) (pc : s.pc = 0x1584) (upper : level ≠ 0)
    (valid : CapturePointerValid pointer) (data : LeafData s secretKey level tree side 0)
    (settings : LeafSignatureSettings s pointer message) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles 368 368 final ∧
      instructions ≤ 49266 ∧ cycles ≤ 51842 ∧ final.pc = 0x18c8 ∧
      LeafData final secretKey level tree side 46 ∧
      EndpointsBefore final hash secretKey level tree side 46 ∧
      SignatureBefore final hash secretKey pointer level tree side message 46 ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideLeafWork a →
        (∀ chain : Reference.Chain, ∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) → final.getMem a = s.getMem a) :=
  sign_selected_leaf_loop hash s secretKey pointer level tree 0 46 side message pc (by decide) upper valid data settings
    (by intro chain lt; omega) (by intro chain lt; omega)

set_option format.width 200
/-- info: 'SigGolfCandidate.Hypertree.Signing.sign_selected_leaf_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sign_selected_leaf_chains

end SigGolfCandidate.Hypertree.Signing
