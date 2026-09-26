import SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainEndpoints67
import SigGolfCandidate.TraceDeterminism

/-! Memory outside the WOTS scratch and output arrays survives each chain. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastWotsProtected67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedByteFastChainReady67
open GroupedBalancedByteFastChainEndpoints67
open GroupedBalancedByteFastLimit67
open GroupedBalancedByteFastSuffixLoop67
open GroupedBalancedByteFastSuffixData67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def Protected (a : Word) : Prop :=
  a.toNat < 0x80000 ∨
  (0x81000 ≤ a.toNat ∧ a.toNat < 0x90000) ∨
  0xfff700 ≤ a.toNat

private theorem protected_outside (a : Word)
    (safeAddr : Protected a) : OutsideTick a := by
  rcases safeAddr with low | ⟨high,below⟩ | upper
  · constructor
    · intro eq
      have h := congrArg BitVec.toNat eq
      simp at h
      omega
    · intro j eq
      have h := congrArg BitVec.toNat eq
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x90020+8*j.val < 2^64)] at h
      omega
  · constructor
    · intro eq
      have h := congrArg BitVec.toNat eq
      simp at h
      omega
    · intro j eq
      have h := congrArg BitVec.toNat eq
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x90020+8*j.val < 2^64)] at h
      omega
  · constructor
    · intro eq
      have h := congrArg BitVec.toNat eq
      simp at h
      omega
    · intro j eq
      have h := congrArg BitVec.toNat eq
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x90020+8*j.val < 2^64)] at h
      omega

private theorem protected_output (s : MachineState)
    (base leaf start : Nat) (chain : Fin 67)
    (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (ready : Ready s base leaf start chain message values)
    (a : Word) (safeAddr : Protected a) :
    a ≠ s.getReg .x24 ∧ a ≠ s.getReg .x24 + 8 := by
  have out0 : (s.getReg .x24).toNat =
      0x80020+16*chain.val := by
    rw [ready.outputPtr]
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80020+16*chain.val < 2^64)]
  have out8 : (s.getReg .x24 + 8).toNat =
      0x80020+16*chain.val+8 := by
    rw [ready.outputPtr]
    change (BitVec.ofNat 64 (0x80020+16*chain.val) +
      BitVec.ofNat 64 8).toNat = _
    rw [← BitVec.ofNat_add]
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega :
        0x80020+16*chain.val+8 < 2^64)]
  constructor
  · intro eq
    have h := congrArg BitVec.toNat eq
    rw [out0] at h
    rcases safeAddr with low | ⟨high,_⟩ | upper <;> omega
  · intro eq
    have h := congrArg BitVec.toNat eq
    rw [out8] at h
    rcases safeAddr with low | ⟨high,_⟩ | upper <;> omega

theorem copied_frame (hash : Hash) (s copied : MachineState)
    (base leaf start : Nat) (chain : Fin 67)
    (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (ready : Ready s base leaf start chain message values)
    (frame : ∀ a, OutsideTick a → a ≠ s.getReg .x24 →
      a ≠ s.getReg .x24 + 8 → copied.getMem a = s.getMem a)
    (a : Word) (safeAddr : Protected a) :
    copied.getMem a = s.getMem a := by
  obtain ⟨ne0,ne8⟩ := protected_output s base leaf start chain
    message values ready a safeAddr
  exact frame a (protected_outside a safeAddr) ne0 ne8

#print axioms copied_frame
end SigGolfCandidate.Hypertree.GroupedBalancedByteFastWotsProtected67
