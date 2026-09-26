import SigGolfCandidate.Hypertree.GroupedBalancedVerifyFooter67

/-! A two-word verifier comparison is equality of complete 128-bit roots. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyRootMatch67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.Signing
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private def wordAddress (base i : Nat) : Word :=
  BitVec.ofNat 64 (base + 8*i)

theorem digest_eq_of_words (left right : Reference.Digest)
    (words : ∀ i : Fin 2,
      left.extractLsb' (64*i.val) 64 =
        right.extractLsb' (64*i.val) 64) : left = right := by
  ext j hj
  simp only [← BitVec.getLsbD_eq_getElem]
  by_cases low : j < 64
  · have h := congrArg (fun value : BitVec 64 => value.getLsbD j)
      (words 0)
    simpa [low] using h
  · have pos : j-64 < 64 := by omega
    have eq : 64+(j-64) = j := by omega
    have h := congrArg (fun value : BitVec 64 =>
      value.getLsbD (j-64)) (words 1)
    simpa [pos, eq] using h

theorem root_matches_iff (s : MachineState)
    (root pk : Reference.Digest)
    (current : ∀ i : Fin 2,
      s.getMem (wordAddress 0x80500 i.val) =
        root.extractLsb' (64*i.val) 64)
    (publicKey : ∀ i : Fin 2,
      s.getMem (wordAddress 0x40 i.val) =
        pk.extractLsb' (64*i.val) 64) :
    RootMatches s ↔ root = pk := by
  have c0 : s.getMem 0x80500 = root.extractLsb' 0 64 := current 0
  have c1 : s.getMem 0x80508 = root.extractLsb' 64 64 := current 1
  have p0 : s.getMem 0x40 = pk.extractLsb' 0 64 := publicKey 0
  have p1 : s.getMem 0x48 = pk.extractLsb' 64 64 := publicKey 1
  unfold RootMatches
  rw [c0,c1,p0,p1]
  constructor
  · intro h
    apply digest_eq_of_words
    intro i
    fin_cases i
    · exact h.1
    · exact h.2
  · intro h
    rw [h]
    exact ⟨rfl,rfl⟩

#print axioms root_matches_iff
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyRootMatch67
