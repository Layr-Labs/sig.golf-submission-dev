import SigGolfCandidate.Hypertree.Reference

/-!
A separate coding avenue for the 68-chain, base-four WOTS leaf in
GroupedHeightThree. Any injective map from 128-bit messages into words of
weight 122 removes the checksum chains and fixes the verifier suffix at 82
hashes. The antichain property needed by the earlier-point security argument
is proved here independently of the particular ranking algorithm.

The codebook cardinality and a practical ranking/unranking algorithm remain
separate implementation obligations; an external integer DP calculation gives
359374415424324150395184108618677270192 words of weight 122, just above
2^128. This number is recorded as a design target, not assumed as a theorem.
-/

namespace SigGolfCandidate.Hypertree.GroupedAntichain
open SigGolf SigGolfCandidate.Hypertree Reference

abbrev Codeword := Fin 68 → Fin 4

def weight (word : Codeword) : Nat := ∑ i : Fin 68, (word i).val

def Valid (word : Codeword) : Prop := weight word = 122

def suffixCost (word : Codeword) : Nat := ∑ i : Fin 68, (3 - (word i).val)

/-- All codewords with the required weight take precisely 82 chain hashes to
verify, regardless of the message. -/
theorem suffix_cost (word : Codeword) (valid : Valid word) : suffixCost word = 82 := by
  change (∑ i : Fin 68, (word i).val) = 122 at valid
  unfold suffixCost
  rw [Finset.sum_tsub_distrib]
  · simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at *
    omega
  · intro i _
    have hi := (word i).isLt
    omega

/-- Equal-weight quaternary vectors contain no strict componentwise order.
Thus different signed points cannot authorize each other's WOTS prefixes. -/
theorem antichain (first second : Codeword) (firstValid : Valid first)
    (secondValid : Valid second)
    (ordered : ∀ i, (first i).val ≤ (second i).val) : first = second := by
  have sums : (∑ i : Fin 68, (first i).val) =
      ∑ i : Fin 68, (second i).val := by
    simpa only [Valid, weight] using firstValid.trans secondValid.symm
  have each : ∀ i : Fin 68, (first i).val = (second i).val := by
    intro i
    exact (Finset.sum_eq_sum_iff_of_le (fun j _ => ordered j)).mp sums i (Finset.mem_univ i)
  funext i
  exact Fin.ext (each i)

theorem code_capacity_target :
    2 ^ (128 : Nat) < 359374415424324150395184108618677270192 := by decide

theorem next_weight_too_small :
    281914564403039622022788102307397660896 < 2 ^ (128 : Nat) := by decide

/-- Compression target for 52 three-bit upper trees, with 82 chain suffixes,
18 compressions for the 1088-byte WOTS leaf, three tree nodes per group, and
the bottom and index hashes. The RISC-V verifier and rank decoder still need
their own exact cost proof. -/
def groupedVerifyCompressions : Nat := 52 * (82 + 18 + 3) + 5 + 4

theorem grouped_verify_compressions : groupedVerifyCompressions = 5365 := by decide

end SigGolfCandidate.Hypertree.GroupedAntichain
