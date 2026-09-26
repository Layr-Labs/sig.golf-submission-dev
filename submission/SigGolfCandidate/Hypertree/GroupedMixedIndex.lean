import SigGolfCandidate.Hypertree.GroupedHeightThreeUniform

/-!
Arithmetic for a tree-addressed 10-bit bottom and 49 upper WOTS groups:
46 groups of height three followed by three of height four. This covers the
full 160-bit message index. The file records an honest fused-signer cost target;
it is not a bytecode execution or security certificate.
-/

namespace SigGolfCandidate.Hypertree.GroupedMixedIndex
open SigGolf SigGolfCandidate.Hypertree

def upperHeights : List Nat := List.replicate 46 3 ++ List.replicate 3 4

theorem upper_heights_length : upperHeights.length = 49 := by decide
theorem upper_heights_sum : upperHeights.sum = 150 := by decide

def shiftIndex : List Nat → Nat → Nat
  | [], index => index
  | height :: rest, index => shiftIndex rest (index / 2 ^ height)

theorem shift_index_eq_div (heights : List Nat) (index : Nat) :
    shiftIndex heights index = index / 2 ^ heights.sum := by
  induction heights generalizing index with
  | nil => simp [shiftIndex]
  | cons height rest ih =>
    simp only [shiftIndex, List.sum_cons]
    rw [ih, Nat.div_div_eq_div_mul, pow_add]

def bottomTree (index : BitVec 160) : Nat := index.toNat / 2 ^ 10
def bottomChild (index : BitVec 160) : Nat := index.toNat % 2 ^ 10

theorem bottom_recompose (index : BitVec 160) :
    2 ^ 10 * bottomTree index + bottomChild index = index.toNat := by
  simp only [bottomTree, bottomChild]
  omega

theorem upper_final_index_zero (index : BitVec 160) :
    shiftIndex upperHeights (bottomTree index) = 0 := by
  rw [shift_index_eq_div, upper_heights_sum]
  change (index.toNat / 2 ^ 10) / 2 ^ 150 = 0
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  exact Nat.div_eq_of_lt index.isLt

def upperFullTreeCompressions : Nat :=
  46 * (8 * (26 + 52 * 5 + 14) + 7) +
    3 * (16 * (26 + 52 * 5 + 14) + 15)

def bottomFullTreeCompressions : Nat := 3 * 2 ^ 10 - 1

def signCompressions : Nat :=
  upperFullTreeCompressions + bottomFullTreeCompressions + 9

theorem sign_budget :
    upperFullTreeCompressions = 125167 ∧
    bottomFullTreeCompressions = 3071 ∧
    signCompressions = 128247 ∧ signCompressions < BUDGET_SIGN := by decide

def signatureBytes : Nat := 32 + 16 + 160 * 16 + 49 * 52 * 16

theorem signature_bytes : signatureBytes = 43376 := by decide

/-- Every upper group has 113 suffix hashes and a 14-compression leaf hash;
the 160 node hashes cover all bottom and upper authentication edges. -/
def verifyHashCompressions : Nat := 49 * (113 + 14) + 160 + 1 + 4

theorem verify_hash_compressions : verifyHashCompressions = 6388 := by decide

end SigGolfCandidate.Hypertree.GroupedMixedIndex
