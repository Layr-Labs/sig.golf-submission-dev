import SigGolfCandidate.Hypertree.GroupedUniformDecoderImage
import SigGolfCandidate.Hypertree.GroupedUniformGreedy

namespace SigGolfCandidate.Hypertree.GroupedUniformDecoderCost
open SigGolfCandidate.Hypertree.GroupedUniformDecoderImage
open SigGolfCandidate.Hypertree.GroupedUniformGreedy

/-- Contiguous bytecode blocks used in the control-flow accounting.
The fail jump at index 28 and the fail epilogue are unreachable for legal ranks. -/
def setup : List (BitVec 32) := code.take 14
def digitInit : List (BitVec 32) := (code.drop 14).take 1
def trial : List (BitVec 32) := (code.drop 15).take 6
def skip : List (BitVec 32) := (code.drop 21).take 7
def commit : List (BitVec 32) := (code.drop 29).take 6
def finalBlock : List (BitVec 32) := (code.drop 35).take 4

theorem block_lengths :
    setup.length = 14 ∧ digitInit.length = 1 ∧ trial.length = 6 ∧
    skip.length = 7 ∧ commit.length = 6 ∧ finalBlock.length = 4 := by decide

/-- Syntactic worst-case cycle count for a legal digit path through the
42-word program, charging every branch test in each trial. -/
def pathBudget (digits : List Nat) : Nat :=
  setup.length + (digits.take 51).length *
    (digitInit.length + trial.length + commit.length) +
    (digits.take 51).sum * (trial.length + skip.length) + finalBlock.length

private theorem sum_take_le (digits : List Nat) :
    (digits.take 51).sum ≤ digits.sum := by
  have h : (digits.take 51).sum + (digits.drop 51).sum = digits.sum := by
    rw [← List.sum_append, List.take_append_drop]
  omega

theorem pathBudget_le (digits : List Nat)
    (length : digits.length = 52) (weight : digits.sum = 147) :
    pathBudget digits ≤ 2592 := by
  obtain ⟨hsetup, hinit, htrial, hskip, hcommit, hfinal⟩ := block_lengths
  have htake : (digits.take 51).length = 51 := by
    simp [List.length_take, length]
  have hsum : (digits.take 51).sum ≤ 147 := by
    exact le_trans (sum_take_le digits) (le_of_eq weight)
  simp only [pathBudget, hsetup, hinit, htrial, hskip, hcommit, hfinal, htake]
  omega

theorem encoded_pathBudget_le (digest : BitVec 128) :
    pathBudget (encodeGreedy digest) ≤ 2592 := by
  obtain ⟨hlen, hsum, _⟩ := encodeGreedy_valid digest
  exact pathBudget_le _ hlen hsum

end SigGolfCandidate.Hypertree.GroupedUniformDecoderCost
