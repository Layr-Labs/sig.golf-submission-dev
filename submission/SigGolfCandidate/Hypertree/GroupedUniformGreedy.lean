import SigGolfCandidate.Hypertree.GroupedUniformTableBound

namespace SigGolfCandidate.Hypertree.GroupedUniformGreedy
open Finset SigGolfCandidate.Hypertree.GroupedUniformCapacity
open SigGolfCandidate.Hypertree.GroupedUniformTableBound

/-- Number of valid suffix words preceding the branch labeled `d`. -/
def branchPrefix (n s d : Nat) : Nat :=
  ∑ i ∈ Finset.range d, if i ≤ s then count n (s - i) else 0

theorem prefix_succ (n s d : Nat) :
    branchPrefix n s (d+1) = branchPrefix n s d + if d ≤ s then count n (s-d) else 0 := by
  simp only [branchPrefix, Finset.sum_range_succ]

theorem prefix_six (n s : Nat) : branchPrefix n s 6 = count (n+1) s := by
  exact (count_succ_six n s).symm

/-- The first cumulative interval containing a legal rank supplies a valid
next digit and a residual rank within the chosen suffix block. -/
def round (n s r : Nat) (rank : r < count (n+1) s) :
    { d : Nat // d < 6 ∧ d ≤ s ∧ branchPrefix n s d ≤ r ∧
      r - branchPrefix n s d < count n (s-d) } := by
  let P : Nat → Prop := fun d => r < branchPrefix n s (d+1)
  have h5 : P 5 := by
    change r < branchPrefix n s (5 + 1)
    rw [show 5 + 1 = 6 by decide, prefix_six]
    exact rank
  have hex : ∃ d, P d := ⟨5, h5⟩
  let d := Nat.find hex
  have hspec : P d := Nat.find_spec hex
  have hd : d < 6 := by
    have hbound : d ≤ 5 := Nat.find_min' hex h5
    omega
  have hprefix : branchPrefix n s d ≤ r := by
    by_cases hzero : d = 0
    · rw [hzero]
      simp [branchPrefix]
    · have hmin := Nat.find_min hex (show d - 1 < d by omega)
      have hprev : d - 1 + 1 = d := by omega
      change ¬ r < branchPrefix n s (d - 1 + 1) at hmin
      rw [hprev] at hmin
      omega
  have hbranch : r < branchPrefix n s d + if d ≤ s then count n (s-d) else 0 := by
    simpa only [P, prefix_succ] using hspec
  have hds : d ≤ s := by
    by_contra h
    simp only [if_neg h, add_zero] at hbranch
    omega
  refine ⟨d, hd, hds, hprefix, ?_⟩
  simp only [if_pos hds] at hbranch
  omega

theorem greedy_round (n s r : Nat) (rank : r < count (n+1) s) :
    ∃ d : Nat, d < 6 ∧ d ≤ s ∧ branchPrefix n s d ≤ r ∧
      r - branchPrefix n s d < count n (s-d) :=
  ⟨(round n s r rank).val, (round n s r rank).property⟩



/-- Greedy unranking follows one certified cumulative-count interval per digit. -/
def unrank : (n s r : Nat) → r < count n s → List Nat
  | 0, _, _, _ => []
  | n + 1, s, r, hr =>
      let chosen := round n s r hr
      chosen.val :: unrank n (s - chosen.val)
        (r - branchPrefix n s chosen.val) chosen.property.2.2.2

/-- Rank in the same branch order used by `round`. -/
def rankCode : Nat → Nat → List Nat → Nat
  | 0, _, _ => 0
  | _n + 1, _s, [] => 0
  | n + 1, s, d :: tail => branchPrefix n s d + rankCode n (s - d) tail

theorem rank_unrank (n s r : Nat) (hr : r < count n s) :
    rankCode n s (unrank n s r hr) = r := by
  induction n generalizing s r with
  | zero =>
      have hzero : r = 0 := by
        simp only [count] at hr
        split_ifs at hr <;> omega
      subst r
      rfl
  | succ n ih =>
      let chosen := round n s r hr
      have hchild := chosen.property.2.2.2
      change branchPrefix n s chosen.val +
        rankCode n (s - chosen.val)
          (unrank n (s - chosen.val) (r - branchPrefix n s chosen.val) hchild) = r
      rw [ih]
      have hprefix := chosen.property.2.2.1
      omega

theorem unrank_valid (n s r : Nat) (hr : r < count n s) :
    Valid n s (unrank n s r hr) := by
  induction n generalizing s r with
  | zero =>
      have hs : s = 0 := by
        simp only [count] at hr
        split_ifs at hr with h
        · exact h
        · omega
      subst s
      simp [Valid, unrank]
  | succ n ih =>
      let chosen := round n s r hr
      have hchild := chosen.property.2.2.2
      obtain ⟨hlen, hsum, hbound⟩ := ih (s - chosen.val)
        (r - branchPrefix n s chosen.val) hchild
      change Valid (n + 1) s
        (chosen.val :: unrank n (s - chosen.val)
          (r - branchPrefix n s chosen.val) hchild)
      dsimp only [Valid]
      refine ⟨?_, ?_, ?_⟩
      · simpa only [List.length_cons] using congrArg Nat.succ hlen
      · simp only [List.sum_cons, hsum]
        have hle := chosen.property.2.1
        omega
      · intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | htail
        · exact chosen.property.1
        · exact hbound d htail

def encodeGreedy (digest : BitVec 128) : List Nat :=
  unrank 52 147 digest.toNat (lt_of_lt_of_le digest.isLt capacity)

theorem encodeGreedy_valid (digest : BitVec 128) :
    Valid 52 147 (encodeGreedy digest) :=
  unrank_valid 52 147 digest.toNat (lt_of_lt_of_le digest.isLt capacity)

theorem encodeGreedy_injective : Function.Injective encodeGreedy := by
  intro x y same
  have h := congrArg (rankCode 52 147) same
  simp only [encodeGreedy, rank_unrank] at h
  exact BitVec.eq_of_toNat_eq h


/-- WOTS chain digit selected by the constructive greedy encoder. -/
def encodedDigit (digest : BitVec 128) (i : Fin 52) : Nat :=
  (encodeGreedy digest)[i.val]'(by
    rw [(encodeGreedy_valid digest).1]
    exact i.isLt)

theorem distinct_digest_has_earlier_digit (x y : BitVec 128) (different : x ≠ y) :
    ∃ i : Fin 52, encodedDigit y i < encodedDigit x i := by
  by_contra noEarlier
  push Not at noEarlier
  have ordered : List.Forall₂ (fun a b : Nat => a ≤ b)
      (encodeGreedy x) (encodeGreedy y) := by
    apply (List.forall₂_iff_get).2
    constructor
    · rw [(encodeGreedy_valid x).1, (encodeGreedy_valid y).1]
    · intro i hiX hiY
      have hi : i < 52 := by simpa only [(encodeGreedy_valid x).1] using hiX
      have h := noEarlier ⟨i, hi⟩
      change encodedDigit x ⟨i, hi⟩ ≤ encodedDigit y ⟨i, hi⟩ at h
      unfold encodedDigit at h
      omega
  have sameWords : encodeGreedy x = encodeGreedy y :=
    fixed_weight_antichain ordered
      (by rw [(encodeGreedy_valid x).2.1, (encodeGreedy_valid y).2.1])
  exact different (encodeGreedy_injective sameWords)

end SigGolfCandidate.Hypertree.GroupedUniformGreedy
