import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.List.NodupEquivFin

/-! A kernel-checked numerical capacity certificate for 52 radix-six digits of
weight 147. All large binomial values are separately checked using the
factorial identity, so the final coefficient proof uses only kernel-checked steps. -/

namespace SigGolfCandidate.Hypertree.GroupedUniformCapacity
open Finset PowerSeries
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private theorem rescale_one_sub :
    PowerSeries.rescale (-1 : ℤ) ((1 + X : ℤ⟦X⟧) ^ 52) = (1 - X : ℤ⟦X⟧) ^ 52 := by
  simp [map_pow, map_add, PowerSeries.rescale_X]
  ring

private theorem coeff_one_add (j : ℕ) :
    PowerSeries.coeff j ((1 + X : ℤ⟦X⟧) ^ 52) = (Nat.choose 52 j : ℤ) := by
  rw [← PowerSeries.binomialSeries_nat (R := ℤ) (A := ℤ) 52]
  simpa [PowerSeries.binomialSeries_coeff] using (Ring.choose_natCast (R := ℤ) 52 j)

private theorem coeff_one_sub (j : ℕ) :
    PowerSeries.coeff j ((1 - X : ℤ⟦X⟧) ^ 52) =
      (-1 : ℤ) ^ j * (Nat.choose 52 j : ℤ) := by
  rw [← rescale_one_sub, PowerSeries.coeff_rescale, coeff_one_add]

private theorem numerator_subst :
    PowerSeries.subst (X ^ 6 : ℤ⟦X⟧) ((1 - X : ℤ⟦X⟧) ^ 52) =
      (1 - X ^ 6 : ℤ⟦X⟧) ^ 52 := by
  have hs : PowerSeries.HasSubst (X ^ 6 : ℤ⟦X⟧) :=
    PowerSeries.HasSubst.X_pow (by decide)
  rw [PowerSeries.subst_pow hs, PowerSeries.subst_sub hs]
  have hOne : PowerSeries.subst (X ^ 6 : ℤ⟦X⟧) (1 : ℤ⟦X⟧) = 1 := by
    rw [← PowerSeries.coe_substAlgHom hs]
    exact map_one _
  rw [hOne, PowerSeries.subst_X hs]

private theorem numerator_coeff (n : ℕ) :
    PowerSeries.coeff n ((1 - X ^ 6 : ℤ⟦X⟧) ^ 52) =
      if 6 ∣ n then (-1 : ℤ) ^ (n / 6) * (Nat.choose 52 (n / 6) : ℤ) else 0 := by
  rw [← numerator_subst, PowerSeries.coeff_subst_X_pow (by decide)]
  simp [coeff_one_sub]

private noncomputable def payloadPoly : ℤ⟦X⟧ := ∑ i ∈ Finset.range 6, (X : ℤ⟦X⟧) ^ i
private noncomputable def inverseGeom : ℤ⟦X⟧ := (PowerSeries.invOneSubPow ℤ 52).val

private theorem inverse_coeff (n : ℕ) :
    PowerSeries.coeff n inverseGeom = (Nat.choose (51 + n) 51 : ℤ) := by
  rw [inverseGeom, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
  simp

private theorem payload_poly_eq :
    payloadPoly ^ 52 = (1 - X ^ 6 : ℤ⟦X⟧) ^ 52 * inverseGeom := by
  have hgeom : payloadPoly * (1 - X : ℤ⟦X⟧) = 1 - X ^ 6 := by
    simpa [payloadPoly] using (geom_sum_mul_neg (X : ℤ⟦X⟧) 6)
  have hinv : (1 - X : ℤ⟦X⟧) ^ 52 * inverseGeom = 1 := by
    have h := PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one ℤ 51
    simpa [inverseGeom, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
      mul_comm] using h
  calc
    payloadPoly ^ 52 = payloadPoly ^ 52 * 1 := by ring
    _ = payloadPoly ^ 52 * ((1 - X : ℤ⟦X⟧) ^ 52 * inverseGeom) := by rw [hinv]
    _ = (payloadPoly ^ 52 * (1 - X : ℤ⟦X⟧) ^ 52) * inverseGeom := by ring
    _ = (1 - X ^ 6 : ℤ⟦X⟧) ^ 52 * inverseGeom := by rw [← mul_pow, hgeom]

private def certificateSum : ℤ :=
  ∑ k ∈ Finset.range 148,
    (if 6 ∣ k then (-1 : ℤ) ^ (k / 6) * (Nat.choose 52 (k / 6) : ℤ) else 0) *
      (Nat.choose (51 + (147 - k)) 51 : ℤ)

private theorem payload_coeff :
    PowerSeries.coeff 147 (payloadPoly ^ 52) = certificateSum := by
  rw [payload_poly_eq, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [numerator_coeff, inverse_coeff]
  rfl

private theorem sum_divisible_six (f : ℕ → ℤ) :
    (∑ k ∈ Finset.range 148, if 6 ∣ k then f k else 0) =
      ∑ j ∈ Finset.range 25, f (6 * j) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun j _ => 6 * j)
  · intro j hj
    simp only [Finset.mem_range, Finset.mem_filter] at hj ⊢
    omega
  · intro i hi j hj eq
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    rcases hk with ⟨hdiv, hlt⟩
    refine ⟨k / 6, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro j hj
    rfl

private theorem certificate_25 :
    certificateSum =
      ∑ j ∈ Finset.range 25,
        (-1 : ℤ) ^ j * (Nat.choose 52 j : ℤ) *
          (Nat.choose (51 + (147 - 6 * j)) 51 : ℤ) := by
  unfold certificateSum
  simp_rw [ite_mul, zero_mul]
  rw [sum_divisible_six]
  apply Finset.sum_congr rfl
  intro j hj
  have h : 6 * j / 6 = j := by omega
  rw [h]

private theorem choose_large_0 : Nat.choose 198 51 = 739616091484142930731541349281237416880549398608 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_1 : Nat.choose 192 51 = 120573059177776222407167591416696689777314857152 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_2 : Nat.choose 186 51 = 18373899374084962979162291903955359066998295496 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_3 : Nat.choose 180 51 = 2603613845589803456399272137503368767235539780 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_4 : Nat.choose 174 51 = 341045791976158676540105537511166212437571360 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_5 : Nat.choose 168 51 = 41022080997530082561742472763318583966422720 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_6 : Nat.choose 162 51 = 4496881662194506337324364527188834743242880 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_7 : Nat.choose 156 51 = 445402122671788829907475881089961527988240 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_8 : Nat.choose 150 51 = 39467962568101828027922028197900619114000 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_9 : Nat.choose 144 51 = 3093306602058033447596920191287505267840 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_10 : Nat.choose 138 51 = 211593100517628409272272907620176678080 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_11 : Nat.choose 132 51 = 12435996554939276036145892643319231520 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_12 : Nat.choose 126 51 = 616438323006958481344151683850263260 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_13 : Nat.choose 120 51 = 25202394358996989831281417065516920 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_14 : Nat.choose 114 51 = 827103710671265770756367677038144 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_15 : Nat.choose 108 51 = 21072197078882251702606214796528 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_16 : Nat.choose 102 51 = 399608854866744452032002440112 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_17 : Nat.choose 96 51 = 5344581948227203165429053888 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_18 : Nat.choose 90 51 = 46957575409390386430834320 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_19 : Nat.choose 84 51 = 246066921933574690893672 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_20 : Nat.choose 78 51 = 670475333050116177584 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_21 : Nat.choose 72 51 = 772692898154535072 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_22 : Nat.choose 66 51 = 268367258592576 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_23 : Nat.choose 60 51 = 14783142660 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_large_24 : Nat.choose 54 51 = 24804 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_0 : Nat.choose 52 0 = 1 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_1 : Nat.choose 52 1 = 52 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_2 : Nat.choose 52 2 = 1326 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_3 : Nat.choose 52 3 = 22100 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_4 : Nat.choose 52 4 = 270725 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_5 : Nat.choose 52 5 = 2598960 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_6 : Nat.choose 52 6 = 20358520 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_7 : Nat.choose 52 7 = 133784560 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_8 : Nat.choose 52 8 = 752538150 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_9 : Nat.choose 52 9 = 3679075400 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_10 : Nat.choose 52 10 = 15820024220 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_11 : Nat.choose 52 11 = 60403728840 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_12 : Nat.choose 52 12 = 206379406870 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_13 : Nat.choose 52 13 = 635013559600 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_14 : Nat.choose 52 14 = 1768966344600 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_15 : Nat.choose 52 15 = 4481381406320 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_16 : Nat.choose 52 16 = 10363194502115 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_17 : Nat.choose 52 17 = 21945588357420 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_18 : Nat.choose 52 18 = 42671977361650 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_19 : Nat.choose 52 19 = 76360380541900 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_20 : Nat.choose 52 20 = 125994627894135 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_21 : Nat.choose 52 21 = 191991813933920 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_22 : Nat.choose 52 22 = 270533919634160 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_23 : Nat.choose 52 23 = 352870329957600 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide
private theorem choose_small_24 : Nat.choose 52 24 = 426384982032100 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide

private theorem certificate_numeric :
    certificateSum = 365329674442637972243667503636328474120 := by
  rw [certificate_25]
  norm_num [Finset.sum_range_succ,
    choose_large_0,
    choose_large_1,
    choose_large_2,
    choose_large_3,
    choose_large_4,
    choose_large_5,
    choose_large_6,
    choose_large_7,
    choose_large_8,
    choose_large_9,
    choose_large_10,
    choose_large_11,
    choose_large_12,
    choose_large_13,
    choose_large_14,
    choose_large_15,
    choose_large_16,
    choose_large_17,
    choose_large_18,
    choose_large_19,
    choose_large_20,
    choose_large_21,
    choose_large_22,
    choose_large_23,
    choose_large_24,
    choose_small_0,
    choose_small_1,
    choose_small_2,
    choose_small_3,
    choose_small_4,
    choose_small_5,
    choose_small_6,
    choose_small_7,
    choose_small_8,
    choose_small_9,
    choose_small_10,
    choose_small_11,
    choose_small_12,
    choose_small_13,
    choose_small_14,
    choose_small_15,
    choose_small_16,
    choose_small_17,
    choose_small_18,
    choose_small_19,
    choose_small_20,
    choose_small_21,
    choose_small_22,
    choose_small_23,
    choose_small_24]

private noncomputable def polyNat : ℕ⟦X⟧ :=
  ∑ d ∈ Finset.range 6, (X : ℕ⟦X⟧) ^ d

private theorem coeff_polyNat (s : ℕ) :
    PowerSeries.coeff s polyNat = if s < 6 then 1 else 0 := by
  simp [polyNat, PowerSeries.coeff_X_pow]

/-- Number of radix-six digit words of length `n` and total weight `s`,
computed by the same suffix recurrence used by a greedy unranker. -/
def count : Nat → Nat → Nat
  | 0, s => if s = 0 then 1 else 0
  | n + 1, s => ∑ d ∈ Finset.range (s + 1), if d < 6 then count n (s - d) else 0

private theorem coeff_count (n s : Nat) :
    PowerSeries.coeff s (polyNat ^ n) = count n s := by
  induction n generalizing s with
  | zero => simp [count]
  | succ n ih =>
      rw [pow_succ', PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [coeff_polyNat, count, ih]

private theorem map_poly : PowerSeries.map Int.ofNatHom polyNat = payloadPoly := by
  simp [polyNat, payloadPoly]

private theorem count_int (n s : Nat) :
    PowerSeries.coeff s (payloadPoly ^ n) = (count n s : ℤ) := by
  rw [← map_poly, ← map_pow, PowerSeries.coeff_map, coeff_count]
  rfl

theorem exact_count : count 52 147 = 365329674442637972243667503636328474120 := by
  have h : ((count 52 147 : Nat) : ℤ) =
      365329674442637972243667503636328474120 := by
    rw [← count_int, payload_coeff, certificate_numeric]
  exact_mod_cast h

theorem capacity : 2 ^ 128 ≤ count 52 147 := by
  rw [exact_count]
  norm_num

private theorem list_sum_range (f : Nat → Nat) (m : Nat) :
    ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, ih, Finset.sum_range_succ]

def words : Nat → Nat → List (List Nat)
  | 0, s => if s = 0 then [[]] else []
  | n + 1, s =>
      (List.range (s + 1)).flatMap (fun d =>
        if d < 6 then (words n (s - d)).map (fun tail => d :: tail) else [])

theorem words_length (n s : Nat) : (words n s).length = count n s := by
  induction n generalizing s with
  | zero => by_cases h : s = 0 <;> simp [words, count, h]
  | succ n ih =>
      simp only [words, List.length_flatMap, count]
      rw [list_sum_range]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases h : d < 6
      · simp [h, ih]
      · simp [h]

theorem words_nodup (n s : Nat) : (words n s).Nodup := by
  induction n generalizing s with
  | zero => by_cases h : s = 0 <;> simp [words, h]
  | succ n ih =>
      rw [words, List.nodup_flatMap]
      constructor
      · intro d hd
        by_cases h : d < 6
        · simp only [if_pos h]
          exact (ih (s - d)).map (by intro a b hab; exact (List.cons.inj hab).2)
        · simp [h]
      · have hrange : (List.range (s + 1)).Nodup := List.nodup_range
        apply hrange.imp
        intro a b hab
        apply (List.disjoint_iff_ne).2
        intro xs hxs ys hys
        by_cases ha : a < 6
        · by_cases hb : b < 6
          · simp only [if_pos ha, List.mem_map] at hxs
            simp only [if_pos hb, List.mem_map] at hys
            rcases hxs with ⟨tx, _, rfl⟩
            rcases hys with ⟨ty, _, rfl⟩
            intro eq
            exact hab (List.cons.inj eq).1
          · simp [hb] at hys
        · simp [ha] at hxs

def Valid (n s : Nat) (digits : List Nat) : Prop :=
  digits.length = n ∧ digits.sum = s ∧ ∀ d ∈ digits, d < 6

theorem words_valid (n s : Nat) (digits : List Nat)
    (member : digits ∈ words n s) : Valid n s digits := by
  induction n generalizing s digits with
  | zero =>
      simp only [words] at member
      by_cases h : s = 0
      · simp only [if_pos h] at member
        have hd : digits = [] := by simpa using member
        subst digits
        simp [Valid, h]
      · simp [h] at member
  | succ n ih =>
      simp only [words, List.mem_flatMap] at member
      rcases member with ⟨d, hd, htail⟩
      by_cases h : d < 6
      · simp only [if_pos h, List.mem_map] at htail
        rcases htail with ⟨tail, hmem, rfl⟩
        obtain ⟨hlen, hsum, hbound⟩ := ih (s - d) tail hmem
        have hds : d ≤ s := by simpa using hd
        constructor
        · simp [hlen]
        constructor
        · simp [hsum]; omega
        · intro k hk
          simp only [List.mem_cons] at hk
          rcases hk with rfl | hk
          · exact h
          · exact hbound k hk
      · simp [h] at htail

theorem fixed_weight_antichain {a b : List Nat}
    (ordered : List.Forall₂ (fun x y => x ≤ y) a b)
    (same_sum : a.sum = b.sum) : a = b := by
  induction ordered with
  | nil => rfl
  | @cons x y xs ys hxy hrest ih =>
      have htail : xs.sum ≤ ys.sum := hrest.sum_le_sum
      have hxy' : x = y := by
        simp only [List.sum_cons] at same_sum
        omega
      subst y
      have hsum : xs.sum = ys.sum := by
        exact Nat.add_left_cancel (by simpa only [List.sum_cons] using same_sum)
      congr
      exact ih hsum

def specEncode (hcap : 2 ^ 128 ≤ count 52 147) (digest : BitVec 128) : List Nat :=
  (words 52 147)[digest.toNat]'(by
    rw [words_length]
    exact lt_of_lt_of_le digest.isLt hcap)

theorem specEncode_valid (hcap : 2 ^ 128 ≤ count 52 147) (digest : BitVec 128) :
    Valid 52 147 (specEncode hcap digest) := by
  unfold specEncode
  exact words_valid 52 147 _ (List.getElem_mem _)

theorem specEncode_injective (hcap : 2 ^ 128 ≤ count 52 147) :
    Function.Injective (specEncode hcap) := by
  intro x y same
  have h : x.toNat = y.toNat := by
    exact (List.getElem_inj (words_nodup 52 147)).mp same
  exact BitVec.eq_of_toNat_eq h


/-- The mathematical rank/unrank bijection for the complete fixed-weight codebook.
The RISC-V implementation should realize this ordering through cumulative DP counts. -/
def rankUnrank : Fin (words 52 147).length ≃
    { digits : List Nat // digits ∈ words 52 147 } :=
  (words_nodup 52 147).getEquiv (words 52 147)

theorem rank_unrank_inverse (i : Fin (words 52 147).length) :
    rankUnrank.symm (rankUnrank i) = i :=
  rankUnrank.symm_apply_apply i

def encode (digest : BitVec 128) : List Nat := specEncode capacity digest

theorem encode_injective : Function.Injective encode :=
  specEncode_injective capacity

theorem encode_valid (digest : BitVec 128) : Valid 52 147 (encode digest) :=
  specEncode_valid capacity digest

/-- The coordinate used by the WOTS verifier at a given chain. -/
def encodedDigit (digest : BitVec 128) (i : Fin 52) : Nat :=
  (encode digest)[i.val]'(by
    rw [(encode_valid digest).1]
    exact i.isLt)

/-- Distinct encoded messages require an earlier chain point in one coordinate. -/
theorem distinct_digest_has_earlier_digit (x y : BitVec 128) (different : x ≠ y) :
    ∃ i : Fin 52, encodedDigit y i < encodedDigit x i := by
  by_contra noEarlier
  push Not at noEarlier
  have ordered : List.Forall₂ (fun a b : Nat => a ≤ b) (encode x) (encode y) := by
    apply (List.forall₂_iff_get).2
    constructor
    · rw [(encode_valid x).1, (encode_valid y).1]
    · intro i hiX hiY
      have hi : i < 52 := by simpa only [(encode_valid x).1] using hiX
      have h := noEarlier ⟨i, hi⟩
      change encodedDigit x ⟨i, hi⟩ ≤ encodedDigit y ⟨i, hi⟩ at h
      unfold encodedDigit at h
      omega
  have sameWords : encode x = encode y :=
    fixed_weight_antichain ordered (by rw [(encode_valid x).2.1, (encode_valid y).2.1])
  exact different (encode_injective sameWords)

end SigGolfCandidate.Hypertree.GroupedUniformCapacity
