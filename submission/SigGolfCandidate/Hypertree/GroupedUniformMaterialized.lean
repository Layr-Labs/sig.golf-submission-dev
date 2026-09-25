import SigGolfCandidate.Hypertree.GroupedUniformTableLayout

namespace SigGolfCandidate.Hypertree.GroupedUniformMaterialized
open SigGolfCandidate.Hypertree.GroupedUniformCapacity
open SigGolfCandidate.Hypertree.GroupedUniformTableBound

/-! The executable table is built row by row. Each row recomputes its
predecessors once; no byte evaluates the exponential specification `count`. -/

def rowZero : Vector Nat 148 :=
  Vector.ofFn fun i => if i.val = 0 then 1 else 0

def nextRow (prev : Vector Nat 148) : Vector Nat 148 :=
  Vector.ofFn fun s =>
    ∑ d ∈ Finset.range 6,
      if h : d ≤ s.val then prev[s.val - d]'(by omega) else 0

def row : Nat → Vector Nat 148
  | 0 => rowZero
  | n + 1 => nextRow (row n)

theorem row_eq_count (n s : Nat) (hs : s < 148) :
    (row n)[s] = count n s := by
  induction n generalizing s with
  | zero =>
      simp [row, rowZero, count]
  | succ n ih =>
      simp only [row, nextRow, Vector.getElem_ofFn]
      rw [count_succ_six]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hds : d ≤ s
      · simp only [dif_pos hds, if_pos hds]
        exact ih (s - d) (by omega)
      · simp [hds]

def encodedEntry (value : Nat) : Vector (BitVec 8) 16 :=
  Vector.ofFn fun j => BitVec.ofNat 8 (value / 2 ^ (8 * j.val))

def rowsUntil : (n : Nat) → Vector (Vector Nat 148) (n + 1)
  | 0 => #v[rowZero]
  | n + 1 =>
      let rs := rowsUntil n
      rs.push (nextRow rs[n])

def rows : Vector (Vector Nat 148) 52 := rowsUntil 51

theorem rowsUntil_get (n k : Nat) (hk : k ≤ n) :
    (rowsUntil n)[k]'(by omega) = row k := by
  induction n generalizing k with
  | zero =>
      have keq : k = 0 := by omega
      subst k
      rfl
  | succ n ih =>
      by_cases hlt : k ≤ n
      · change ((rowsUntil n).push (nextRow (rowsUntil n)[n]))[k] = row k
        rw [Vector.getElem_push_lt (by omega : k < n + 1)]
        exact ih k hlt
      · have keq : k = n + 1 := by omega
        subst k
        change ((rowsUntil n).push (nextRow (rowsUntil n)[n]))[n + 1] =
          nextRow (row n)
        rw [Vector.getElem_push_eq, ih n (by omega)]

def payload : Vector (BitVec 8) (52 * (148 * 16)) :=
  rows.flatMap (fun r => r.flatMap encodedEntry)

def data : List (BitVec 8) := payload.toList ++ List.replicate 64 0

theorem data_length : data.length = GroupedUniformTableLayout.totalBytes := by
  simp [data, GroupedUniformTableLayout.totalBytes,
    GroupedUniformTableLayout.payloadBytes, GroupedUniformTableLayout.paddingBytes]

theorem data_entry (n s j : Nat) (hn : n < 52) (hs : s < 148) (hj : j < 16) :
    data[16 * (148 * n + s) + j]'(by
      rw [data_length]
      have h := GroupedUniformTableLayout.entry_offset_bound n s j hn hs hj
      dsimp [GroupedUniformTableLayout.totalBytes,
        GroupedUniformTableLayout.payloadBytes] at *
      omega) =
    BitVec.ofNat 8 (count n s / 2 ^ (8 * j)) := by
  let i := 16 * (148 * n + s) + j
  have hi : i < 52 * (148 * 16) := by
    dsimp [i]
    omega
  have hp : i < payload.toList.length := by simpa using hi
  have hoq : i / (148 * 16) = n := by dsimp [i]; omega
  have hor : i % (148 * 16) = 16 * s + j := by dsimp [i]; omega
  have hiq : (16 * s + j) / 16 = s := by omega
  have hir : (16 * s + j) % 16 = j := by omega
  simp only [data]
  rw [List.getElem_append_left hp, Vector.getElem_toList]
  simp only [payload]
  rw [Vector.getElem_flatMap hi]
  simp only [hoq, hor]
  rw [Vector.getElem_flatMap (show 16 * s + j < 148 * 16 by omega)]
  simp only [hiq, hir]
  simp only [encodedEntry, Vector.getElem_ofFn, rows]
  simp only [rowsUntil_get 51 n (by omega), row_eq_count n s hs]

theorem padding_zero (i : Nat)
    (hlow : GroupedUniformTableLayout.payloadBytes ≤ i)
    (hhigh : i < GroupedUniformTableLayout.totalBytes) :
    data[i]'(by rw [data_length]; exact hhigh) = 0 := by
  have hp : payload.toList.length ≤ i := by
    simpa [GroupedUniformTableLayout.payloadBytes] using hlow
  simp only [data]
  rw [List.getElem_append_right hp]
  simp only [List.getElem_replicate]

end SigGolfCandidate.Hypertree.GroupedUniformMaterialized
