import SigGolfCandidate.Hypertree.GroupedUniformTableBound

namespace SigGolfCandidate.Hypertree.GroupedUniformTableLayout
open SigGolfCandidate.Hypertree.GroupedUniformCapacity

abbrev payloadBytes : Nat := 52 * 148 * 16
abbrev paddingBytes : Nat := 64
abbrev totalBytes : Nat := payloadBytes + paddingBytes
abbrev memoryBytes : Nat := 2 ^ 24
abbrev baseAddress : Nat := memoryBytes - totalBytes

private def entryByte (n s j : Nat) : BitVec 8 :=
  BitVec.ofNat 8 (count n s / 2 ^ (8 * j))

def dataByte (i : Fin totalBytes) : BitVec 8 :=
  if i.val < payloadBytes then
    entryByte ((i.val / 16) / 148) ((i.val / 16) % 148) (i.val % 16)
  else 0

def data : List (BitVec 8) := List.ofFn dataByte

theorem data_length : data.length = totalBytes := by simp only [data, List.length_ofFn]

theorem numeric_layout :
    payloadBytes = 123136 ∧ totalBytes = 123200 ∧ baseAddress = 0xFE1EC0 := by decide

theorem payload_below_stack :
    baseAddress + payloadBytes = 0xFFFFC0 ∧
    0xFFFFC0 ≤ 0xFFFFE0 ∧ 0xFFFFF0 + 8 ≤ memoryBytes := by decide

theorem entry_offset_bound (n s j : Nat) (hn : n < 52) (hs : s < 148) (hj : j < 16) :
    16 * (148 * n + s) + j < payloadBytes := by
  dsimp [payloadBytes]
  omega

theorem data_entry (n s j : Nat) (hn : n < 52) (hs : s < 148) (hj : j < 16) :
    data[16 * (148 * n + s) + j]'(by rw [data_length]; exact lt_of_lt_of_le (entry_offset_bound n s j hn hs hj) (by decide)) =
      entryByte n s j := by
  have bound := entry_offset_bound n s j hn hs hj
  have hdiv : (16 * (148 * n + s) + j) / 16 = 148 * n + s := by omega
  have hmod : (16 * (148 * n + s) + j) % 16 = j := by omega
  have hrow : (148 * n + s) / 148 = n := by omega
  have hcol : (148 * n + s) % 148 = s := by omega
  simp only [data, List.getElem_ofFn, dataByte, if_pos bound]
  rw [hdiv, hmod, hrow, hcol]

theorem padding_zero (i : Nat) (hlow : payloadBytes ≤ i) (hhigh : i < totalBytes) :
    data[i]'(by rw [data_length]; exact hhigh) = 0 := by
  simp only [data, List.getElem_ofFn, dataByte, if_neg (show ¬i < payloadBytes by omega)]

theorem entry_value_fits (n s : Nat) (hn : n < 52) : count n s < 2 ^ 128 :=
  GroupedUniformTableBound.child_count_fits n s (by omega)

end SigGolfCandidate.Hypertree.GroupedUniformTableLayout
