import SigGolfCandidate.Hypertree.GroupedUniformTableLayout

namespace SigGolfCandidate.Hypertree.GroupedUniformPointer
open SigGolfCandidate.Hypertree.GroupedUniformTableLayout

def address (row column : Nat) : Nat :=
  baseAddress + 16 * (148 * row + column)

theorem initial_address : address 51 147 = 0xFFFFB0 := by decide

theorem skip_address (row column : Nat) (hc : 0 < column) :
    address row column - 16 = address row (column - 1) := by
  unfold address
  omega

theorem select_address (row column : Nat) (hr : 0 < row) :
    address row column - 2368 = address (row - 1) column := by
  unfold address
  omega

theorem entry_bounds (row column : Nat) (hr : row < 52) (hc : column < 148) :
    baseAddress ≤ address row column ∧
    address row column + 16 ≤ baseAddress + payloadBytes ∧
    address row column % 8 = 0 := by
  have hbase : baseAddress = 0xFE1EC0 := numeric_layout.2.2
  simp only [address, hbase]
  dsimp [payloadBytes]
  omega

theorem reads_below_stack (row column : Nat) (hr : row < 52) (hc : column < 148) :
    address row column + 16 ≤ 0xFFFFC0 ∧
    address row column + 16 ≤ 0xFFFFE0 := by
  have h := entry_bounds row column hr hc
  have n := numeric_layout
  omega

end SigGolfCandidate.Hypertree.GroupedUniformPointer
