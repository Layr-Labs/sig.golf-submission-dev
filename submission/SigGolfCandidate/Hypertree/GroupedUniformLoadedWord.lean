import SigGolfCandidate.Hypertree.GroupedUniformLoaderGeneric
import SigGolfCandidate.Hypertree.GroupedUniformTableWord
import SigGolfCandidate.Hypertree.GroupedUniformPointer

namespace SigGolfCandidate.Hypertree.GroupedUniformLoadedWord
open SigGolf RiscvZkvm.Rv64
open GroupedUniformTableLayout
  (baseAddress totalBytes payloadBytes paddingBytes memoryBytes entry_offset_bound)
open GroupedUniformMaterialized (data data_length)
open GroupedUniformCapacity (count)
open GroupedUniformTableWord GroupedUniformPointer

private def blank : MachineState :=
  { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }

def loaded : MachineState :=
  blank.writeBytesAsWords (BitVec.ofNat 64 baseAddress) data

private theorem loaded_word_generic (bs : List Byte) (same : bs = data)
    (row col : Nat) (half : Fin 2) (hr : row < 52) (hc : col < 148) :
    (blank.writeBytesAsWords (BitVec.ofNat 64 baseAddress) bs).getMem
      (BitVec.ofNat 64 (address row col + 8 * half.val)) =
      tableWord row col half hr hc := by
  let i := 2 * (148 * row + col) + half.val
  have hoff : 8 * i = 16 * (148 * row + col) + 8 * half.val := by
    dsimp [i]
    omega
  have hlen : bs.length = totalBytes := by rw [same, data_length]
  have h8 : 8 * i + 8 ≤ bs.length := by
    rw [hlen, hoff]
    have h := entry_offset_bound row col (8 * half.val + 7) hr hc (by omega)
    dsimp [totalBytes, payloadBytes, paddingBytes] at *
    omega
  have hbound : baseAddress + 8 * ((bs.length + 7) / 8) < 2 ^ 64 := by
    rw [hlen]
    dsimp [baseAddress, totalBytes, payloadBytes, paddingBytes, memoryBytes]
    decide
  have haddr : address row col + 8 * half.val = baseAddress + 8 * i := by
    unfold address
    omega
  rw [haddr]
  rw [GroupedUniformLoaderGeneric.write_word_getD blank baseAddress bs i hbound h8]
  unfold tableWord
  apply congrArg (fun f : Fin 8 → BitVec 8 => packDword f)
  funext j
  have hj : 8 * i + j.val =
      16 * (148 * row + col) + 8 * half.val + j.val := by omega
  rw [hj, same]

theorem loaded_word (row col : Nat) (half : Fin 2)
    (hr : row < 52) (hc : col < 148) :
    loaded.getMem (BitVec.ofNat 64 (address row col + 8 * half.val)) =
      BitVec.ofNat 64 (count row col / 2 ^ (64 * half.val)) := by
  change (blank.writeBytesAsWords (BitVec.ofNat 64 baseAddress) data).getMem _ = _
  rw [loaded_word_generic data rfl row col half hr hc]
  exact tableWord_eq row col half hr hc

end SigGolfCandidate.Hypertree.GroupedUniformLoadedWord
