import SigGolfCandidate.Hypertree.GroupedUniformMaterialized
import RiscvZkvm.Rv64.Logic.ByteOps

namespace SigGolfCandidate.Hypertree.GroupedUniformTableWord
open SigGolfCandidate.Hypertree.GroupedUniformCapacity
open SigGolfCandidate.Hypertree.GroupedUniformMaterialized
open RiscvZkvm.Rv64

theorem byte_eq_any (x : Nat) (i : Fin 8) :
    BitVec.ofNat 8 (x / 2 ^ (8 * i.val)) =
      extractByte (BitVec.ofNat 64 x) i.val := by
  apply BitVec.eq_of_toNat_eq
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  fin_cases i <;> norm_num <;> omega

private theorem pack_roundtrip (v : Word) :
    packDword (fun i : Fin 8 => extractByte v i.val) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hlt : j / 8 < 8 := by omega
  have hb := congrArg (fun b : BitVec 8 => b.getLsbD (j % 8))
    (extractByte_packDword (f := fun i : Fin 8 => extractByte v i.val)
      (i := ⟨j / 8, hlt⟩))
  have hidx : j / 8 * 8 + j % 8 = j := by omega
  have hm : j % 8 < 8 := by omega
  simpa [extractByte, hidx, hm] using hb

private theorem byte_bound (n s : Nat) (half : Fin 2) (j : Fin 8)
    (hn : n < 52) (hs : s < 148) :
    16 * (148 * n + s) + 8 * half.val + j.val <
      GroupedUniformTableLayout.totalBytes := by
  have hj : 8 * half.val + j.val < 16 := by omega
  have h := GroupedUniformTableLayout.entry_offset_bound n s
    (8 * half.val + j.val) hn hs hj
  dsimp [GroupedUniformTableLayout.totalBytes,
    GroupedUniformTableLayout.payloadBytes] at *
  omega

def tableWord (n s : Nat) (half : Fin 2) (_hn : n < 52) (_hs : s < 148) : Word :=
  packDword (fun j : Fin 8 =>
    data.getD (16 * (148 * n + s) + 8 * half.val + j.val) 0)

theorem tableWord_eq (n s : Nat) (half : Fin 2)
    (hn : n < 52) (hs : s < 148) :
    tableWord n s half hn hs =
      BitVec.ofNat 64 (count n s / 2 ^ (64 * half.val)) := by
  unfold tableWord
  rw [← pack_roundtrip (BitVec.ofNat 64 (count n s / 2 ^ (64 * half.val)))]
  apply congrArg (fun f : Fin 8 → BitVec 8 => packDword f)
  funext j
  have hj : 8 * half.val + j.val < 16 := by omega
  have hb := data_entry n s (8 * half.val + j.val) hn hs hj
  rw [List.getElem_eq_getD (fallback := (0 : BitVec 8))] at hb
  have hindex : 16 * (148 * n + s) + 8 * half.val + j.val =
      16 * (148 * n + s) + (8 * half.val + j.val) := by omega
  rw [hindex]
  rw [hb]
  rw [← byte_eq_any (count n s / 2 ^ (64 * half.val)) j]
  apply congrArg (BitVec.ofNat 8)
  have he : 8 * (8 * half.val + j.val) = 64 * half.val + 8 * j.val := by omega
  rw [he, Nat.div_div_eq_div_mul, ← pow_add]

end SigGolfCandidate.Hypertree.GroupedUniformTableWord
