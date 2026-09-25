import SigGolfCandidate.Memory

namespace SigGolfCandidate.Hypertree.GroupedUniformLoaderGeneric
open RiscvZkvm.Rv64

private theorem pack_slice (bs : List (BitVec 8)) (off : Nat)
    (h : off + 8 ≤ bs.length) :
    packBytes ((bs.drop off).take 8) =
      packDword (fun j : Fin 8 => bs.getD (off + j.val) 0) := by
  unfold packBytes
  apply congrArg (fun f : Fin 8 → BitVec 8 => packDword f)
  funext j
  have hj : j.val < ((bs.drop off).take 8).length := by
    simp only [List.length_take, List.length_drop]
    omega
  simp only [getByteAt, dif_pos hj]
  rw [List.getElem_take, List.getElem_drop]
  exact List.getElem_eq_getD 0

theorem write_word_getD (s : MachineState) (base : Nat)
    (bs : List (BitVec 8)) (i : Nat)
    (bound : base + 8 * ((bs.length + 7) / 8) < 2 ^ 64)
    (hi : 8 * i + 8 ≤ bs.length) :
    (s.writeBytesAsWords (BitVec.ofNat 64 base) bs).getMem
      (BitVec.ofNat 64 (base + 8 * i)) =
    packDword (fun j : Fin 8 => bs.getD (8 * i + j.val) 0) := by
  rw [Memory.write_word s base bs i bound (by omega)]
  exact pack_slice bs (8 * i) hi

end SigGolfCandidate.Hypertree.GroupedUniformLoaderGeneric
