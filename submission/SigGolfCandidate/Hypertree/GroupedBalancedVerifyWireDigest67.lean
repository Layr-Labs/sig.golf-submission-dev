import SigGolfCandidate.Hypertree.GroupedBalancedVerifyGenericPath67
import SigGolfCandidate.Hypertree.GroupedBalancedWire67
import SigGolfCandidate.Memory

/-! Reading one aligned 16-byte witness digest from the loaded wire. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyWireDigest67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private theorem extractByte_eq (v : Word) (k : Nat) :
    extractByte v k = v.extractLsb' (8*k) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [extractByte,BitVec.extractLsb',BitVec.toNat_ushiftRight,
    BitVec.toNat_setWidth,Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm k 8]

theorem pair_byte (s : MachineState) (base j : Nat)
    (aligned : base % 8 = 0) (bound : base+16 < 2^64)
    (hj : j < 16) :
    s.getByte (BitVec.ofNat 64 (base+j)) =
      (s.getMem (BitVec.ofNat 64 (base+8)) ++
        s.getMem (BitVec.ofNat 64 base)).extractLsb' (8*j) 8 := by
  have baseBound : base < 2^64 := by omega
  have halign : (BitVec.ofNat 64 base).toNat % 8 = 0 := by
    simpa [Nat.mod_eq_of_lt baseBound] using aligned
  have hover : (BitVec.ofNat 64 base).toNat+j < 2^64 := by
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt baseBound]
    omega
  rw [show BitVec.ofNat 64 (base+j) =
    BitVec.ofNat 64 base + BitVec.ofNat 64 j from
      BitVec.ofNat_add _ _]
  simp only [MachineState.getByte,
    alignToDword_add_ofNat_of_aligned halign hover,
    byteOffset_add_ofNat_of_aligned halign hover]
  by_cases small : j < 8
  · have div : j/8 = 0 := by omega
    have mod : j%8 = j := by omega
    simp only [div,mod,Nat.mul_zero]
    have haddr : BitVec.ofNat 64 base + BitVec.ofNat 64 0 =
        BitVec.ofNat 64 base := by simp
    rw [haddr]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by omega : 8*j+8 ≤ 64)]
    exact extractByte_eq _ _
  · have div : j/8 = 1 := by omega
    have mod : j%8 = j-8 := by omega
    simp only [div,mod,Nat.mul_one]
    rw [← BitVec.ofNat_add]
    rw [BitVec.extractLsb'_append_eq_of_le (by omega : 64 ≤ 8*j)]
    have pos : 8*j-64 = 8*(j-8) := by omega
    rw [pos]
    exact extractByte_eq _ _

theorem pair_read (s : MachineState) (base : Nat)
    (aligned : base % 8 = 0) (bound : base+16 < 2^64) :
    readBuffer s base 16 =
      s.getMem (BitVec.ofNat 64 (base+8)) ++
        s.getMem (BitVec.ofNat 64 base) := by
  apply SigGolfCandidate.Memory.readBuffer_of_bytes
  intro i hi
  exact pair_byte s base i aligned bound hi

theorem slice_byte (wire : Bytes 50848) (offset j : Nat)
    (bound : offset+16 ≤ 50848) (hj : j < 16) :
    (SignatureEncoding.slice wire offset 16).extractLsb' (8*j) 8 =
      (bytes wire)[offset+j]'(by rw [SigGolfCandidate.Memory.bytes_length]; omega) := by
  simp only [SignatureEncoding.slice,bytes,List.getElem_map,List.getElem_range]
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  simp only [BitVec.getLsbD_extractLsb',
    show 8*j+bit < 128 by omega,decide_true,Bool.true_and,
    show 8*offset+(8*j+bit) < 8*50848 by omega,
    show 8*(offset+j)+bit < 8*50848 by omega]
  rw [show 8*offset+(8*j+bit) = 8*(offset+j)+bit by omega]

theorem pair_eq_slice (s : MachineState) (wire : Bytes 50848)
    (base offset : Nat) (aligned : base % 8 = 0)
    (baseBound : base+16 < 2^64) (wireBound : offset+16 ≤ 50848)
    (byteEq : ∀ (j : Nat) (hj : j < 16),
      s.getByte (BitVec.ofNat 64 (base+j)) =
        (bytes wire)[offset+j]'(by
          rw [SigGolfCandidate.Memory.bytes_length]
          omega)) :
    s.getMem (BitVec.ofNat 64 (base+8)) ++
      s.getMem (BitVec.ofNat 64 base) =
        SignatureEncoding.slice wire offset 16 := by
  have fromWords := pair_read s base aligned baseBound
  have fromWire : readBuffer s base 16 =
      SignatureEncoding.slice wire offset 16 := by
    apply SigGolfCandidate.Memory.readBuffer_of_bytes
    intro j hj
    rw [byteEq j hj]
    exact (slice_byte wire offset j wireBound hj).symm
  exact fromWords.symm.trans fromWire

#print axioms pair_byte
#print axioms pair_eq_slice
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyWireDigest67
