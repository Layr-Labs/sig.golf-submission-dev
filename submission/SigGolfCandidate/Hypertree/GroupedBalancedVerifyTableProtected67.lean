import SigGolfCandidate.Hypertree.GroupedBalancedByteFastWotsFrameAll67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeHighFrame67

/-! The WOTS memory frame includes the immutable decoder table. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyTableProtected67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem table_aligned_protected (i : Nat) (hi : i < 2304) :
    GroupedBalancedByteFastWotsProtected67.Protected
      (alignToDword (BitVec.ofNat 64 (0xfff700+i))) := by
  apply Or.inr
  apply Or.inr
  have h := alignToDword_add_ofNat_of_aligned
    (base := 0#64) (i := 0xfff700+i) (by decide) (by simp; omega)
  have he : alignToDword (BitVec.ofNat 64 (0xfff700+i)) =
      BitVec.ofNat 64 (8*((0xfff700+i)/8)) := by
    simpa using h
  rw [he,BitVec.toNat_ofNat]
  have bound : 8*((0xfff700+i)/8) < 2^64 := by omega
  rw [Nat.mod_eq_of_lt bound]
  omega

theorem tables_of_protected {s t : MachineState}
    (frame : ∀ a : Word,
      GroupedBalancedByteFastWotsProtected67.Protected a →
      t.getMem a = s.getMem a)
    (tables : GroupedBalancedVerifyByteContract67.Tables s) :
    GroupedBalancedVerifyByteContract67.Tables t := by
  intro i hi
  have mem := frame (alignToDword (BitVec.ofNat 64 (0xfff700+i)))
    (table_aligned_protected i hi)
  simpa only [MachineState.getByte,mem] using tables i hi

theorem tables_of_table_frame {s t : MachineState}
    (frame : ∀ a : Word, 0xfff700 ≤ a.toNat →
      t.getMem a = s.getMem a)
    (tables : GroupedBalancedVerifyByteContract67.Tables s) :
    GroupedBalancedVerifyByteContract67.Tables t := by
  intro i hi
  have h : 0xfff700 ≤
      (alignToDword (BitVec.ofNat 64 (0xfff700+i))).toNat := by
    have aligned := alignToDword_add_ofNat_of_aligned
      (base := 0#64) (i := 0xfff700+i) (by decide) (by simp; omega)
    have he : alignToDword (BitVec.ofNat 64 (0xfff700+i)) =
        BitVec.ofNat 64 (8*((0xfff700+i)/8)) := by
      simpa using aligned
    rw [he,BitVec.toNat_ofNat]
    have bound : 8*((0xfff700+i)/8) < 2^64 := by omega
    rw [Nat.mod_eq_of_lt bound]
    omega
  have mem := frame (alignToDword (BitVec.ofNat 64 (0xfff700+i))) h
  simpa only [MachineState.getByte,mem] using tables i hi

#print axioms tables_of_protected
#print axioms tables_of_table_frame
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyTableProtected67
