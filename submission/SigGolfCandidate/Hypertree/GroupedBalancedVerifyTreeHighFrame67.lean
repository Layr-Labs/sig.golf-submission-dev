import SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteContract67

/-! A common high-memory and stack frame for the predecoder verifier. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeHighFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def HighFrame (s t : MachineState) : Prop :=
  ∀ a : Word, 0x90000 ≤ a.toNat → t.getMem a = s.getMem a

def SafeFrame (s t : MachineState) : Prop :=
  HighFrame s t ∧ t.getReg .x2 = s.getReg .x2

theorem high_refl (s : MachineState) : HighFrame s s := by
  intro _ _
  rfl

theorem high_trans {s t u : MachineState}
    (first : HighFrame s t) (second : HighFrame t u) :
    HighFrame s u := by
  intro a ha
  exact (second a ha).trans (first a ha)

theorem safe_refl (s : MachineState) : SafeFrame s s :=
  ⟨high_refl s,rfl⟩

theorem safe_trans {s t u : MachineState}
    (first : SafeFrame s t) (second : SafeFrame t u) :
    SafeFrame s u :=
  ⟨high_trans first.1 second.1,second.2.trans first.2⟩

theorem table_aligned_high (i : Nat) (hi : i < 2304) :
    0x90000 ≤
      (alignToDword (BitVec.ofNat 64 (0xfff700+i))).toNat := by
  have h := alignToDword_add_ofNat_of_aligned
    (base := 0#64) (i := 0xfff700+i) (by decide) (by simp; omega)
  have he : alignToDword (BitVec.ofNat 64 (0xfff700+i)) =
      BitVec.ofNat 64 (8*((0xfff700+i)/8)) := by
    simpa using h
  rw [he,BitVec.toNat_ofNat]
  have bound : 8*((0xfff700+i)/8) < 2^64 := by omega
  rw [Nat.mod_eq_of_lt bound]
  omega

theorem tables_of_high {s t : MachineState}
    (frame : HighFrame s t)
    (tables : GroupedBalancedVerifyByteContract67.Tables s) :
    GroupedBalancedVerifyByteContract67.Tables t := by
  intro i hi
  have high := table_aligned_high i hi
  have mem := frame (alignToDword (BitVec.ofNat 64 (0xfff700+i))) high
  simpa only [MachineState.getByte,mem] using tables i hi

#print axioms tables_of_high
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeHighFrame67
