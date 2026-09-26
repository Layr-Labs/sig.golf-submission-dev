import SigGolfCandidate.Hypertree.KeygenCopyX19

/-! The fixed-width copy loop leaves the signer stack pointer intact. -/
namespace SigGolfCandidate.Hypertree.KeygenCopyX2X19
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.Keygen
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem loop_next_x2 (s : MachineState) :
    (Expansion.loopNext s).getReg .x2 = s.getReg .x2 := by
  simp [Expansion.loopNext,Expansion.loopBody,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem copy_loop_x2 (image : Image) (p : Word)
    (code : CopyCode image p)
    (source destination total n : Nat) (s : MachineState)
    (inv : CopyInvariant p source destination total n s)
    (srcbound : source + 8*total ≤ MEMORY_BYTES)
    (dstbound : destination + 8*total ≤ MEMORY_BYTES)
    (srcalign : source%8=0) (dstalign : destination%8=0) :
    ∃ final, OrdinarySteps image s (6*n) final ∧
      final.getReg .x2=s.getReg .x2 := by
  induction n generalizing s with
  | zero => exact ⟨s,OrdinarySteps.refl _,rfl⟩
  | succ n ih =>
      have access := copy_accesses p source destination total n s inv
        srcbound dstbound srcalign dstalign
      have block := copy_block image p code s
        (by simpa using inv.2.2.1) access.1 access.2
      obtain ⟨final,tail,sp⟩ := ih (Expansion.loopNext s)
        (copy_invariant_next p source destination total n s inv)
      refine ⟨final,?_,sp.trans (loop_next_x2 s)⟩
      simpa only [Nat.mul_add,Nat.mul_one] using
        ordinary_trans image s _ final 6 (6*n) block tail

theorem copy_all_x19_x2 (image : Image) (p : Word)
    (code : CopyCode image p)
    (source destination total : Nat) (s : MachineState)
    (inv : CopyInvariant p source destination total total s)
    (srcbound : source + 8*total ≤ MEMORY_BYTES)
    (dstbound : destination + 8*total ≤ MEMORY_BYTES)
    (srcalign : source%8=0) (dstalign : destination%8=0)
    (separate : source+8*total≤destination ∨
      destination+8*total≤source) :
    ∃ final, OrdinarySteps image s (6*total) final ∧
      CopyInvariant p source destination total 0 final ∧
      (∀ i, i<total → final.getMem (Signing.wordAddress destination i)=
        s.getMem (Signing.wordAddress source i)) ∧
      (∀ a, (∀ i, i<total → a≠Signing.wordAddress destination i) →
        final.getMem a=s.getMem a) ∧
      final.getReg .x19=s.getReg .x19 ∧
      final.getReg .x2=s.getReg .x2 := by
  obtain ⟨final,first,done,words,frame,x19⟩ :=
    KeygenCopyX19.copy_all_x19 image p code source destination total s
      inv srcbound dstbound srcalign dstalign separate
  obtain ⟨other,second,x2⟩ :=
    copy_loop_x2 image p code source destination total total s inv
      srcbound dstbound srcalign dstalign
  have eq := Keygen.ordinary_deterministic first second
  subst other
  exact ⟨final,first,done,words,frame,x19,x2⟩

#print axioms copy_all_x19_x2
end SigGolfCandidate.Hypertree.KeygenCopyX2X19
