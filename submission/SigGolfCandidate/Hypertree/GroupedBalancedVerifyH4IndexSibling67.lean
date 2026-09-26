import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyStackGlobal67

/-! Both H4 sibling-order paths preserve the verifier's index scratch words. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexSibling67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyH4IndexFrame67
open GroupedBalancedVerifyTreeHighFrame67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem jump_index (s : MachineState) :
    IndexFrame s (execInstrBr s (.JAL .x0 84)) := by
  intro i
  simp [execInstrBr]

theorem nonzero_path_index (s final : MachineState) (p : Word)
    (pc : s.pc = 0x1314) (pointer : s.getMem 0x81048 = p)
    (valid0 : accessValid p 8 = true)
    (valid8 : accessValid (p+8) 8 = true)
    (run : OrdinarySteps image s 27 final) :
    IndexFrame s final := by
  obtain ⟨copied,copyRun,copyPC,_,copyPointer,_,_⟩ :=
    GroupedBalancedVerifyTreeSiblingNonzero67.copy_current s pc
  have copiedPointer : copied.getMem 0x81048 = p := copyPointer.trans pointer
  let staged := GroupedBalancedVerifyTreeSiblingNonzero67.siblingState copied
  have siblingRun :=
    GroupedBalancedVerifyTreeSiblingNonzero67.sibling_steps copied p copyPC
      copiedPointer valid0 valid8
  have stagedPC := GroupedBalancedVerifyTreeSiblingNonzero67.sibling_pc copied copyPC
  have jumpRun := GroupedBalancedVerifyTreeSiblingNonzero67.jump_step staged stagedPC
  have expected : OrdinarySteps image s 27
      (execInstrBr staged (.JAL .x0 84)) := by
    have first := Keygen.ordinary_trans image s copied staged 17 9
      copyRun siblingRun
    have all := Keygen.ordinary_trans image s staged _ 26 1
      (by simpa only [Nat.reduceAdd] using first) jumpRun
    simpa only [Nat.reduceAdd] using all
  have same := Keygen.ordinary_deterministic run expected
  subst final
  exact index_trans
    (index_trans (nonzero_copy_index s copied pc copyRun)
      (nonzero_sibling_index copied))
    (jump_index staged)

theorem zero_path_index (s final : MachineState) (p : Word)
    (pc : s.pc = 0x1368) (pointer : s.getMem 0x81048 = p)
    (valid0 : accessValid p 8 = true)
    (valid8 : accessValid (p+8) 8 = true)
    (run : OrdinarySteps image s 26 final) :
    IndexFrame s final := by
  obtain ⟨copied,copyRun,copyPC,_,copyPointer,_,_⟩ :=
    GroupedBalancedVerifyTreeSiblingZero67.copy_current s pc
  have copiedPointer : copied.getMem 0x81048 = p := copyPointer.trans pointer
  let staged := GroupedBalancedVerifyTreeSiblingZero67.siblingState copied
  have siblingRun :=
    GroupedBalancedVerifyTreeSiblingZero67.sibling_steps copied p copyPC
      copiedPointer valid0 valid8
  have expected : OrdinarySteps image s 26 staged := by
    have all := Keygen.ordinary_trans image s copied staged 17 9
      copyRun siblingRun
    simpa only [Nat.reduceAdd] using all
  have same := Keygen.ordinary_deterministic run expected
  subst final
  exact index_trans (zero_copy_index s copied pc copyRun)
    (zero_sibling_index copied)

theorem nonzero_path_base (s final : MachineState) (p : Word)
    (pc : s.pc = 0x1314) (pointer : s.getMem 0x81048 = p)
    (valid0 : accessValid p 8 = true)
    (valid8 : accessValid (p+8) 8 = true)
    (run : OrdinarySteps image s 27 final) :
    final.getMem 0x81000 = s.getMem 0x81000 := by
  obtain ⟨copied,copyRun,copyPC,_,copyPointer,_,_⟩ :=
    GroupedBalancedVerifyTreeSiblingNonzero67.copy_current s pc
  let staged := GroupedBalancedVerifyTreeSiblingNonzero67.siblingState copied
  have stagedRun := GroupedBalancedVerifyTreeSiblingNonzero67.sibling_steps
    copied p copyPC (copyPointer.trans pointer) valid0 valid8
  have stagedPC := GroupedBalancedVerifyTreeSiblingNonzero67.sibling_pc copied copyPC
  have jumpRun := GroupedBalancedVerifyTreeSiblingNonzero67.jump_step staged stagedPC
  have expected : OrdinarySteps image s 27
      (execInstrBr staged (.JAL .x0 84)) := by
    have first := Keygen.ordinary_trans image s copied staged 17 9
      copyRun stagedRun
    have all := Keygen.ordinary_trans image s staged _ 26 1
      (by simpa only [Nat.reduceAdd] using first) jumpRun
    simpa only [Nat.reduceAdd] using all
  have same := Keygen.ordinary_deterministic run expected
  subst final
  calc
    (execInstrBr staged (.JAL .x0 84)).getMem 0x81000 =
        staged.getMem 0x81000 := by simp [execInstrBr]
    _ = copied.getMem 0x81000 :=
      GroupedBalancedVerifyTreeH4Base67.nonzero_sibling_base copied
    _ = s.getMem 0x81000 :=
      GroupedBalancedVerifyTreeH4Base67.nonzero_copy_base s copied pc copyRun

theorem zero_path_base (s final : MachineState) (p : Word)
    (pc : s.pc = 0x1368) (pointer : s.getMem 0x81048 = p)
    (valid0 : accessValid p 8 = true)
    (valid8 : accessValid (p+8) 8 = true)
    (run : OrdinarySteps image s 26 final) :
    final.getMem 0x81000 = s.getMem 0x81000 := by
  obtain ⟨copied,copyRun,copyPC,_,copyPointer,_,_⟩ :=
    GroupedBalancedVerifyTreeSiblingZero67.copy_current s pc
  let staged := GroupedBalancedVerifyTreeSiblingZero67.siblingState copied
  have stagedRun := GroupedBalancedVerifyTreeSiblingZero67.sibling_steps
    copied p copyPC (copyPointer.trans pointer) valid0 valid8
  have expected : OrdinarySteps image s 26 staged := by
    have all := Keygen.ordinary_trans image s copied staged 17 9
      copyRun stagedRun
    simpa only [Nat.reduceAdd] using all
  have same := Keygen.ordinary_deterministic run expected
  subst final
  exact (GroupedBalancedVerifyTreeH4Base67.zero_sibling_base copied).trans
    (GroupedBalancedVerifyTreeH4Base67.zero_copy_base s copied pc copyRun)

theorem nonzero_path_low (s final : MachineState) (p : Word)
    (pc : s.pc = 0x1314) (pointer : s.getMem 0x81048 = p)
    (valid0 : accessValid p 8 = true)
    (valid8 : accessValid (p+8) 8 = true)
    (run : OrdinarySteps image s 27 final) :
    GroupedBalancedVerifyStackGlobal67.LowFrame s final := by
  obtain ⟨copied,copyRun,copyPC,_,copyPointer,_,_⟩ :=
    GroupedBalancedVerifyTreeSiblingNonzero67.copy_current s pc
  let staged := GroupedBalancedVerifyTreeSiblingNonzero67.siblingState copied
  have stagedRun := GroupedBalancedVerifyTreeSiblingNonzero67.sibling_steps
    copied p copyPC (copyPointer.trans pointer) valid0 valid8
  have stagedPC := GroupedBalancedVerifyTreeSiblingNonzero67.sibling_pc copied copyPC
  have jumpRun := GroupedBalancedVerifyTreeSiblingNonzero67.jump_step staged stagedPC
  have expected : OrdinarySteps image s 27
      (execInstrBr staged (.JAL .x0 84)) := by
    have first := Keygen.ordinary_trans image s copied staged 17 9
      copyRun stagedRun
    have all := Keygen.ordinary_trans image s staged _ 26 1
      (by simpa only [Nat.reduceAdd] using first) jumpRun
    simpa only [Nat.reduceAdd] using all
  have same := Keygen.ordinary_deterministic run expected
  subst final
  have h0 := GroupedBalancedVerifyTreeH4Base67.nonzero_copy_low
    s copied pc copyRun
  have h1 := GroupedBalancedVerifyTreeH4Base67.nonzero_sibling_low copied
  exact (h0.trans h1).trans (by
    intro a _
    simp [staged,execInstrBr])

theorem zero_path_low (s final : MachineState) (p : Word)
    (pc : s.pc = 0x1368) (pointer : s.getMem 0x81048 = p)
    (valid0 : accessValid p 8 = true)
    (valid8 : accessValid (p+8) 8 = true)
    (run : OrdinarySteps image s 26 final) :
    GroupedBalancedVerifyStackGlobal67.LowFrame s final := by
  obtain ⟨copied,copyRun,copyPC,_,copyPointer,_,_⟩ :=
    GroupedBalancedVerifyTreeSiblingZero67.copy_current s pc
  let staged := GroupedBalancedVerifyTreeSiblingZero67.siblingState copied
  have stagedRun := GroupedBalancedVerifyTreeSiblingZero67.sibling_steps
    copied p copyPC (copyPointer.trans pointer) valid0 valid8
  have expected : OrdinarySteps image s 26 staged := by
    have all := Keygen.ordinary_trans image s copied staged 17 9
      copyRun stagedRun
    simpa only [Nat.reduceAdd] using all
  have same := Keygen.ordinary_deterministic run expected
  subst final
  exact (GroupedBalancedVerifyTreeH4Base67.zero_copy_low s copied pc copyRun).trans
    (GroupedBalancedVerifyTreeH4Base67.zero_sibling_low copied)

theorem sibling_paths_index (s : MachineState) (p : Word)
    (pc : s.pc = 0x1314 ∨ s.pc = 0x1368)
    (pointer : s.getMem 0x81048 = p)
    (valid0 : accessValid p 8 = true)
    (valid8 : accessValid (p+8) 8 = true) :
    ∃ n final, (n = 26 ∨ n = 27) ∧ OrdinarySteps image s n final ∧
      final.pc = 0x13b8 ∧ final.getMem 0x81048 = p ∧
      final.getMem 0x81050 = s.getMem 0x81050 ∧
      SafeFrame s final ∧ IndexFrame s final ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      GroupedBalancedVerifyStackGlobal67.LowFrame s final := by
  rcases pc with nonzero | zero
  · obtain ⟨final,run,endPC,endPointer,endCount,safe⟩ :=
      GroupedBalancedVerifyTreeSiblingNonzero67.nonzero_path s p
        nonzero pointer valid0 valid8
    exact ⟨27,final,Or.inr rfl,run,endPC,endPointer,endCount,safe,
      nonzero_path_index s final p nonzero pointer valid0 valid8 run,
      nonzero_path_base s final p nonzero pointer valid0 valid8 run,
      nonzero_path_low s final p nonzero pointer valid0 valid8 run⟩
  · obtain ⟨final,run,endPC,endPointer,endCount,safe⟩ :=
      GroupedBalancedVerifyTreeSiblingZero67.zero_path s p
        zero pointer valid0 valid8
    exact ⟨26,final,Or.inl rfl,run,endPC,endPointer,endCount,safe,
      zero_path_index s final p zero pointer valid0 valid8 run,
      zero_path_base s final p zero pointer valid0 valid8 run,
      zero_path_low s final p zero pointer valid0 valid8 run⟩

#print axioms sibling_paths_index
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexSibling67
