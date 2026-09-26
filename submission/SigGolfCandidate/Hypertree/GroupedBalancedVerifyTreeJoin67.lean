import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeSiblingNonzero67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeSiblingZero67

/-! Both sibling-order paths reach the common H4 input preparation. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeJoin67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyTreeHighFrame67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67Byte.submission

theorem sibling_paths (s : MachineState) (p : Word)
    (pc : s.pc = 0x1314 ∨ s.pc = 0x1368)
    (pointer : s.getMem 0x81048 = p)
    (valid0 : accessValid p 8 = true)
    (valid8 : accessValid (p+8) 8 = true) :
    ∃ n final, (n = 26 ∨ n = 27) ∧ OrdinarySteps image s n final ∧
      final.pc = 0x13b8 ∧ final.getMem 0x81048 = p ∧
      final.getMem 0x81050 = s.getMem 0x81050 ∧
      SafeFrame s final := by
  rcases pc with nonzero | zero
  · obtain ⟨final,run,endPC,endPointer,endCount,safe⟩ :=
      GroupedBalancedVerifyTreeSiblingNonzero67.nonzero_path s p nonzero pointer valid0 valid8
    exact ⟨27,final,Or.inr rfl,run,endPC,endPointer,endCount,safe⟩
  · obtain ⟨final,run,endPC,endPointer,endCount,safe⟩ :=
      GroupedBalancedVerifyTreeSiblingZero67.zero_path s p zero pointer valid0 valid8
    exact ⟨26,final,Or.inl rfl,run,endPC,endPointer,endCount,safe⟩

theorem loaded_join (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial n final,
      initialState program .verify input = some initial ∧
      (n = 277 ∨ n = 278) ∧
      Trace hash image initial n (n+22) 2 3 final ∧
      final.pc = 0x13b8 ∧ final.getMem 0x81048 = 0x2c730 := by
  obtain ⟨initial,branch,loaded,first,branchPC,pointer⟩ :=
    GroupedBalancedVerifyTreeBranch67.loaded_branch hash input
  obtain ⟨n,final,ncases,run,endPC,endPointer,_,_⟩ := sibling_paths branch 0x2c730
    branchPC pointer (by decide) (by decide)
  refine ⟨initial,251+n,final,loaded,?_,?_,endPC,endPointer⟩
  · rcases ncases with h | h <;> simp [h]
  · have all := first.trans run.trace
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all

#print axioms loaded_join
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeJoin67
