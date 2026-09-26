import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexHeader67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Base67

/-! Preserve the verifier's 192-bit index scratch words outside the tree
round header. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyH4IndexHeader67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

def IndexFrame (s t : MachineState) : Prop :=
  ∀ i : Fin 3,
    t.getMem (Signing.wordAddress 0x81008 i.val) =
      s.getMem (Signing.wordAddress 0x81008 i.val)

theorem index_refl (s : MachineState) : IndexFrame s s := by
  intro _
  rfl

theorem index_trans {s t u : MachineState}
    (first : IndexFrame s t) (second : IndexFrame t u) :
    IndexFrame s u := by
  intro i
  exact (second i).trans (first i)

theorem stored_of_frame {s t : MachineState} {index : BitVec 192}
    (frame : IndexFrame s t) (stored : StoredIndex s index) :
    StoredIndex t index := by
  intro i
  exact (frame i).trans (stored i)

theorem branch_index (s : MachineState) :
    IndexFrame s (execInstrBr s (.BEQ .x6 .x0 88)) := by
  intro i
  simp [execInstrBr]

theorem nonzero_sibling_index (s : MachineState) :
    IndexFrame s (GroupedBalancedVerifyTreeSiblingNonzero67.siblingState s) := by
  intro i
  fin_cases i <;>
    simp [GroupedBalancedVerifyTreeSiblingNonzero67.siblingState,
      execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_ne,Signing.wordAddress]

theorem zero_sibling_index (s : MachineState) :
    IndexFrame s (GroupedBalancedVerifyTreeSiblingZero67.siblingState s) := by
  intro i
  fin_cases i <;>
    simp [GroupedBalancedVerifyTreeSiblingZero67.siblingState,
      execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_ne,Signing.wordAddress]

theorem h4_header_index (s : MachineState) :
    IndexFrame s (GroupedBalancedVerifyTreeH4Header67.headerState s) := by
  intro i
  fin_cases i <;>
    simp [GroupedBalancedVerifyTreeH4Header67.headerState,
      execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_ne,Signing.wordAddress]

theorem tail_index (s : MachineState) :
    IndexFrame s (GroupedBalancedVerifyTreeH4Tail67.updateState s) := by
  intro i
  fin_cases i <;>
    exact GroupedBalancedVerifyTreeH4Tail67.update_mem s _
      (by decide) (by decide) (by decide)

theorem hash_index (hash : Hash) (s : MachineState)
    (fields : GroupedBalancedVerifyTreeH4Query67.Fields s) :
    IndexFrame s (writeHash s (hash (hashInput s))) := by
  intro i
  fin_cases i <;>
    simp [writeHash,fields.destination,Signing.wordAddress]

private theorem nonzero_setup_code :
    Keygen.CopySetupCode image 0x1314 0x500 0x530 2 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopySetupCode
  decide

private theorem nonzero_copy_code : Keygen.CopyCode image 0x1328 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

private theorem zero_setup_code :
    Keygen.CopySetupCode image 0x1368 0x500 0x520 2 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopySetupCode
  decide

private theorem zero_copy_code : Keygen.CopyCode image 0x137c := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

private theorem answer_setup_code :
    Keygen.CopySetupCode image 0x146c 0x300 0x500 2 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopySetupCode
  decide

private theorem answer_copy_code : Keygen.CopyCode image 0x1480 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

theorem nonzero_copy_index (s mid : MachineState)
    (pc : s.pc = 0x1314) (run : OrdinarySteps image s 17 mid) :
    IndexFrame s mid := by
  obtain ⟨other,otherRun,_,_,_,_,frame⟩ :=
    Keygen.copy_two image 0x1314 0x500 0x530 0x80500 0x80530
      nonzero_setup_code nonzero_copy_code (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) s pc
  have same := Keygen.ordinary_deterministic run otherRun
  subst other
  intro i
  exact frame _ (by intro j; fin_cases i <;> fin_cases j <;> decide)

theorem zero_copy_index (s mid : MachineState)
    (pc : s.pc = 0x1368) (run : OrdinarySteps image s 17 mid) :
    IndexFrame s mid := by
  obtain ⟨other,otherRun,_,_,_,_,frame⟩ :=
    Keygen.copy_two image 0x1368 0x500 0x520 0x80500 0x80520
      zero_setup_code zero_copy_code (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) s pc
  have same := Keygen.ordinary_deterministic run otherRun
  subst other
  intro i
  exact frame _ (by intro j; fin_cases i <;> fin_cases j <;> decide)

theorem answer_copy_index (s mid : MachineState)
    (pc : s.pc = 0x146c) (run : OrdinarySteps image s 17 mid) :
    IndexFrame s mid := by
  obtain ⟨other,otherRun,_,_,_,_,frame⟩ :=
    Keygen.copy_two image 0x146c 0x300 0x500 0x80300 0x80500
      answer_setup_code answer_copy_code (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) s pc
  have same := Keygen.ordinary_deterministic run otherRun
  subst other
  intro i
  exact frame _ (by intro j; fin_cases i <;> fin_cases j <;> decide)

private theorem input_setup_code :
    Keygen.CopySetupCode image 0x13b8 0x520 0x20 4 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopySetupCode
  decide

private theorem input_copy_code : Keygen.CopyCode image 0x13cc := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

theorem input_copy_index (s final : MachineState)
    (pc : s.pc = 0x13b8) (run : OrdinarySteps image s 29 final) :
    IndexFrame s final := by
  let setup := Keygen.copySetup s 0x520 0x20 4
  have setupRun := Keygen.copy_setup_block image 0x13b8 0x520 0x20 4
    input_setup_code s pc
  have inv : Keygen.CopyInvariant 0x13cc 0x80520 0x80020 4 4 setup := by
    have regs := Keygen.copy_setup_regs s 0x520 0x20 4
    simp only [Keygen.CopyInvariant,setup,Keygen.copy_setup_pc,pc,
      regs.1,regs.2.1,regs.2.2]
    simp [signExtend12]
  obtain ⟨other,copyRun,_,_,frame,_,_⟩ :=
    Keygen.copy_all_frame image 0x13cc input_copy_code
      0x80520 0x80020 4 setup inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have otherRun : OrdinarySteps image s 29 other := by
    have all := Keygen.ordinary_trans image s setup other 5 24
      setupRun copyRun
    simpa only [Nat.reduceAdd] using all
  have same := Keygen.ordinary_deterministic run otherRun
  subst other
  intro i
  rw [frame _ (by intro j hj; interval_cases j <;> fin_cases i <;> decide)]
  exact Keygen.copy_setup_mem s 0x520 0x20 4 _

#print axioms nonzero_sibling_index
#print axioms h4_header_index
#print axioms hash_index
#print axioms nonzero_copy_index
#print axioms zero_copy_index
#print axioms answer_copy_index
#print axioms input_copy_index
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexFrame67
