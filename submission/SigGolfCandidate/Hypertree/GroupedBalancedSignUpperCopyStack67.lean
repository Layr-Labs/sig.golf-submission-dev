import SigGolfCandidate.Hypertree.KeygenCopyX2X19
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCopiesH367
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCopiesH467

/-! Stack preservation for a setup followed by a fixed-width copy loop. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCopyStack67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.Keygen
private abbrev image := GroupedBalancedSignImage67Byte.image
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem copy_sp_from_setup (image : Image) (p : Word)
    (code : CopyCode image p) (source destination total setupLength : Nat)
    (s begun final : MachineState)
    (setupSteps : OrdinarySteps image s setupLength begun)
    (setupSp : begun.getReg .x2=s.getReg .x2)
    (inv : CopyInvariant p source destination total total begun)
    (srcbound : source + 8*total ≤ MEMORY_BYTES)
    (dstbound : destination + 8*total ≤ MEMORY_BYTES)
    (srcalign : source%8=0) (dstalign : destination%8=0)
    (allSteps : OrdinarySteps image s (setupLength+6*total) final) :
    final.getReg .x2=s.getReg .x2 := by
  obtain ⟨other,loop,loopSp⟩ :=
    KeygenCopyX2X19.copy_loop_x2 image p code source destination total
      total begun inv srcbound dstbound srcalign dstalign
  have path : OrdinarySteps image s (setupLength+6*total) other := by
    simpa only [Nat.add_comm] using
      Keygen.ordinary_trans image s begun other setupLength (6*total)
        setupSteps loop
  have eq := Keygen.ordinary_deterministic allSteps path
  subst other
  exact loopSp.trans setupSp

theorem upper_h3_sp (s final : MachineState) (pc : s.pc=0x1620)
    (path : OrdinarySteps image s 17 final) :
    final.getReg .x2=s.getReg .x2 := by
  let begun := GroupedBalancedSignUpperCopiesH367.upperSetup s
  have setupSp : begun.getReg .x2=s.getReg .x2 := by
    simp [begun,GroupedBalancedSignUpperCopiesH367.upperSetup,
      execInstrBr,MachineState.getReg_setReg_ne]
  exact copy_sp_from_setup image 0x1634
    GroupedBalancedSignUpperCopiesH367.upper_copy_code 0x81098 0x810b0
    2 5 s begun final
    (GroupedBalancedSignUpperCopiesH367.upper_setup_steps s pc)
    setupSp (GroupedBalancedSignUpperCopiesH367.upper_copy_inv s pc)
    (by decide) (by decide) (by decide) (by decide) (by simpa using path)

theorem base_h3_sp (s final : MachineState) (pc : s.pc=0x164c)
    (path : OrdinarySteps image s 23 final) :
    final.getReg .x2=s.getReg .x2 := by
  let begun := GroupedBalancedSignUpperCopiesH367.baseSetup s
  have setupSp : begun.getReg .x2=s.getReg .x2 := by
    simp [begun,GroupedBalancedSignUpperCopiesH367.baseSetup,
      execInstrBr,MachineState.getReg_setReg_ne]
  exact copy_sp_from_setup image 0x1660
    GroupedBalancedSignUpperCopiesH367.base_copy_code 0x810a8 0x81008
    3 5 s begun final
    (GroupedBalancedSignUpperCopiesH367.base_setup_steps s pc)
    setupSp (GroupedBalancedSignUpperCopiesH367.base_copy_inv s pc)
    (by decide) (by decide) (by decide) (by decide) (by simpa using path)

theorem upper_h4_sp (s final : MachineState) (pc : s.pc=0x16b8)
    (path : OrdinarySteps image s 17 final) :
    final.getReg .x2=s.getReg .x2 := by
  let begun := GroupedBalancedSignUpperCopiesH467.upperSetup s
  have setupSp : begun.getReg .x2=s.getReg .x2 := by
    simp [begun,GroupedBalancedSignUpperCopiesH467.upperSetup,
      execInstrBr,MachineState.getReg_setReg_ne]
  exact copy_sp_from_setup image 0x16cc
    GroupedBalancedSignUpperCopiesH467.upper_copy_code 0x81098 0x810b0
    2 5 s begun final
    (GroupedBalancedSignUpperCopiesH467.upper_setup_steps s pc)
    setupSp (GroupedBalancedSignUpperCopiesH467.upper_copy_inv s pc)
    (by decide) (by decide) (by decide) (by decide) (by simpa using path)

theorem base_h4_sp (s final : MachineState) (pc : s.pc=0x16e4)
    (path : OrdinarySteps image s 23 final) :
    final.getReg .x2=s.getReg .x2 := by
  let begun := GroupedBalancedSignUpperCopiesH467.baseSetup s
  have setupSp : begun.getReg .x2=s.getReg .x2 := by
    simp [begun,GroupedBalancedSignUpperCopiesH467.baseSetup,
      execInstrBr,MachineState.getReg_setReg_ne]
  exact copy_sp_from_setup image 0x16f8
    GroupedBalancedSignUpperCopiesH467.base_copy_code 0x810a8 0x81008
    3 5 s begun final
    (GroupedBalancedSignUpperCopiesH467.base_setup_steps s pc)
    setupSp (GroupedBalancedSignUpperCopiesH467.base_copy_inv s pc)
    (by decide) (by decide) (by decide) (by decide) (by simpa using path)

#print axioms copy_sp_from_setup
#print axioms upper_h3_sp
#print axioms base_h3_sp
#print axioms upper_h4_sp
#print axioms base_h4_sp
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCopyStack67
