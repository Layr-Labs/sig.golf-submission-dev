import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoopStart67
import SigGolfCandidate.Hypertree.KeygenCopyFrame

/-! Stack pointer preservation across the 72-instruction bottom-leaf setup. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSetupStack67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
private abbrev image := GroupedBalancedSignImage67.image

theorem upper_copy_sp (s final : MachineState) (pc : s.pc = 0x1220)
    (trace : OrdinarySteps image s 17 final) :
    final.getReg .x2 = s.getReg .x2 := by
  let begun := GroupedBalancedSignBottomCopies67.upperSetup s
  obtain ⟨other,loop,_,_,_,_,sp⟩ := Keygen.copy_all_frame image 0x1234
    GroupedBalancedSignBottomCopies67.upper_copy_code 0x81098 0x810b0 2 begun
    (GroupedBalancedSignBottomCopies67.upper_copy_inv s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have setup := GroupedBalancedSignBottomCopies67.upper_setup_steps s pc
  have constructed : OrdinarySteps image s 17 other := by
    simpa only [show 5+12=17 by decide] using
      Keygen.ordinary_trans image s begun other 5 12 setup loop
  have same := Keygen.ordinary_deterministic trace constructed
  rw [same,sp]
  simp [begun,GroupedBalancedSignBottomCopies67.upperSetup,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem base_copy_sp (s final : MachineState) (pc : s.pc = 0x124c)
    (trace : OrdinarySteps image s 23 final) :
    final.getReg .x2 = s.getReg .x2 := by
  let begun := GroupedBalancedSignBottomCopies67.baseSetup s
  obtain ⟨other,loop,_,_,_,_,sp⟩ := Keygen.copy_all_frame image 0x1260
    GroupedBalancedSignBottomCopies67.base_copy_code 0x810a8 0x81008 3 begun
    (GroupedBalancedSignBottomCopies67.base_copy_inv s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have setup := GroupedBalancedSignBottomCopies67.base_setup_steps s pc
  have constructed : OrdinarySteps image s 23 other := by
    simpa only [show 5+18=23 by decide] using
      Keygen.ordinary_trans image s begun other 5 18 setup loop
  have same := Keygen.ordinary_deterministic trace constructed
  rw [same,sp]
  simp [begun,GroupedBalancedSignBottomCopies67.baseSetup,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem setup_sp (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x11f4)
    (trace : Trace hash image s 72 72 0 0 final) :
    final.getReg .x2 = s.getReg .x2 := by
  let entry := GroupedBalancedSignBottomEntry67.entryState s
  have entrySteps := GroupedBalancedSignBottomEntry67.entry_steps s pc
  have entryPc := GroupedBalancedSignBottomEntry67.entry_pc s pc
  obtain ⟨upper,upperSteps,upperPc,_,_⟩ :=
    GroupedBalancedSignBottomCopies67.upper_copy entry entryPc
  obtain ⟨lower,lowerSteps,lowerPc,_,_⟩ :=
    GroupedBalancedSignBottomCopies67.base_copy upper upperPc
  let initialized := GroupedBalancedSignBottomBuilderInit67.initState lower
  have initSteps := GroupedBalancedSignBottomBuilderInit67.init_steps lower lowerPc
  have constructed : Trace hash image s 72 72 0 0 initialized := by
    simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (((OrdinarySteps.trace (hash := hash) entrySteps).trans
        (OrdinarySteps.trace (hash := hash) upperSteps)).trans
        (OrdinarySteps.trace (hash := hash) lowerSteps)).trans
        (OrdinarySteps.trace (hash := hash) initSteps)
  have same := Trace.deterministic trace constructed
  rw [same]
  have initSp : initialized.getReg .x2 = lower.getReg .x2 := by
    simp [initialized,GroupedBalancedSignBottomBuilderInit67.initState,
      execInstrBr,MachineState.getReg_setReg_ne]
  have entrySp : entry.getReg .x2 = s.getReg .x2 := by
    simp [entry,GroupedBalancedSignBottomEntry67.entryState,
      execInstrBr,MachineState.getReg_setReg_ne]
  exact initSp.trans ((base_copy_sp upper lower upperPc lowerSteps).trans
    ((upper_copy_sp entry upper entryPc upperSteps).trans entrySp))

#print axioms setup_sp
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSetupStack67
