import SigGolfCandidate.Hypertree.BalancedPatchControl
import SigGolfCandidate.Hypertree.BalancedPatchSetup
import SigGolfCandidate.Hypertree.BalancedPatchWords
import SigGolfCandidate.Hypertree.BalancedPatchExit
import SigGolfCandidate.Hypertree.BalancedPatchRest
import SigGolfCandidate.Hypertree.BalancedPatchPC

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def noFlipResult (s : MachineState) (forward back : BitVec 21) : MachineState :=
  skipState (testState (entryState s forward)) back

theorem noFlip_block (image : Image) (entry start : Word) (forward back : BitVec 21)
    (code : PatchCode image entry start forward back)
    (s : MachineState) (pc : s.pc = entry)
    (forwardPC : entry + signExtend21 forward = start)
    (backPC : start+144+signExtend21 back = entry+4)
    (c : Nat) (bound : c ≤ 301) (sum : s.getReg .x12 = BitVec.ofNat 64 c)
    (noFlip : c < 151) :
    OrdinarySteps image s 6 (noFlipResult s forward back) ∧
    (noFlipResult s forward back).pc = entry+4 ∧
    (noFlipResult s forward back).getReg .x12 = BitVec.ofNat 64 c ∧
    (noFlipResult s forward back).getReg .x13 = BitVec.ofNat 64 c &&& 7 ∧
    (∀ a, (noFlipResult s forward back).getByte a = s.getByte a) ∧
    (noFlipResult s forward back).getReg .x10 = s.getReg .x10 ∧
    (noFlipResult s forward back).getReg .x1 = s.getReg .x1 ∧
    (noFlipResult s forward back).getReg .x2 = s.getReg .x2 := by
  have b1 := entry_block image entry start forward back code s pc
  have b2 := test_block image start
    (patch_test_code image entry start forward back code) (entryState s forward)
    (entry_pc s entry start forward pc forwardPC)
  have b3 := skip_block image entry start forward back code
    (testState (entryState s forward))
    (entry_test_skip_pc s entry start forward pc forwardPC c bound sum noFlip)
  refine ⟨Keygen.ordinary_trans image s _ _ 4 2
    (Keygen.ordinary_trans image s _ _ 1 3 b1 b2) b3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact skip_pc _ entry start back
      (entry_test_skip_pc s entry start forward pc forwardPC c bound sum noFlip) backPC
  · rw [noFlipResult,skip_x12,test_reg _ .x12 (by decide),entry_reg,sum]
  · rw [noFlipResult,skip_x13,test_reg _ .x12 (by decide),entry_reg,sum]
    rfl
  · intro a
    simp only [MachineState.getByte,noFlipResult,skip_mem,test_mem,entry_mem]
  · simp [noFlipResult,skipState,execInstrBr,
      MachineState.getReg_setReg_ne,test_reg _ .x10 (by decide),entry_reg]
  · rw [noFlipResult,skip_ra,test_reg _ .x1 (by decide),entry_reg]
  · rw [noFlipResult,skip_sp,test_reg _ .x2 (by decide),entry_reg]

end SigGolfCandidate.Hypertree.Signing
