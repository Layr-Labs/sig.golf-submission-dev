import SigGolfCandidate.Hypertree.BalancedPatchControl
import SigGolfCandidate.Hypertree.BalancedPatchSetup
import SigGolfCandidate.Hypertree.BalancedPatchWords
import SigGolfCandidate.Hypertree.BalancedPatchTails
import SigGolfCandidate.Hypertree.BalancedPatchExit

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion

theorem pc_flip (s : MachineState) (forward : BitVec 21) (c : Nat)
    (bound : c ≤ 301) (sum : (entryState s forward).getReg .x12 = BitVec.ofNat 64 c)
    (flip : ¬c < 151) :
    (testState (entryState s forward)).pc = (entryState s forward).pc + 12 := by
  have hp := test_pc (entryState s forward) c bound sum
  rw [if_neg flip] at hp
  exact hp

theorem entry_test_flip_pc (s : MachineState) (entry start : Word)
    (forward : BitVec 21) (pc : s.pc = entry)
    (offset : entry + signExtend21 forward = start)
    (c : Nat) (bound : c ≤ 301)
    (sum : s.getReg .x12 = BitVec.ofNat 64 c)
    (flip : ¬ c < 151) :
    (testState (entryState s forward)).pc = start + 12 := by
  have input : (entryState s forward).getReg .x12 = BitVec.ofNat 64 c :=
    (entry_reg s forward .x12).trans sum
  exact (pc_flip s forward c bound input flip).trans
    (congrArg (· + 12) (entry_pc s entry start forward pc offset))
end SigGolfCandidate.Hypertree.Signing


namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion
set_option maxRecDepth 4096

def flipResult (s : MachineState) (forward back : BitVec 21) : MachineState :=
  finishState (tailPass (wordPass (setupState (testState (entryState s forward))))) back

theorem flip_block (image : Image) (entry start : Word) (forward back : BitVec 21)
    (code : PatchCode image entry start forward back)
    (s : MachineState) (pc : s.pc = entry)
    (forwardPC : entry + signExtend21 forward = start)
    (backPC : start+144+signExtend21 back = entry+4)
    (c : Nat) (bound : c ≤ 301) (sum : s.getReg .x12 = BitVec.ofNat 64 c)
    (flip : ¬c < 151) :
    OrdinarySteps image s 38 (flipResult s forward back) ∧
    (flipResult s forward back).pc = entry+4 ∧
    (flipResult s forward back).getReg .x12 = BitVec.ofNat 64 (301-c) := by
  have pc2 := entry_test_flip_pc s entry start forward pc forwardPC c bound sum flip
  have pc3 : (setupState (testState (entryState s forward))).pc = start+36 := by
    rw [setup_pc, pc2]; simp [BitVec.add_assoc]
  have pc4 : (wordPass (setupState (testState (entryState s forward)))).pc = start+96 := by
    rw [wordPass_pc, pc3]; simp [BitVec.add_assoc]
  have pc5 : (tailPass (wordPass (setupState (testState (entryState s forward))))).pc = start+132 := by
    rw [tailPass_pc, pc4]; simp [BitVec.add_assoc]
  have base3 : (setupState (testState (entryState s forward))).getReg .x15 = 0x80600 := setup_x15 _
  have base4 : (wordPass (setupState (testState (entryState s forward)))).getReg .x15 = 0x80600 :=
    (wordPass_regs _).1.trans base3
  have b1 := entry_block image entry start forward back code s pc
  have b2 := test_block image start
    (patch_test_code image entry start forward back code) (entryState s forward)
    (entry_pc s entry start forward pc forwardPC)
  have b3 := setup_block image entry start forward back code
    (testState (entryState s forward)) pc2
  have b4 := wordPass_block image entry start forward back code
    (setupState (testState (entryState s forward))) pc3 base3
  have b5 := tailPass_block image entry start forward back code
    (wordPass (setupState (testState (entryState s forward)))) pc4 base4
  have b6 := finish_block image entry start forward back code
    (tailPass (wordPass (setupState (testState (entryState s forward))))) pc5
  have sum5 : (tailPass (wordPass (setupState (testState (entryState s forward))))).getReg .x12 =
      BitVec.ofNat 64 c := by
    rw [(tailPass_regs _).2.2.1, (wordPass_regs _).2.2.1,
      setup_x12, test_reg _ .x12 (by decide), entry_reg, sum]
  refine ⟨?_, ?_, ?_⟩
  · exact Keygen.ordinary_trans image s _ _ 34 4
      (Keygen.ordinary_trans image s _ _ 25 9
        (Keygen.ordinary_trans image s _ _ 10 15
          (Keygen.ordinary_trans image s _ _ 4 6
            (Keygen.ordinary_trans image s _ _ 1 3 b1 b2) b3) b4) b5) b6
  · exact finish_pc _ entry start back pc5 backPC
  · exact finish_checksum _ back c bound sum5

#print axioms flip_block
end SigGolfCandidate.Hypertree.Signing
