import SigGolfCandidate.Hypertree.BalancedPatchControl
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
