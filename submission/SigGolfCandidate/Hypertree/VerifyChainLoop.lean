import SigGolfCandidate.Hypertree.VerifyChainStep
import SigGolfCandidate.Hypertree.VerifyHoistLoop

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

/-- The in-place HASH loop recovers exactly the remaining verifier chain. -/
theorem chain_from_digit_fast (hash : Hash) (s : MachineState) (level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (digit : Fin 8)
    (value : Reference.Digest)
    (pc : s.pc = 0x1930) (levelBound : level < 256)
    (data : Hoist.LoopData s level tree side chain digit.val value) :
    ∃ final instructions cycles,
      Trace hash verify s instructions cycles (7-digit.val) (7-digit.val) final ∧
      instructions ≤ 4*(7-digit.val)+2 ∧ cycles ≤ 11*(7-digit.val)+2 ∧
      instructions ≤ cycles ∧
      final.pc = 0x1644 ∧
      Hoist.LoopData final level tree side chain 7
        (walk (Reference.chainHash hash level tree side chain)
          digit.val (7-digit.val) value) ∧
      Hoist.HeaderWordCarry final level tree (Reference.sideNumber side) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  have code : Hoist.LoopCode verify := by unfold Hoist.LoopCode Hoist.TickCode; decide
  obtain ⟨final, instructions, cycles, run, steps, cyclesBound, stepsCycles, endPC, finalData,
    carry, ra, sp, frame⟩ :=
    Hoist.run_fragment verify hash code s level tree digit.val (7-digit.val)
      side chain value pc (by have := digit.isLt; omega) levelBound data
  refine ⟨final, instructions, cycles, run, steps, cyclesBound, stepsCycles, endPC,
    finalData, carry, ra, sp, ?_⟩
  intro a outside
  apply frame a
  refine ⟨?_, ?_⟩
  · simpa [wordAddress] using outside.1 (0 : Fin 8)
  · intro i
    have h := outside.1 ⟨i.val+4, by have := i.isLt; omega⟩
    simpa [wordAddress, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h

end SigGolfCandidate.Hypertree.Verifying
