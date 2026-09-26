import SigGolfCandidate.Hypertree.GroupedBalancedVerifyImage67Fast2Byte
import SigGolfCandidate.Hypertree.SignFinish

/-! The prototype verifier's final root/public-key comparison. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyFooter67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem footer_code : Signing.FooterCode image 0x1a04 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem footer_executes (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1a04) :
    ∃ (steps : Nat) (final : MachineState), steps ≤ 15 ∧
      Executes hash image s steps
        ⟨if Signing.RootMatches s then .success else .failure,
          final, steps, 0, 0⟩ ∧
      ∀ a, final.getMem a = s.getMem a :=
  Signing.footer_executes hash image 0x1a04 footer_code s pc

#print axioms footer_code
#print axioms footer_executes
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyFooter67
