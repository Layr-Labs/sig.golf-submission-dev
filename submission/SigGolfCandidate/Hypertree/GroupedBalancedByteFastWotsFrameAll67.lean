import SigGolfCandidate.Hypertree.GroupedBalancedByteFastWotsStepFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastWotsFrameFold67

/-! The full 67-chain verifier loop preserves protected caller memory. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastWotsFrameAll67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedByteFastChainReady67
open GroupedBalancedByteFastChainEndpoints67
open GroupedBalancedByteFastChainFold67
open GroupedBalancedByteFastWotsProtected67
open GroupedBalancedByteFastSuffixLoop67

theorem all_addresses (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start) (baseBound : base < 256)
    (ready : Ready s base leaf start (0 : Fin 67) message values) :
    ∃ final,
      Trace hash image s
        (4 * GroupedBalancedChecksum67.suffixCost message + 1221)
        (11 * GroupedBalancedChecksum67.suffixCost message + 1221)
        (GroupedBalancedChecksum67.suffixCost message)
        (GroupedBalancedChecksum67.suffixCost message) final ∧
      StrongDone hash final base leaf start message values ∧
      (∀ a : Word, Protected a → final.getMem a = s.getMem a) :=
  GroupedBalancedByteFastWotsFrameFold67.all_addresses_of_step
    hash s base leaf start message values safe baseBound ready
      (fun a safeAddr i hi t inv =>
        GroupedBalancedByteFastWotsStepFrame67.strong_step_frame
          hash base leaf start message values safe baseBound
          i hi t inv a safeAddr)

#print axioms all_addresses
end SigGolfCandidate.Hypertree.GroupedBalancedByteFastWotsFrameAll67
