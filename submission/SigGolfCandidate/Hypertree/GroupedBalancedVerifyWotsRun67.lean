import SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsReadyInput67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainEndpoints67

/-! The decoder return executes all 67 concrete WOTS chains. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsRun67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyWotsReady67
open GroupedBalancedVerifyWotsReadyInput67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem run_wots (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (pc : s.pc = 0x1518)
    (baseWord : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (index : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (startWord : s.getMem 0x81048 = BitVec.ofNat 64 start)
    (safe : GroupedBalancedByteFastChainReady67.SafeWitnesses start)
    (witnesses : GroupedBalancedByteFastChainReady67.WitnessWords
      s start values)
    (tables : GroupedBalancedVerifyByteContract67.Tables s)
    (digits : GroupedBalancedByteFastWotsFrame67.Digits s message)
    (baseBound : base < 256) :
    ∃ final,
      Trace hash image s
        (4 * GroupedBalancedChecksum67.suffixCost message + 1281)
        (11 * GroupedBalancedChecksum67.suffixCost message + 1281)
        (GroupedBalancedChecksum67.suffixCost message)
        (GroupedBalancedChecksum67.suffixCost message) final ∧
      GroupedBalancedByteFastChainEndpoints67.StrongDone hash final
        base leaf start message values := by
  have ready := ready_first s base leaf start message values pc baseWord
    index startWord safe witnesses tables digits
  obtain ⟨final,trace,done⟩ :=
    GroupedBalancedByteFastChainEndpoints67.all_wots_endpoints
      hash (readyState s) base leaf start message values
      safe baseBound ready
  refine ⟨final,?_,done⟩
  have firstTrace := OrdinarySteps.trace (hash := hash) (ready_steps s pc)
  convert firstTrace.trans trace using 1 <;> omega

#print axioms run_wots
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsRun67
