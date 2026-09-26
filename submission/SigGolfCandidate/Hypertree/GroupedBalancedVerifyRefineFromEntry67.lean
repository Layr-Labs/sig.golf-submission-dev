import SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedWire67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyCallBridge67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyFinalGroup67
import SigGolfCandidate.Hypertree.GroupedBalancedSecurityCheckConditional67

/-! The upper verifier trace refines the oracle verifier once its loaded
bottom root and shifted index have been identified. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyRefineFromEntry67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.SecurityVerifyCost
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev program := GroupedBalancedProgram67ByteSign.submission

theorem post_root (s : MachineState) :
    GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot
      (GroupedBalancedVerifyTreePost67.postState s) =
    GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot s := by
  simp only [GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot]
  rw [GroupedBalancedVerifyTreePost67.post_mem s 0x80508 (by decide)
      (by decide),
    GroupedBalancedVerifyTreePost67.post_mem s 0x80500 (by decide)
      (by decide)]

theorem post_index (s : MachineState) :
    GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex
      (GroupedBalancedVerifyTreePost67.postState s) =
    GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex s := by
  simp only [GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex]
  rw [GroupedBalancedVerifyTreePost67.post_mem s 0x81018 (by decide)
      (by decide),
    GroupedBalancedVerifyTreePost67.post_mem s 0x81010 (by decide)
      (by decide),
    GroupedBalancedVerifyTreePost67.post_mem s 0x81008 (by decide)
      (by decide)]

theorem one (hash : Hash) (pk : PublicKey) (message : Message)
    (wire : Bytes 50848) (initial entry : MachineState)
    (loaded : initialState program .verify (message,pk,wire) = some initial)
    (frame : ∀ a : Word, a.toNat < 0x80000 →
      entry.getMem a = initial.getMem a)
    (value : (program.runWith hash .verify (message,pk,wire)).value.isSome =
      decide (GroupedBalancedVerifyGroupFold67.rootAt hash entry
        (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat
        45 = GroupedBalancedVerifyFinalGroup67.publicKeyDigest initial))
    (callCount : (program.runWith hash .verify (message,pk,wire)).hashCalls =
      12+GroupedBalancedVerifyGroupFold67.callsAt hash entry
        (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat
        45)
    (indexEq :
      (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat =
        GroupedMixedIndex.bottomTree
          (Reference.indexOf hash message
            (GroupedBalancedWire67.decode wire).randomizer))
    (rootEq : GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot entry =
      GroupedBottomTree.recover hash 10
        (GroupedMixedIndex.bottomTree
          (Reference.indexOf hash message
            (GroupedBalancedWire67.decode wire).randomizer))
        (Reference.indexOf hash message
          (GroupedBalancedWire67.decode wire).randomizer).toNat
        (GroupedBalancedWire67.decode wire).bottom) :
    (program.runWith hash .verify (message,pk,wire)).value.isSome =
        evalWithAnswerFn hash
          (GroupedBalancedSecurityCheckConditional67.program pk message wire) ∧
      (program.runWith hash .verify (message,pk,wire)).hashCalls =
        calls hash
          (GroupedBalancedSecurityCheckConditional67.program pk message wire) := by
  let signature := GroupedBalancedWire67.decode wire
  let index := Reference.indexOf hash message signature.randomizer
  let bottomTree := GroupedMixedIndex.bottomTree index
  let bottom := GroupedBottomTree.recover hash 10 bottomTree index.toNat
    signature.bottom
  let root := GroupedBalancedScheme67.recoverLayers hash
    GroupedBalancedScheme67.Heights 10 bottomTree bottom signature.upper
  have pkEq : GroupedBalancedVerifyFinalGroup67.publicKeyDigest initial =
      pk := by
    simpa only [GroupedBalancedVerifyFinalGroup67.publicKeyDigest] using
      GroupedBalancedVerifyLoadedWire67.initial_pk_digest
        message pk wire initial loaded
  have rootMachine : GroupedBalancedVerifyGroupFold67.rootAt hash entry
      (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat
      45 = root := by
    rw [indexEq]
    have bridge := GroupedBalancedVerifyLoadedWire67.root45_eq_recoverLayers
      hash message pk wire initial entry loaded frame bottomTree
    rw [rootEq] at bridge
    simpa only [root,bottom,signature,index,bottomTree,
      GroupedBalancedWire67.decode] using bridge
  have callsMachine : GroupedBalancedVerifyGroupFold67.callsAt hash entry
      (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat
      45 =
      GroupedBalancedVerifyCallBridge67.layersCalls hash
        GroupedBalancedScheme67.Heights 10 bottomTree bottom
        signature.upper := by
    rw [indexEq]
    have bridge := GroupedBalancedVerifyCallBridge67.callsAt45_eq_layersCalls
      hash message pk wire initial entry loaded frame bottomTree
    rw [rootEq] at bridge
    simpa only [bottom,signature,index,bottomTree,
      GroupedBalancedWire67.decode] using bridge
  have evalEq : evalWithAnswerFn hash
      (GroupedBalancedSecurityCheckConditional67.program pk message wire) =
      decide (root = pk) := by
    simp only [GroupedBalancedSecurityCheckConditional67.program,
      GroupedBalancedVerifyOracle67.verify,evalWithAnswerFn_bind,
      SecurityReference.eval_ask,
      GroupedBalancedVerifyOracle67.eval_recoverBottom,
      GroupedBalancedVerifyOracle67.eval_recoverLayers,
      evalWithAnswerFn_pure,Reference.indexOf]
    rfl
  have callsEq : calls hash
      (GroupedBalancedSecurityCheckConditional67.program pk message wire) =
      12+GroupedBalancedVerifyCallBridge67.layersCalls hash
        GroupedBalancedScheme67.Heights 10 bottomTree bottom
        signature.upper := by
    simpa only [GroupedBalancedSecurityCheckConditional67.program,
      signature,index,bottomTree,bottom] using
      GroupedBalancedVerifyCallBridge67.calls_verify hash pk message signature
  constructor
  · rw [value,rootMachine,pkEq,← evalEq]
  · rw [callCount,callsMachine,callsEq]

#print axioms one
#print axioms post_root
#print axioms post_index
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyRefineFromEntry67
