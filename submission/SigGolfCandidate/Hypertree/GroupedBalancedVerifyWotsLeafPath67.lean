import SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsPathInputs67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastWotsFrameAll67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafPath67

/-! From the decoder return through WOTS recovery and the upper Merkle path. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsLeafPath67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyWotsReady67
open GroupedBalancedVerifyWotsReadyInput67
open GroupedBalancedVerifyWotsPathInputs67
open GroupedBalancedByteFastWotsFrameAll67
open GroupedBalancedByteFastEdgeIndexRefine67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem run_wots_leaf_path (hash : Hash) (s : MachineState)
    (base leaf start height : Nat)
    (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (siblings : Nat → Reference.Digest)
    (pc : s.pc = 0x1518)
    (baseWord : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (index : StoredIndex s (BitVec.ofNat 192 leaf))
    (startWord : s.getMem 0x81048 = BitVec.ofNat 64 start)
    (heightWord : s.getMem 0x81060 = BitVec.ofNat 64 height)
    (safe : GroupedBalancedByteFastChainReady67.SafeWitnesses start)
    (witnesses : GroupedBalancedByteFastChainReady67.WitnessWords
      s start values)
    (tables : GroupedBalancedVerifyByteContract67.Tables s)
    (digits : GroupedBalancedByteFastWotsFrame67.Digits s message)
    (siblingWords : ∀ j, j < height → ∀ half : Fin 2,
      s.getMem (BitVec.ofNat 64
        (start+16*67+16*j+8*half.val)) =
        (siblings j).extractLsb' (64*half.val) 64)
    (heightChoice : height = 3 ∨ height = 4)
    (aligned : start % 8 = 0)
    (wireBound : start + 16*67 + 16*height ≤ 0x38da0)
    (baseBound : base < 256)
    (leafBound : leaf < 2^192) :
    ∃ final steps cycles,
      Trace hash image s
        (4*GroupedBalancedChecksum67.suffixCost message + 1281 + steps)
        (11*GroupedBalancedChecksum67.suffixCost message + 1281 + cycles)
        (GroupedBalancedChecksum67.suffixCost message + 1 + height)
        (GroupedBalancedChecksum67.suffixCost message + 18 + height)
        final ∧
      final.pc = 0x19c4 ∧
      (∀ half : Fin 2,
        final.getMem (Signing.wordAddress 0x80500 half.val) =
          (GroupedBalancedByteFastUpperPathIter67.rootAt hash base leaf
            (GroupedBalancedUpperTree67.compressLeaf hash base leaf
              (GroupedBalancedByteFastEndpointAccum67.expectedEndpoint
                hash base leaf message values)) siblings height).extractLsb'
                  (64*half.val) 64) ∧
      final.getMem 0x81048 =
        BitVec.ofNat 64 (start+16*67+16*height) ∧
      final.getMem 0x81050 = BitVec.ofNat 64 height ∧
      final.getMem 0x81060 = BitVec.ofNat 64 height ∧
      final.getMem 0x81000 = BitVec.ofNat 64 (base+height) ∧
      StoredIndex final (BitVec.ofNat 192 (leaf/2^height)) ∧
      final.getMem 0x81058 = s.getMem 0x81058 ∧
      (∀ a : Word, a.toNat < 0x80000 →
        final.getMem a = s.getMem a) ∧
      (∀ a : Word, 0xfff700 ≤ a.toNat →
        final.getMem a = s.getMem a) ∧
      cycles ≤ 202+172*height := by
  have ready := ready_first s base leaf start message values pc baseWord
    index startWord safe witnesses tables digits
  obtain ⟨wots,wotsTrace,wotsDone,wotsFrame⟩ := all_addresses
    hash (readyState s) base leaf start message values safe baseBound ready
  obtain ⟨hbase,hindex,hlimit,hwitness⟩ := path_inputs
    s wots base leaf start height siblings baseWord index heightWord
      wireBound siblingWords wotsFrame
  obtain ⟨final,steps,cycles,path,finalPc,finalPtr,finalCount,
    finalLimit,finalLevel,finalIndex,root,
    pathGroup,pathLow,pathHigh,bound⟩ :=
    GroupedBalancedByteFastLeafPath67.leaf_path
      hash wots base leaf start height message values siblings wotsDone
      heightChoice aligned wireBound baseBound leafBound hbase hindex
      hlimit hwitness
  refine ⟨final,steps,cycles,?_,finalPc,root,
    finalPtr,finalCount,finalLimit,finalLevel,finalIndex,?_,?_,?_,bound⟩
  have firstTrace := OrdinarySteps.trace (hash := hash) (ready_steps s pc)
  have full := (firstTrace.trans wotsTrace).trans path
  convert full using 1 <;> omega
  · rw [pathGroup,wotsFrame 0x81058
      (Or.inr (Or.inl ⟨by decide,by decide⟩)),
      ready_mem,GroupedBalancedVerifyWotsHeaderFields67.header_mem_frame
        s 0x81058 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
  · intro a low
    rw [pathLow a low,wotsFrame a (Or.inl low),ready_mem,
      GroupedBalancedVerifyWotsHeaderFields67.header_low_frame s a
        (by omega)]
  · intro a high
    have disjoint (b : Word) (small : b.toNat < 0xfff700) : a ≠ b := by
      intro eq
      have h := congrArg BitVec.toNat eq
      omega
    rw [pathHigh a high,wotsFrame a (Or.inr (Or.inr high)),ready_mem,
      GroupedBalancedVerifyWotsHeaderFields67.header_mem_frame s a
        (disjoint 0x81030 (by decide))
        (disjoint 0x81038 (by decide))
        (disjoint 0x90000 (by decide))
        (disjoint 0x90008 (by decide))
        (disjoint 0x90010 (by decide))
        (disjoint 0x90018 (by decide))]

#print axioms run_wots_leaf_path
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsLeafPath67
