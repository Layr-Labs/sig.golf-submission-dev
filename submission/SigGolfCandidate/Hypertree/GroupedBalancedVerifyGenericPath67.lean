import SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsLeafPath67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTableProtected67

/-! A decoder-to-root path for any group and either allowed tree height. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyGenericPath67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

def witnessDigest (s : MachineState) (start : Nat)
    (chain : Fin 67) : Reference.Digest :=
  s.getMem (BitVec.ofNat 64 (start+16*chain.val+8)) ++
  s.getMem (BitVec.ofNat 64 (start+16*chain.val))

def siblingDigest (s : MachineState) (start j : Nat) : Reference.Digest :=
  s.getMem (BitVec.ofNat 64 (start+16*67+16*j+8)) ++
  s.getMem (BitVec.ofNat 64 (start+16*67+16*j))

theorem witness_words (s : MachineState) (start : Nat) :
    GroupedBalancedByteFastChainReady67.WitnessWords
      s start (witnessDigest s start) := by
  intro chain half
  fin_cases half
  · change s.getMem (BitVec.ofNat 64 (start+16*chain.val)) =
      (witnessDigest s start chain).extractLsb' 0 64
    exact BitVec.extractLsb'_append_eq_right.symm
  · change s.getMem (BitVec.ofNat 64 (start+16*chain.val+8)) =
      (witnessDigest s start chain).extractLsb' 64 64
    exact BitVec.extractLsb'_append_eq_left.symm

theorem sibling_words (s : MachineState) (start height : Nat) :
    ∀ j, j < height → ∀ half : Fin 2,
      s.getMem (BitVec.ofNat 64 (start+16*67+16*j+8*half.val)) =
        (siblingDigest s start j).extractLsb' (64*half.val) 64 := by
  intro j _ half
  fin_cases half
  · change s.getMem (BitVec.ofNat 64 (start+16*67+16*j)) =
      (siblingDigest s start j).extractLsb' 0 64
    exact BitVec.extractLsb'_append_eq_right.symm
  · change s.getMem (BitVec.ofNat 64 (start+16*67+16*j+8)) =
      (siblingDigest s start j).extractLsb' 64 64
    exact BitVec.extractLsb'_append_eq_left.symm

theorem safe_witnesses (start height : Nat)
    (aligned : start % 8 = 0)
    (wireBound : start + 16*67 + 16*height ≤ 0x38da0) :
    GroupedBalancedByteFastChainReady67.SafeWitnesses start := by
  intro chain half
  have small : start+16*chain.val+8*half.val < 2^64 := by
    have hc := chain.isLt
    have hh := half.isLt
    omega
  have nat :
      (GroupedBalancedByteFastChainReady67.witnessAddress
        start chain half).toNat = start+16*chain.val+8*half.val := by
    change (start+16*chain.val+8*half.val) % 2^64 = _
    exact Nat.mod_eq_of_lt small
  constructor
  · unfold accessValid rangeValid
    rw [nat]
    have align : (start+16*chain.val+8*half.val)%8 = 0 := by omega
    simp [align,MEMORY_BYTES]
    have hc := chain.isLt
    have hh := half.isLt
    omega
  · rw [nat]
    have hc := chain.isLt
    have hh := half.isLt
    omega

theorem path_from_decoder (hash : Hash) (s : MachineState)
    (base leaf start height : Nat) (message : Reference.Digest)
    (pc : s.pc = 0x1518)
    (baseWord : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (index : GroupedBalancedByteFastEdgeIndexRefine67.StoredIndex s
      (BitVec.ofNat 192 leaf))
    (startWord : s.getMem 0x81048 = BitVec.ofNat 64 start)
    (heightWord : s.getMem 0x81060 = BitVec.ofNat 64 height)
    (tables : GroupedBalancedVerifyByteContract67.Tables s)
    (digits : GroupedBalancedByteFastWotsFrame67.Digits s message)
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
        (GroupedBalancedChecksum67.suffixCost message + 18 + height) final ∧
      final.pc = 0x19c4 ∧
      (∀ half : Fin 2,
        final.getMem (Signing.wordAddress 0x80500 half.val) =
          (GroupedBalancedByteFastUpperPathIter67.rootAt hash base leaf
            (GroupedBalancedUpperTree67.compressLeaf hash base leaf
              (GroupedBalancedByteFastEndpointAccum67.expectedEndpoint hash
                base leaf message (witnessDigest s start)))
            (siblingDigest s start) height).extractLsb'
              (64*half.val) 64) ∧
      final.getMem 0x81048 =
        BitVec.ofNat 64 (start+16*67+16*height) ∧
      final.getMem 0x81050 = BitVec.ofNat 64 height ∧
      final.getMem 0x81060 = BitVec.ofNat 64 height ∧
      final.getMem 0x81000 = BitVec.ofNat 64 (base+height) ∧
      GroupedBalancedByteFastEdgeIndexRefine67.StoredIndex final
        (BitVec.ofNat 192 (leaf/2^height)) ∧
      final.getMem 0x81058 = s.getMem 0x81058 ∧
      (∀ a : Word, a.toNat < 0x80000 → final.getMem a = s.getMem a) ∧
      GroupedBalancedVerifyByteContract67.Tables final ∧
      cycles ≤ 202+172*height := by
  obtain ⟨final,steps,cycles,run,endPC,root,ptr,count,hlim,
    b,idx,group,low,tableFrame,bound⟩ :=
    GroupedBalancedVerifyWotsLeafPath67.run_wots_leaf_path hash s
      base leaf start height message (witnessDigest s start)
      (siblingDigest s start) pc baseWord index startWord heightWord
      (safe_witnesses start height aligned wireBound)
      (witness_words s start) tables digits (sibling_words s start height)
      heightChoice aligned wireBound baseBound leafBound
  exact ⟨final,steps,cycles,run,endPC,root,ptr,count,hlim,b,idx,
    group,low,
    GroupedBalancedVerifyTableProtected67.tables_of_table_frame tableFrame
      tables,bound⟩

#print axioms path_from_decoder
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyGenericPath67
