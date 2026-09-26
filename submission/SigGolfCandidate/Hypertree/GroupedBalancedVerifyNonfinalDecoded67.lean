import SigGolfCandidate.Hypertree.GroupedBalancedVerifyGenericPath67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyEndGroupDispatch67

/-! A decoded nonfinal verifier group returns to the next decoder call. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyNonfinalDecoded67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem next_group (hash : Hash) (s : MachineState)
    (g base leaf start height : Nat) (message : Reference.Digest)
    (pc : s.pc = 0x1518)
    (group : s.getMem 0x81058 = BitVec.ofNat 64 g)
    (groupBound : g < 44)
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
    ∃ next steps cycles tailSteps,
      tailSteps ≤ 15 ∧
      Trace hash image s
        (4*GroupedBalancedChecksum67.suffixCost message + 1281 +
          steps + tailSteps)
        (11*GroupedBalancedChecksum67.suffixCost message + 1281 +
          cycles + tailSteps)
        (GroupedBalancedChecksum67.suffixCost message + 1 + height)
        (GroupedBalancedChecksum67.suffixCost message + 18 + height) next ∧
      next.pc = 0x1514 ∧
      (∀ half : Fin 2,
        next.getMem (Signing.wordAddress 0x80500 half.val) =
          (GroupedBalancedByteFastUpperPathIter67.rootAt hash base leaf
            (GroupedBalancedUpperTree67.compressLeaf hash base leaf
              (GroupedBalancedByteFastEndpointAccum67.expectedEndpoint hash
                base leaf message
                (GroupedBalancedVerifyGenericPath67.witnessDigest s start)))
            (GroupedBalancedVerifyGenericPath67.siblingDigest s start)
            height).extractLsb' (64*half.val) 64) ∧
      next.getMem 0x81048 =
        BitVec.ofNat 64 (start+16*67+16*height) ∧
      next.getMem 0x81058 = BitVec.ofNat 64 (g+1) ∧
      next.getMem 0x81060 =
        (if g = 29 then 4 else BitVec.ofNat 64 height) ∧
      next.getMem 0x81000 = BitVec.ofNat 64 (base+height) ∧
      GroupedBalancedByteFastEdgeIndexRefine67.StoredIndex next
        (BitVec.ofNat 192 (leaf/2^height)) ∧
      (∀ a : Word, a.toNat < 0x80000 → next.getMem a = s.getMem a) ∧
      GroupedBalancedVerifyByteContract67.Tables next ∧
      cycles ≤ 202+172*height := by
  obtain ⟨rootState,steps,cycles,path,rootPc,root,ptr,_,hlim,
    b,idx,groupCarry,low,tableCarry,bound⟩ :=
    GroupedBalancedVerifyGenericPath67.path_from_decoder hash s
      base leaf start height message pc baseWord index startWord heightWord
      tables digits heightChoice aligned wireBound baseBound leafBound
  obtain ⟨next,tailSteps,tailBound,tail,nextPc,nextGroup,nextHeight,
    tailLow,tailMem⟩ :=
    GroupedBalancedVerifyEndGroupDispatch67.dispatch rootState g rootPc
      (groupCarry.trans group) (by omega)
  have separate (a b : Word) (high : b.toNat < 0xfff700)
      (ha : 0xfff700 ≤ a.toNat) : a ≠ b := by
    intro eq
    have h := congrArg BitVec.toNat eq
    omega
  have carry (a : Word) (h58 : a ≠ 0x81058) (h60 : a ≠ 0x81060) :
      next.getMem a = rootState.getMem a := tailMem a h58 h60
  have heightNext : next.getMem 0x81060 =
      (if g = 29 then 4 else BitVec.ofNat 64 height) := by
    rw [nextHeight,hlim]
  refine ⟨next,steps,cycles,tailSteps,tailBound,?_,?_,?_,?_,
    nextGroup,heightNext,?_,?_,?_,?_,bound⟩
  · have all := path.trans (OrdinarySteps.trace (hash := hash) tail)
    convert all using 1 <;> omega
  · simpa [show g ≠ 44 by omega] using nextPc
  · intro half
    rw [carry _ (by fin_cases half <;> decide)
      (by fin_cases half <;> decide)]
    exact root half
  · rw [carry 0x81048 (by decide) (by decide)]
    exact ptr
  · rw [carry 0x81000 (by decide) (by decide)]
    exact b
  · intro i
    rw [carry _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)]
    exact idx i
  · intro a ha
    rw [tailLow a ha,low a ha]
  · apply GroupedBalancedVerifyTableProtected67.tables_of_table_frame
      (s := rootState) (t := next) ?_ tableCarry
    intro a ha
    exact carry a (separate a 0x81058 (by decide) ha)
      (separate a 0x81060 (by decide) ha)

#print axioms next_group
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyNonfinalDecoded67
