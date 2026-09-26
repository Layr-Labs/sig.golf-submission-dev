import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4Payload67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4RoundUnique67

/-! A verifier H4 round computes the addressed parent of the current root
and selected sibling, with the same state used by the index/control proof. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4FunctionalRound67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyH4IndexHeader67
open GroupedBalancedVerifyH4IndexFrame67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem round_trace_root (hash : Hash) (s : MachineState) (p c : Word)
    (index : BitVec 192) (level : Nat)
    (root sibling : Reference.Digest)
    (pc : s.pc = 0x1290)
    (pointer : s.getMem 0x81048 = p)
    (count : s.getMem 0x81050 = c)
    (pSmall : p.toNat < 0x80000)
    (p8Small : (p+8).toNat < 0x80000)
    (valid0 : accessValid p 8 = true)
    (valid8 : accessValid (p+8) 8 = true)
    (stored : StoredIndex s index)
    (levelWord : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (rootWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80500 i.val) =
        root.extractLsb' (64*i.val) 64)
    (siblingWords : ∀ i : Fin 2,
      s.getMem (p + BitVec.ofNat 64 (8*i.val)) =
        sibling.extractLsb' (64*i.val) 64) :
    ∃ n final, (n = 162 ∨ n = 163) ∧
      Trace hash image s n (n+7) 1 1 final ∧
      final.pc = (if c+1 ≠ (10 : Word) then 0x1290 else 0x14f4) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80500 i.val) =
          (Reference.node hash level (index >>> 1).toNat
            (if s.getMem 0x81008#64 &&& 1#64 = 0#64 then root else sibling)
            (if s.getMem 0x81008#64 &&& 1#64 = 0#64 then sibling else root)
          ).extractLsb' (64*i.val) 64) := by
  obtain ⟨n,copied,nCases,prefixRun,copiedPC,leftWords,rightWords,
    copiedBase,copiedIndex,copiedPointer,copiedCount,_,_⟩ :=
    GroupedBalancedVerifyH4Payload67.header_payload s p pc pointer
      pSmall p8Small valid0 valid8 root sibling rootWords siblingWords
  have shifted : StoredIndex copied (index >>> 1) :=
    stored_of_frame copiedIndex (header_refines s index stored)
  have addressWords : ∀ i : Fin 3,
      copied.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 (index >>> 1).toNat).extractLsb' (64*i.val) 64 := by
    intro i
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using shifted i
  have copiedLevel : copied.getMem 0x81000 = BitVec.ofNat 64 level :=
    copiedBase.trans levelWord
  let left := if s.getMem 0x81008#64 &&& 1#64 = 0#64 then root else sibling
  let right := if s.getMem 0x81008#64 &&& 1#64 = 0#64 then sibling else root
  let ready := GroupedBalancedVerifyTreeH4Header67.headerState copied
  have headerRun := GroupedBalancedVerifyTreeH4Header67.header_block copied copiedPC
  have fields := GroupedBalancedVerifyTreeH4Query67.header_fields copied copiedPC
  let answered := writeHash ready (hash (hashInput ready))
  have hashRun := GroupedBalancedVerifyTreeH4Query67.hash_trace hash ready fields
  have hashPC := GroupedBalancedVerifyTreeH4Query67.hash_pc hash ready fields
  obtain ⟨storedAnswer,answerRun,answerPC,answerRoot⟩ :=
    GroupedBalancedVerifyH4NodeQuery67.node_copy hash copied copiedPC
      level (index >>> 1).toNat left right copiedLevel addressWords
      leftWords rightWords
  obtain ⟨sameAnswer,sameRun,_,_,samePointer,sameCount,_⟩ :=
    GroupedBalancedVerifyTreeH4Answer67.answer_copy answered hashPC
  have same : storedAnswer = sameAnswer :=
    Keygen.ordinary_deterministic answerRun sameRun
  have answerPointer : storedAnswer.getMem 0x81048 = answered.getMem 0x81048 := by
    rw [same]
    exact samePointer
  have answerCount : storedAnswer.getMem 0x81050 = answered.getMem 0x81050 := by
    rw [same]
    exact sameCount
  have storedCount : storedAnswer.getMem 0x81050 = c := by
    exact answerCount.trans
      ((GroupedBalancedVerifyTreeH4Query67.hash_count hash ready fields).trans
        ((GroupedBalancedVerifyTreeH4Header67.header_count copied).trans
          (copiedCount.trans count)))
  let final := GroupedBalancedVerifyTreeH4Tail67.updateState storedAnswer
  have tailRun := GroupedBalancedVerifyTreeH4Tail67.update_block storedAnswer answerPC
  refine ⟨n+74,final,?_,?_,?_,?_⟩
  · rcases nCases with h | h <;> simp [h]
  · have t0 : Trace hash image s (n+33) (n+33) 0 0 ready :=
      prefixRun.trace.trans headerRun.trace
    have t1 := t0.trans hashRun
    have t2 := t1.trans answerRun.trace
    have all := t2.trans tailRun.trace
    simpa [image,final,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all
  · change (GroupedBalancedVerifyTreeH4Tail67.updateState storedAnswer).pc = _
    rw [GroupedBalancedVerifyTreeH4Tail67.update_pc_count
      storedAnswer answerPC,storedCount]
  · intro i
    have unchanged := GroupedBalancedVerifyTreeH4Tail67.update_mem
      storedAnswer (Signing.wordAddress 0x80500 i.val)
      (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)
    exact unchanged.trans (answerRoot i)

theorem round_root (hash : Hash) (s : MachineState) (p c : Word)
    (index : BitVec 192) (level : Nat)
    (root sibling : Reference.Digest)
    (pc : s.pc = 0x1290)
    (pointer : s.getMem 0x81048 = p)
    (count : s.getMem 0x81050 = c)
    (pSmall : p.toNat < 0x80000)
    (p8Small : (p+8).toNat < 0x80000)
    (valid0 : accessValid p 8 = true)
    (valid8 : accessValid (p+8) 8 = true)
    (stored : StoredIndex s index)
    (levelWord : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (rootWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80500 i.val) =
        root.extractLsb' (64*i.val) 64)
    (siblingWords : ∀ i : Fin 2,
      s.getMem (p + BitVec.ofNat 64 (8*i.val)) =
        sibling.extractLsb' (64*i.val) 64) :
    ∃ n final, (n = 162 ∨ n = 163) ∧
      Trace hash image s n (n+7) 1 1 final ∧
      final.getMem 0x81048 = p+16 ∧
      final.getMem 0x81050 = c+1 ∧
      final.pc = (if c+1 ≠ (10 : Word) then 0x1290 else 0x14f4) ∧
      GroupedBalancedVerifyTreeHighFrame67.SafeFrame s final ∧
      StoredIndex final (index >>> 1) ∧
      final.getMem 0x81000 = s.getMem 0x81000 + 1 ∧
      GroupedBalancedVerifyStackGlobal67.LowFrame s final ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80500 i.val) =
          (Reference.node hash level (index >>> 1).toNat
            (if s.getMem 0x81008#64 &&& 1#64 = 0#64 then root else sibling)
            (if s.getMem 0x81008#64 &&& 1#64 = 0#64 then sibling else root)
          ).extractLsb' (64*i.val) 64) := by
  obtain ⟨n,actual,nCases,actualRun,actualPC,actualRoot⟩ :=
    round_trace_root hash s p c index level root sibling pc pointer count
      pSmall p8Small valid0 valid8 stored levelWord rootWords siblingWords
  obtain ⟨m,control,mCases,controlRun,controlPointer,controlCount,
    controlPC,controlSafe,controlIndex,controlBase,controlLow⟩ :=
    GroupedBalancedVerifyH4IndexRound67.round_index hash s p c index
      pc pointer count valid0 valid8 stored
  have equal := GroupedBalancedVerifyH4RoundUnique67.round_unique hash s
    actual control c n m (n+7) (m+7) 1 1 1 1
    nCases mCases actualRun controlRun actualPC controlPC
  rcases equal with ⟨_,stateEq⟩
  subst control
  exact ⟨n,actual,nCases,actualRun,controlPointer,controlCount,
    actualPC,controlSafe,controlIndex,controlBase,controlLow,actualRoot⟩

#print axioms round_trace_root
#print axioms round_root
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4FunctionalRound67
