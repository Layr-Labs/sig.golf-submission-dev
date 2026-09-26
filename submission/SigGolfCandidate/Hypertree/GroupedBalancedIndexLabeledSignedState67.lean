import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAudit67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledSignedWitness67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledCompilerAgree67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledDrawFaithful67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledSignedState67. -/
section
/-! Each retained H5 draw agrees with the audit's final cache value. The
compiler only draws on cache misses, so later draws cannot overwrite it. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledDrawFaithful67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedIndexLabeledAudit67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

def DrawFaithful (audit : Audit) : Prop :=
  ∀ input mark index,
    (input, (mark, index)) ∈ audit.draws →
      ∃ answer : BitVec 256,
        audit.h5cache input = some answer ∧
          index = answer.extractLsb' 0 160

theorem empty : DrawFaithful {} := by
  intro input mark index member
  cases member

theorem publicStep (audit : Audit) (pair : Message × Bytes 32)
    (faithful : DrawFaithful audit) :
    DrawFaithful (GroupedBalancedIndexLabeledAudit67.publicStep audit pair) := by
  by_cases signed : pair.1 ∈ audit.signedMessages <;>
    simpa [DrawFaithful, GroupedBalancedIndexLabeledAudit67.publicStep,
      signed] using faithful

theorem signStep (audit : Audit) (pair : Message × Bytes 32)
    (faithful : DrawFaithful audit) :
    DrawFaithful (GroupedBalancedIndexLabeledAudit67.signStep audit pair) := by
  simpa [DrawFaithful, GroupedBalancedIndexLabeledAudit67.signStep]
    using faithful

theorem drawStep (audit : Audit) (input : Query)
    (mark : Bool) (answer : BitVec 256)
    (faithful : DrawFaithful audit)
    (miss : audit.h5cache input = none) :
    DrawFaithful
      { audit with
        h5cache := audit.h5cache.cacheQuery input answer
        draws := audit.draws ++
          [(input, (mark, answer.extractLsb' 0 160))] } := by
  intro query flag index member
  have split :
      (query, (flag, index)) ∈ audit.draws ∨
        (query, (flag, index)) =
          (input, (mark, answer.extractLsb' 0 160)) := by
    simpa only [List.mem_append, List.mem_singleton] using member
  rcases split with old | new
  · obtain ⟨oldAnswer, oldCached, oldIndex⟩ := faithful query flag index old
    have distinct : query ≠ input := by
      intro same
      rw [same, miss] at oldCached
      cases oldCached
    exact ⟨oldAnswer,
      by simpa only [QueryCache.cacheQuery_of_ne _ _ distinct] using oldCached,
      oldIndex⟩
  · cases new
    exact ⟨answer, QueryCache.cacheQuery_self _ _ _, rfl⟩

theorem marked_answer (audit : Audit) (faithful : DrawFaithful audit)
    (input : Query) (index : BitVec 160)
    (member : (input, (true, index)) ∈ audit.draws) :
    ∃ answer : BitVec 256,
      audit.h5cache input = some answer ∧
        index = answer.extractLsb' 0 160 :=
  faithful input true index member

#print axioms drawStep
#print axioms marked_answer

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledDrawFaithful67

end

/-! Local invariant for first-signer evidence: cache agreement, nonce coverage,
the compiler's signed set, and the audit's first-pair witness. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledSignedState67
open SigGolf OracleComp OracleSpec Reference SecurityRandomOracle
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledCacheAgree67
open GroupedBalancedIndexLabeledNonceCovered67
open GroupedBalancedIndexLabeledSignedWitness67
open GroupedBalancedIndexLabeledDrawFaithful67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false
open scoped Classical

structure Sound (state : State) (signedMessages : Finset Message)
    (audit : Audit) : Prop where
  agree : H5Agree state.residual audit.h5cache
  nonceCovered : NonceCovered audit
  signedEq : signedMessages = audit.signedMessages
  witness : SignedWitness audit
  faithful : DrawFaithful audit

theorem empty (state : State)
    (residual : state.residual = ∅) : Sound state ∅ {} := by
  constructor
  · rw [residual]
    exact GroupedBalancedIndexLabeledCacheAgree67.empty
  · exact GroupedBalancedIndexLabeledNonceCovered67.empty
  · rfl
  · exact GroupedBalancedIndexLabeledSignedWitness67.empty
  · exact GroupedBalancedIndexLabeledDrawFaithful67.empty

theorem signedBottom (state : State) (signedMessages : Finset Message)
    (audit : Audit) (sound : Sound state signedMessages audit)
    (index : BitVec 160) (answer : BitVec 256) :
    Sound (signed state index answer) signedMessages audit := by
  exact ⟨sound.agree, sound.nonceCovered, sound.signedEq,
    sound.witness, sound.faithful⟩

theorem privateCached (state : State) (signedMessages : Finset Message)
    (audit : Audit) (sound : Sound state signedMessages audit)
    (input : Query) (pair : Message × Bytes 32)
    (parsed : SecurityIndexQuery.parse input = some pair)
    (answer : BitVec 256) (cached : state.residual input = some answer) :
    Sound state (insert pair.1 signedMessages)
      (GroupedBalancedIndexLabeledAudit67.signStep audit pair) := by
  have inputEq : indexInput pair.1 pair.2 = input :=
    (SecurityIndexQuery.parse_some_iff input pair).1 parsed
  have ghost : audit.h5cache (indexInput pair.1 pair.2) ≠ none := by
    rw [← sound.agree pair.1 pair.2, inputEq, cached]
    exact Option.some_ne_none _
  have witnessed : SignedWitness
      (GroupedBalancedIndexLabeledAudit67.signStep audit pair) := by
    by_cases known : pair.1 ∈ audit.signedMessages
    · exact GroupedBalancedIndexLabeledSignedWitness67.signStep_repeat
        audit pair sound.witness known
    · have guess := GroupedBalancedIndexLabeledNonceCovered67.firstSignHit
        audit sound.nonceCovered pair.1 pair.2 known ghost
      exact GroupedBalancedIndexLabeledSignedWitness67.signStep
        audit pair sound.witness (Or.inl guess)
  constructor
  · simpa only [GroupedBalancedIndexLabeledAudit67.signStep]
      using sound.agree
  · exact GroupedBalancedIndexLabeledNonceCovered67.signStep
      audit pair sound.nonceCovered
  · simpa only [GroupedBalancedIndexLabeledAudit67.signStep,
      sound.signedEq]
  · exact witnessed
  · exact GroupedBalancedIndexLabeledDrawFaithful67.signStep
      audit pair sound.faithful

theorem privateFresh (state : State) (signedMessages : Finset Message)
    (audit : Audit) (sound : Sound state signedMessages audit)
    (input : Query) (pair : Message × Bytes 32)
    (parsed : SecurityIndexQuery.parse input = some pair)
    (answer : BitVec 256)
    (miss : state.residual input = none) :
    Sound
      { state with residual := state.residual.cacheQuery input answer }
      (insert pair.1 signedMessages)
      (GroupedBalancedIndexLabeledAudit67.signStep
        { audit with
          h5cache := audit.h5cache.cacheQuery input answer
          draws := audit.draws ++
            [(input, (decide (pair.1 ∉ signedMessages),
              answer.extractLsb' 0 160))] }
        pair) := by
  have inputEq : indexInput pair.1 pair.2 = input :=
    (SecurityIndexQuery.parse_some_iff input pair).1 parsed
  subst input
  let updated : Audit :=
    { audit with
      h5cache := audit.h5cache.cacheQuery
        (indexInput pair.1 pair.2) answer
      draws := audit.draws ++
        [(indexInput pair.1 pair.2,
          (decide (pair.1 ∉ signedMessages),
          answer.extractLsb' 0 160))] }
  have coveredUpdated : NonceCovered
      (GroupedBalancedIndexLabeledAudit67.signStep updated pair) := by
    simpa only [updated, NonceCovered,
      GroupedBalancedIndexLabeledAudit67.signStep] using
      (GroupedBalancedIndexLabeledNonceCovered67.signFill
        audit pair answer sound.nonceCovered)
  have witnessUpdated : SignedWitness updated :=
    GroupedBalancedIndexLabeledSignedWitness67.drawStep
      audit (indexInput pair.1 pair.2)
        (decide (pair.1 ∉ signedMessages)) answer sound.witness
  have witnessed : SignedWitness
      (GroupedBalancedIndexLabeledAudit67.signStep updated pair) := by
    by_cases known : pair.1 ∈ audit.signedMessages
    · exact GroupedBalancedIndexLabeledSignedWitness67.signStep_repeat
        updated pair witnessUpdated (by simpa only [updated] using known)
    · have unsigned : pair.1 ∉ signedMessages := by
        simpa only [sound.signedEq] using known
      have marked :
          (indexInput pair.1 pair.2,
            (true, answer.extractLsb' 0 160)) ∈ updated.draws := by
        simp [updated, unsigned]
      exact GroupedBalancedIndexLabeledSignedWitness67.signStep
        updated pair witnessUpdated
        (Or.inr ⟨answer.extractLsb' 0 160, marked⟩)
  have ghostMiss : audit.h5cache
      (indexInput pair.1 pair.2) = none := by
    rw [← sound.agree pair.1 pair.2]
    exact miss
  have faithfulUpdated : DrawFaithful updated :=
    GroupedBalancedIndexLabeledDrawFaithful67.drawStep audit
      (indexInput pair.1 pair.2)
      (decide (pair.1 ∉ signedMessages)) answer sound.faithful ghostMiss
  constructor
  · simpa only [updated, GroupedBalancedIndexLabeledAudit67.signStep]
      using (cacheBoth state.residual audit.h5cache sound.agree
        (indexInput pair.1 pair.2) answer)
  · exact coveredUpdated
  · simpa only [updated, GroupedBalancedIndexLabeledAudit67.signStep,
      sound.signedEq]
  · exact witnessed
  · exact GroupedBalancedIndexLabeledDrawFaithful67.signStep
      updated pair faithfulUpdated

#print axioms privateCached
#print axioms privateFresh

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledSignedState67
