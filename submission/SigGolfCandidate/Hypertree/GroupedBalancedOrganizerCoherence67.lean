import SigGolfCandidate.Hypertree.GroupedBalancedForgeryLogged67
import SigGolfCandidate.Hypertree.GroupedBalancedWireTranscript67
import SigGolfCandidate.Hypertree.GroupedBalancedOrganizerCheckBridge67
import SigGolfCandidate.Hypertree.GroupedBalancedResidualNoPrivate67
import SigGolfCandidate.Hypertree.GroupedBalancedResidualCompletion67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedStoppedCacheMonotone67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedOrganizerCoherence67. -/
section
/-! Every completed stopped organizer prefix retains all residual oracle
answers that were already cached. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedStoppedCacheMonotone67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphMonitorSignCoupling67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem execute_preserves {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state final : State)
    (result : Option α) (left : Nat)
    (member : some (result, left, final) ∈ support
      (execute table view remaining state))
    (old : Query) (answer : BitVec 256)
    (present : state.residual old = some answer) :
    final.residual old = some answer := by
  induction view generalizing remaining state with
  | done value =>
      simp only [execute, support_pure,
        Set.mem_singleton_iff] at member
      cases member
      exact present
  | coin n next ih =>
      simp only [execute, mem_support_bind_iff] at member
      obtain ⟨value, _, tail⟩ := member
      exact ih value remaining state tail present
  | sign index next ih =>
      exact ih (table (.inr (.inl index))) remaining
        (signed state index (table (.inr (.inl index))))
        (by simpa only [execute] using member)
        (by simpa only [signed] using present)
  | privateHash input outside next ih =>
      cases cached : state.residual input with
      | some value =>
          exact ih value remaining state
            (by simpa only [execute, cached] using member) present
      | none =>
          simp only [execute, cached, mem_support_bind_iff] at member
          obtain ⟨value, _, tail⟩ := member
          have different : old ≠ input := by
            intro same
            subst old
            rw [cached] at present
            cases present
          exact ih value remaining (privateOpened state input value)
            tail (by simpa only [privateOpened,
              QueryCache.cacheQuery_of_ne _ _ different] using present)
  | hash input next ih =>
      cases remaining with
      | zero =>
          simp only [execute, support_pure,
            Set.mem_singleton_iff] at member
          cases member
          exact present
      | succ remaining =>
          simp only [execute] at member
          by_cases first : GroupedBalancedGraphMonitorPublicCoupling67.inputHit
              table state.exposed input
          · simp only [if_pos first, support_pure,
              Set.mem_singleton_iff, Option.some_ne_none] at member
          · simp only [if_neg first, mem_support_bind_iff] at member
            obtain ⟨read, readMember, tail⟩ := member
            by_cases second : GroupedBalancedGraphMonitorPublicCoupling67.outputHit
                table input read.1
            · simp only [if_pos second, support_pure,
                Set.mem_singleton_iff, Option.some_ne_none] at tail
            · simp only [if_neg second] at tail
              exact ih read.1 remaining
                (opened state
                  (GroupedBalancedGraphMonitorPublicCoupling67.opened
                    table state.exposed input) read.2)
                tail (GroupedBalancedVerifierCache67.query_preserves
                  table input state.residual read readMember
                  old answer present)

theorem execute_agree_backward {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state final : State)
    (result : Option α) (left : Nat)
    (member : some (result, left, final) ∈ support
      (execute table view remaining state))
    (hash : Hash) (finalAgree : final.residual.AgreesWithFn hash) :
    state.residual.AgreesWithFn hash := by
  intro query answer present
  exact finalAgree (execute_preserves table view remaining state final
    result left member query answer present)

#print axioms execute_preserves
#print axioms execute_agree_backward

end SigGolfCandidate.Hypertree.GroupedBalancedStoppedCacheMonotone67
end

/-! The exact signed-index set and honest-response invariant carried by the
organizer wire transcript. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedTranscriptInvariant67
open SigGolf SigGolfCandidate.Hypertree Reference
set_option backward.isDefEq.respectTransparency false

def indices (hash : Hash)
    (responses : GroupedBalancedStrongExtraction67.History) :
    Finset (BitVec 160) :=
  (responses.map (fun entry =>
    Reference.indexOf hash entry.1 entry.2.randomizer)).toFinset

theorem mem_indices (hash : Hash)
    (responses : GroupedBalancedStrongExtraction67.History)
    (index : BitVec 160) :
    index ∈ indices hash responses ↔
      ∃ entry ∈ responses,
        Reference.indexOf hash entry.1 entry.2.randomizer = index := by
  simp only [indices, List.mem_toFinset, List.mem_map]

theorem indices_cons (hash : Hash) (message : Message)
    (signature : GroupedBalancedScheme67.Signature)
    (responses : GroupedBalancedStrongExtraction67.History) :
    indices hash ((message, signature) :: responses) =
      insert (Reference.indexOf hash message signature.randomizer)
        (indices hash responses) := by
  simp only [indices, List.map_cons, List.toFinset_cons]

theorem honest_nil (hash : Hash) (secretKey : SecretKey) :
    GroupedBalancedStrongExtraction67.HonestHistory hash secretKey [] := by
  intro entry member
  cases member

theorem honest_cons (hash : Hash) (secretKey : SecretKey)
    (message : Message)
    (responses : GroupedBalancedStrongExtraction67.History)
    (honest : GroupedBalancedStrongExtraction67.HonestHistory
      hash secretKey responses) :
    GroupedBalancedStrongExtraction67.HonestHistory hash secretKey
      ((message, GroupedBalancedScheme67.sign hash secretKey message) ::
        responses) := by
  intro entry member
  rcases List.mem_cons.mp member with same | member
  · simpa only [same]
  · exact honest entry member

theorem indices_response_after_structured
    (hash : Hash)
    (transcript : SigGolf.Transcript GroupedBalancedWireTranscript67.sizes)
    (message : Message)
    (signature : GroupedBalancedScheme67.Signature) :
    indices hash (GroupedBalancedWireTranscript67.responses
      (GroupedBalancedWireTranscript67.afterSign transcript message
        (some (GroupedBalancedWire67.wire signature)))) =
      insert (Reference.indexOf hash message signature.randomizer)
        (indices hash (GroupedBalancedWireTranscript67.responses transcript)) := by
  rw [GroupedBalancedWireTranscript67.responses_after_structured]
  exact indices_cons hash message signature _

#print axioms mem_indices
#print axioms indices_response_after_structured

end SigGolfCandidate.Hypertree.GroupedBalancedTranscriptInvariant67


/-! Signed wire responses are honest for a fixed total completion hash, and
their H5 indices are exactly the bottom indices authorized in monitor state. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedOrganizerCoherence67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphMonitorSignCoupling67
open GroupedBalancedGraphMonitorInvariant67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedIdealEagerCutoff67
open GroupedBalancedGraphOrganizerView67
open GroupedBalancedEagerDecompose67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

abbrev sizes : Sizes := GroupedBalancedOrganizerAtChecker67.sizes

def Coherent (hash : Hash) (secretKey : SecretKey)
    (state : State) (transcript : SigGolf.Transcript sizes) : Prop :=
  GroupedBalancedStrongExtraction67.HonestHistory hash secretKey
    (GroupedBalancedWireTranscript67.responses transcript) ∧
  state.signedBottom =
    GroupedBalancedTranscriptInvariant67.indices hash
      (GroupedBalancedWireTranscript67.responses transcript)

theorem empty (hash : Hash) (secretKey : SecretKey)
    (state : State) (empty : state.signedBottom = ∅) :
    Coherent hash secretKey state {} := by
  constructor
  · exact GroupedBalancedTranscriptInvariant67.honest_nil hash secretKey
  · simpa only [GroupedBalancedWireTranscript67.responses,
      GroupedBalancedTranscriptInvariant67.indices,
      List.map_nil, List.toFinset_nil] using empty

theorem hashStep (hash : Hash) (secretKey : SecretKey)
    (state : State) (transcript : SigGolf.Transcript sizes)
    (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec)
    (old : Coherent hash secretKey state transcript) :
    Coherent hash secretKey (opened state exposed residual)
      { transcript with hashCalls := transcript.hashCalls + 1 } := by
  exact old

theorem signed (hash : Hash) (secretKey : SecretKey)
    (state : State) (transcript : SigGolf.Transcript sizes)
    (message : Message) (signature : GroupedBalancedScheme67.Signature)
    (index : BitVec 160) (bottomAnswer : BitVec 256)
    (old : Coherent hash secretKey state transcript)
    (honest : signature = GroupedBalancedScheme67.sign hash secretKey message)
    (indexEq : Reference.indexOf hash message signature.randomizer = index) :
    Coherent hash secretKey (GroupedBalancedGraphMonitorSignCompiler67.signed
      state index bottomAnswer)
      (GroupedBalancedWireTranscript67.afterSign transcript message
        (some (GroupedBalancedWire67.wire signature))) := by
  rw [Coherent,
    GroupedBalancedWireTranscript67.responses_after_structured]
  constructor
  · rw [honest]
    exact GroupedBalancedTranscriptInvariant67.honest_cons
      hash secretKey message _ old.1
  · simp only [GroupedBalancedGraphMonitorSignCompiler67.signed,
      GroupedBalancedTranscriptInvariant67.indices_cons]
    rw [indexEq, ← old.2]

def SignLaw (hash : Hash) (secretKey : SecretKey)
    (answers : SecurityGraphIdeal.PrivateTable)
    (table : PointTable) (cache : QueryCache PointSpec) : Prop :=
  ∀ message indexAnswer,
    hash (SecurityRandomOracle.indexInput message
      (answers (.randomizer message))) = indexAnswer →
    GroupedBalancedScheme67.sign hash secretKey message =
      GroupedBalancedGraphHonestSignView67.signatureFromAnswers cache
        (answers (.randomizer message))
        (indexAnswer.extractLsb' 0 160)
        (table (.inr (.inl (indexAnswer.extractLsb' 0 160))))

theorem programmed_index (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (message : Message) (randomizer : Bytes 32) :
    GroupedBalancedGraphProgrammedReference67.programmedGrouped
      residual secretKey labels
      (SecurityRandomOracle.indexInput message randomizer) =
      residual (SecurityRandomOracle.indexInput message randomizer) := by
  unfold GroupedBalancedGraphProgrammedReference67.programmedGrouped
  rw [GroupedBalancedGraphQuery67.locate_programmed]
  rw [GroupedBalancedGraphHonestSignView67.locate_index_none]

theorem completion_signLaw (table : PointTable)
    (answers : SecurityGraphIdeal.PrivateTable)
    (secretKey : SecretKey) (finalCache : QueryCache HashSpec) :
    SignLaw
      (GroupedBalancedGraphProgrammedReference67.programmedGrouped
        (GroupedBalancedResidualCompletion67.completion
          table answers secretKey finalCache)
        secretKey (GroupedBalancedGraphMonitorTable67.labelsOf table))
      secretKey answers table (GroupedBalancedGraphMonitorSetup67.cache table) := by
  intro message indexAnswer selected
  let residual := GroupedBalancedResidualCompletion67.completion
    table answers secretKey finalCache
  let hash := GroupedBalancedGraphProgrammedReference67.programmedGrouped
    residual secretKey (GroupedBalancedGraphMonitorTable67.labelsOf table)
  have nonceEq : Reference.randomizer residual secretKey message =
      answers (.randomizer message) :=
    GroupedBalancedResidualCompletion67.completion_randomizer
      table answers secretKey finalCache message
  have indexEq : residual
      (SecurityRandomOracle.indexInput message
        (answers (.randomizer message))) = indexAnswer := by
    have outside := programmed_index residual secretKey
      (GroupedBalancedGraphMonitorTable67.labelsOf table)
      message (answers (.randomizer message))
    exact outside.symm.trans selected
  have signing :=
    GroupedBalancedGraphHonestSignView67.programmed_sign_from_answers
      residual secretKey
      (GroupedBalancedGraphMonitorTable67.labelsOf table) table rfl
      (GroupedBalancedResidualCompletion67.completion_bottom
        table answers secretKey finalCache)
      (GroupedBalancedResidualCompletion67.completion_upper
        table answers secretKey finalCache) message
  change GroupedBalancedScheme67.sign hash secretKey message =
    GroupedBalancedGraphHonestSignView67.signatureFromAnswers
      (GroupedBalancedGraphMonitorSetup67.cache table)
      (Reference.randomizer residual secretKey message)
      ((residual (SecurityRandomOracle.indexInput message
        (Reference.randomizer residual secretKey message))).extractLsb' 0 160)
      (table (.inr (.inl
        ((residual (SecurityRandomOracle.indexInput message
          (Reference.randomizer residual secretKey message))).extractLsb' 0 160)))) at signing
  rw [nonceEq, indexEq] at signing
  exact signing

#print axioms empty
#print axioms signed
#print axioms completion_signLaw

end SigGolfCandidate.Hypertree.GroupedBalancedOrganizerCoherence67
