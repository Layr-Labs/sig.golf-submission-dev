import SigGolfCandidate.Hypertree.SecurityMonitorGraphView
import SigGolfCandidate.Hypertree.SecurityGraphMonitorNoContact
import SigGolfCandidate.Hypertree.SecurityMonitorViewAtomic

/-! Inlined from SigGolfCandidate.Hypertree.SecurityMonitorGraphState; its only importer was SigGolfCandidate.Hypertree.SecurityMonitorGraphStoppedView. -/
section
namespace SigGolfCandidate.Hypertree.SecurityMonitorGraphState
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphQuery
  SecurityGraphFrontier SecurityGraphPassive SecurityGraphDisclosure SecurityGraphFactor
  SecurityGraphAuthorization SecurityGraphMonitorProgram SecurityGraphMonitorSign
  SecurityGraphMonitorInvariant SecurityGraphMonitorChainState SecurityGraphMonitorPublicState
  SecurityGraphMonitorPublicCoupling SecurityGraphMonitorNoContact SecurityMonitorIndexState
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

def Ready (factors : Factors) (history : History) (exposed : QueryCache PointSpec)
    (residual : QueryCache HashSpec) : Prop :=
  Safe factors history.signedIndices exposed residual ∧ PublicReady factors.1 exposed

theorem PublicReady.cacheQuery {table : PointTable} {exposed : QueryCache PointSpec}
    (ready : PublicReady table exposed) (point : Point) :
    PublicReady table (exposed.cacheQuery point (table point)) := ready.reveal [point]

theorem opened_ready (factors : Factors) (exposed : QueryCache PointSpec) (query : Query)
    (ready : PublicReady factors.1 exposed) : PublicReady factors.1 (opened factors exposed query) := by
  unfold opened
  cases locate query with
  | none => exact ready
  | some position =>
    cases position with
    | chain address step =>
      dsimp only
      split
      · exact PublicReady.cacheQuery ready _
      · exact ready
    | leaf level tree side | node level tree => exact ready.reveal _

theorem parsed_indices (history : History) (query : Query) (parsed : Option (Message × Bytes 32))
    (eligible cached : Bool) (answer : BitVec 256) :
    (recordParsed history query parsed eligible cached answer).signedIndices = history.signedIndices := by
  cases parsed with
  | some pair => rfl
  | none => cases eligible <;> rfl

attribute [local irreducible] recordParsed

theorem public_indices (history : History) (query : Query) (cached : Bool) (answer : BitVec 256) :
    (recordPublic history query cached answer).signedIndices = history.signedIndices :=
  parsed_indices history query (SecurityIndexQuery.parse query)
    (decide (SecuritySeparation.SecretKeyEligible query)) cached answer

/-- The concrete public step preserves everything required to execute future
honest signing macros, including the public endpoint disclosures. -/
theorem public_ready (factors : Factors) (history : History)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (initial : Ready factors history exposed cache)
    (query : Query) (result : Answer)
    (member : some result ∈ support (stopped factors.1 exposed
      (SecurityGraphMonitorOracle.publicStep factors.2.2 exposed cache query
        (fun answer opened residual => .done (answer, opened, residual))))) :
    Ready factors (recordPublic history query (cache query).isSome result.1) result.2.1 result.2.2 := by
  have safe := public_read_safe factors history.signedIndices exposed cache initial.1 query result member
  have spec := read_spec factors history.signedIndices exposed cache initial.1 query result member
  refine ⟨?_, ?_⟩
  · simpa only [public_indices] using safe
  · rw [spec.2.2.1]
    exact opened_ready factors exposed query initial.2

/-- The selected honest signature coordinates are authorized after inserting
this signing index; point selection itself depends only on disclosed metadata. -/
theorem needed_authorized (factors : Factors) (history : History) (exposed : QueryCache PointSpec)
    (ready : PublicReady factors.1 exposed) (index : BitVec 160) :
    ∀ point ∈ needed factors.2.2 exposed index,
      Authorized factors.2.2 (insert index history.signedIndices) point := by
  intro point member
  rw [needed, Finset.mem_toList] at member
  have same := signaturePoints_congr _ _ (metadata_ready factors.1 factors.2.1 factors.2.2 exposed ready) index
  rw [same] at member
  exact signaturePoints_authorized factors (insert index history.signedIndices) index (Finset.mem_insert_self ..)
    point member

/-- A completed H5 lookup plus honest disclosure preserves the full graph state.
The raw H5 answer, and therefore the exact signed index, are retained. -/
theorem sign_ready (factors : Factors) (history : History) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (initial : Ready factors history exposed cache)
    (message : Message) (answer : BitVec 256) (residual : QueryCache HashSpec)
    (member : (answer, residual) ∈ support ((randomOracle (spec := HashSpec)
      (SecurityRandomOracle.indexInput message (factors.2.1 message))).run cache)) :
    Ready factors (recordSign history message
      (cache (SecurityRandomOracle.indexInput message (factors.2.1 message))).isSome answer)
      (revealCache factors.1 (needed factors.2.2 exposed (answer.extractLsb' 0 160)) exposed) residual := by
  have safeResidual : ResidualSafe factors residual := by
    let query := SecurityRandomOracle.indexInput message (factors.2.1 message)
    have outside := SecurityIndexQuery.locate_index message (factors.2.1 message)
    change (answer, residual) ∈ support ((randomOracle (spec := HashSpec) query).run cache) at member
    cases present : cache query with
    | some value =>
      simp only [randomOracle.run_eq, present, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at member
      exact member.2 ▸ initial.1.2.2
    | none =>
      simp only [randomOracle.run_eq, present, bind_pure_comp, support_map, Set.mem_image] at member
      obtain ⟨value, _, equal⟩ := member
      cases equal
      apply initial.1.2.2.cacheQuery factors cache query answer
      intro position impossible
      rw [outside] at impossible
      cases impossible
  refine ⟨⟨initial.1.1.revealCache _, ?_, safeResidual⟩, initial.2.reveal _⟩
  apply ExposedSafe.revealCache
  · exact initial.1.2.1.mono factors.2.2 (fun _ member => Finset.mem_insert_of_mem member) exposed
  · exact needed_authorized factors history exposed initial.2 _

/-- The actual finite setup reveal prefix establishes the state invariant. -/
theorem setup_ready (factors : Factors) :
    Ready factors (recordKeygen {}) (SecurityGraphMonitorSetup.cache factors.1 factors.2.2) ∅ := by
  refine ⟨⟨SecurityGraphMonitorSetup.cache_agree _ _, ?_, residualSafe_empty factors⟩,
    SecurityGraphMonitorSetup.cache_publicReady _ _⟩
  exact SecurityGraphMonitorSetup.cache_authorized factors.1 factors.2.2

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorGraphState.sign_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sign_ready
end SigGolfCandidate.Hypertree.SecurityMonitorGraphState

end

namespace SigGolfCandidate.Hypertree.SecurityMonitorGraphStoppedView
open SigGolf OracleComp OracleSpec Reference SecurityGraphFactor SecurityGraphPassive
  SecurityGraphDisclosure SecurityGraphMonitorProgram SecurityGraphMonitorSign SecurityGraphMonitorMetadata
  SecurityGraphMonitorPublicCoupling SecurityGraphMonitorNoContact SecurityGraphMonitorChainState
  SecurityMonitorView SecurityMonitorIndexState SecurityMonitorGraphView SecurityMonitorGraphState
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical
attribute [local irreducible] recordParsed

/-- Mathematical stopped execution through the actual graph oracle. Secret
coordinates are inspected only to define the stopping events, never to supply
extra information to the passive simulator's continuation. -/
noncomputable def execute {α : Type} (factors : Factors) :
    View α → Nat → QueryCache PointSpec → QueryCache HashSpec → History → ProbComp (Option (Result α))
  | .done value, remaining, exposed, cache, history => pure (some ⟨some value, remaining, exposed, cache, history⟩)
  | .coin n next, remaining, exposed, cache, history => do
      let answer ← $ᵗ Fin (n + 1)
      execute factors (next answer) remaining exposed cache history
  | .hash input next, remaining, exposed, cache, history =>
      match remaining with
      | 0 => pure (some ⟨none, 0, exposed, cache, history⟩)
      | remaining + 1 =>
          if inputHit factors exposed input then pure none else do
            let result ← (SecurityGraphOracle.publicOracle (privateTable factors) (labels factors) input).run cache
            if outputHit factors input result.1 then pure none else
              execute factors (next result.1) remaining (opened factors exposed input) result.2
                (recordPublic history input (cache input).isSome result.1)
  | .sign message next, remaining, exposed, cache, history =>
      if 117508 ≤ remaining then do
        let result ← (randomOracle (spec := HashSpec)
          (SecurityRandomOracle.indexInput message (factors.2.1 message))).run cache
        let index := result.1.extractLsb' 0 160
        let response := SecurityExperiment.serialize
          (SecurityGraphSigner.signature (privateTable factors) (labels factors) (factors.2.1 message) index)
        let opened := revealCache factors.1 (needed factors.2.2 exposed index) exposed
        execute factors (next response) (remaining - 117508) opened result.2
          (recordSign history message
            (cache (SecurityRandomOracle.indexInput message (factors.2.1 message))).isSome result.1)
      else pure (some ⟨none, remaining, exposed, cache, history⟩)

theorem stopped_indexStep {α : Type} (table : PointTable) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (query : Query) (next : BitVec 256 → QueryCache HashSpec → Program α) :
    stopped table exposed (indexStep cache query next) =
      ((randomOracle (spec := HashSpec) query).run cache >>= fun result => stopped table exposed (next result.1 result.2)) := by
  cases present : cache query <;> simp only [indexStep, present, stopped, randomOracle.run_eq, pure_bind, bind_assoc]

/-- A supported real graph query that misses both contacts appears as a normal
read in the operational monitor; its exact state can feed the next induction step. -/
theorem read_supported (factors : Factors) (history : History) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (ready : Ready factors history exposed cache) (query : Query)
    (result : BitVec 256 × QueryCache HashSpec)
    (member : result ∈ support ((SecurityGraphOracle.publicOracle (privateTable factors) (labels factors) query).run cache))
    (first : ¬inputHit factors exposed query) (second : ¬outputHit factors query result.1) :
    some (result.1, opened factors exposed query, result.2) ∈ support (stopped factors.1 exposed
      (SecurityGraphMonitorOracle.publicStep factors.2.2 exposed cache query
        (fun answer opened residual => Program.done (answer, opened, residual)))) := by
  rw [stopped_public_oracle _ _ _ _ _ ready.1.1 ready.1.2.2, if_neg first, mem_support_bind_iff]
  refine ⟨result, member, ?_⟩
  simp only [if_neg second, stopped, support_pure, Set.mem_singleton_iff]

/-- Exact full adaptive-view coupling. This is the actual shared compiler, with
signing responses, both caches, history, remaining budget, and every private coin
preserved up to the first graph contact. -/
theorem stopped_compile {α : Type} (factors : Factors) (view : View α)
    (remaining : Nat) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (history : History)
    (ready : Ready factors history exposed cache) :
    𝒮[stopped factors.1 exposed
      (compile factors.2.1 factors.2.2 view remaining exposed cache history)] =
      𝒮[execute factors view remaining exposed cache history] := by
  induction view generalizing remaining exposed cache history with
  | done value => rfl
  | coin n next ih =>
    simp only [compile, execute, stopped]
    apply evalSPMF_bind_congr
    intro answer _
    exact ih answer remaining exposed cache history ready
  | hash query next ih =>
    cases remaining with
    | zero => rfl
    | succ remaining =>
      simp only [compile, execute]
      rw [stopped_public_oracle _ _ _ _ _ ready.1.1 ready.1.2.2]
      by_cases first : inputHit factors exposed query
      · simp only [if_pos first]
      · simp only [if_neg first]
        apply evalSPMF_bind_congr
        intro result member
        by_cases second : outputHit factors query result.1
        · simp only [if_pos second]
        · simp only [if_neg second]
          have queried := read_supported factors history exposed cache ready query result member first second
          exact ih result.1 remaining _ result.2 _
            (public_ready factors history exposed cache ready query _ queried)
  | sign message next ih =>
    simp only [compile, execute]
    by_cases enough : 117508 ≤ remaining
    · simp only [if_pos enough]
      rw [stopped_indexStep]
      apply evalSPMF_bind_congr
      intro result member
      rw [stopped_disclose]
      rw [opened_signature factors.1 factors.2.1 factors.2.2 exposed ready.2]
      exact ih _ (remaining - 117508) _ result.2 _
        (sign_ready factors history exposed cache ready message result.1 result.2 member)
    · simp only [if_neg enough, stopped]

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorGraphStoppedView.stopped_compile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stopped_compile
end SigGolfCandidate.Hypertree.SecurityMonitorGraphStoppedView
