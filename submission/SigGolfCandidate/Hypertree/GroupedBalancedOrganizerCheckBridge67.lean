import SigGolfCandidate.Hypertree.GroupedBalancedEagerDecompose67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifierCache67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphInteractionGame67
import SigGolfCandidate.Hypertree.GroupedBalancedOrganizerAtChecker67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedEagerVerifierBudget67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedOrganizerCheckBridge67. -/
section
/-! A completed budgeted hash-only eager phase is an actual completed run of
the verifier compiler, with the same final caches and signed-index set. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedEagerVerifierBudget67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphMonitorSignCoupling67
open GroupedBalancedGraphMonitorInvariant67
open GroupedBalancedGraphMonitorStop67
open GroupedBalancedGraphMonitorCompose67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedIdealEagerCutoff67
open GroupedBalancedGraphInteractionGame67
open GroupedBalancedVerifierCache67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem completed {α β : Type}
    (answers : SecurityGraphIdeal.PrivateTable)
    (table : PointTable) (publicCache : QueryCache PointSpec)
    (program : OracleComp HashSpec α) (finish : α → β)
    (budget remaining : Nat) (state final : State)
    (initial : Safe table state.signedBottom state.exposed state.residual)
    (result : Option β) (trace : List Action) (left : Nat)
    (member : some (some (result, trace), left, final) ∈ support
      (execute table
        (eagerCutoffView answers publicCache
          (ofHash program (fun value => .done (finish value))) budget)
        remaining state))
    (finished : result ≠ none) :
    ∃ value, result = some (finish value) ∧
      some (value, final.exposed, final.residual) ∈ support
        (stopped table state.exposed
          (compile program state.exposed state.residual)) ∧
      final.signedBottom = state.signedBottom := by
  induction program using OracleComp.inductionOn
      generalizing budget remaining state trace with
  | pure value =>
      simp only [ofHash_pure, eagerCutoffView, execute,
        support_pure, Set.mem_singleton_iff] at member
      cases member
      refine ⟨value, rfl, ?_, rfl⟩
      simp only [compile_pure, stopped, support_pure,
        Set.mem_singleton_iff]
  | query_bind query next ih =>
      rw [ofHash_query] at member
      cases budget with
      | zero =>
          simp only [eagerCutoffView, execute,
            support_pure, Set.mem_singleton_iff] at member
          cases member
          exact False.elim (finished rfl)
      | succ budget =>
          cases remaining with
          | zero =>
              simp only [eagerCutoffView, execute,
                support_pure, Set.mem_singleton_iff] at member
              cases member
          | succ remaining =>
              have queryMember : some (some (result, trace), left, final) ∈
                  support (execute table
                    (.hash query (fun answer =>
                      GroupedBalancedGameViewLoggedBridge67.prependAction
                        (.publicHash query)
                        (eagerCutoffView answers publicCache
                          (ofHash (next answer)
                            (fun value => .done (finish value))) budget)))
                    (remaining + 1) state) := by
                simpa only [eagerCutoffView] using member
              simp only [execute] at queryMember
              by_cases first :
                  GroupedBalancedGraphMonitorPublicCoupling67.inputHit
                    table state.exposed query
              · simp only [if_pos first, support_pure,
                  Set.mem_singleton_iff, Option.some_ne_none] at queryMember
              · simp only [if_neg first, mem_support_bind_iff] at queryMember
                obtain ⟨answer, queried, tail⟩ := queryMember
                by_cases second :
                    GroupedBalancedGraphMonitorPublicCoupling67.outputHit
                      table query answer.1
                · simp only [if_pos second, support_pure,
                    Set.mem_singleton_iff, Option.some_ne_none] at tail
                · simp only [if_neg second] at tail
                  let opened := GroupedBalancedGraphMonitorPublicCoupling67.opened
                    table state.exposed query
                  let nextState := GroupedBalancedGraphMonitorSignCompiler67.opened
                    state opened answer.2
                  obtain ⟨tailTrace, traceEq, child⟩ :=
                    GroupedBalancedResidualNoPrivate67.prepend_decompose
                      table (.publicHash query)
                      (eagerCutoffView answers publicCache
                        (ofHash (next answer.1)
                          (fun value => .done (finish value))) budget)
                      remaining nextState final result trace left
                      (by simpa only [nextState] using tail)
                  have read :=
                    GroupedBalancedGraphMonitorCompileCoupling67.read_supported
                      table state.signedBottom state.exposed state.residual
                      initial query answer queried first second
                  have nextSafe :=
                    GroupedBalancedGraphMonitorPublicUnified67.public_read_safe
                      table state.signedBottom state.exposed state.residual
                      initial query (answer.1, opened, answer.2) read
                  obtain ⟨value, output, raw, signedEq⟩ :=
                    ih answer.1 budget remaining nextState
                      (by simpa only [nextState,
                        GroupedBalancedGraphMonitorSignCompiler67.opened]
                        using nextSafe)
                      tailTrace
                      (by simpa only [nextState] using child)
                  refine ⟨value, output, ?_, ?_⟩
                  · rw [compile_query,
                      stopped_public_bind table state.signedBottom
                        state.exposed state.residual initial,
                      mem_support_bind_iff]
                    exact ⟨some (answer.1, opened, answer.2),
                      read, by simpa only [continueWith, nextState,
                        GroupedBalancedGraphMonitorSignCompiler67.opened]
                        using raw⟩
                  · simpa only [nextState,
                      GroupedBalancedGraphMonitorSignCompiler67.opened]
                      using signedEq

#print axioms completed

end SigGolfCandidate.Hypertree.GroupedBalancedEagerVerifierBudget67

end

/-! Both organizer forgery modes use the exact stopped direct67 verifier.
A winning wire candidate is fresh in the decoded structured history. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedOrganizerCheckBridge67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphMonitorSignCoupling67
open GroupedBalancedGraphMonitorInvariant67
open GroupedBalancedGraphMonitorStop67
open GroupedBalancedIdealEagerCutoff67
open GroupedBalancedGraphOrganizerView67
open GroupedBalancedGameQueryTrace67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem completed_winning_check
    (answers : SecurityGraphIdeal.PrivateTable)
    (table : PointTable) (cache : QueryCache PointSpec)
    (pk : PublicKey)
    (transcript : SigGolf.Transcript GroupedBalancedOrganizerAtChecker67.sizes)
    (forgery : SigGolf.Forgery GroupedBalancedOrganizerAtChecker67.sizes)
    (budget remaining : Nat) (state final : State)
    (initial : Safe table state.signedBottom state.exposed state.residual)
    (outcome : Result GroupedBalancedOrganizerAtChecker67.sizes)
    (trace : List Action) (left : Nat)
    (member : some (some (some outcome, trace), left, final) ∈ support
      (execute table
        (eagerCutoffView answers cache
          (ofCheck GroupedBalancedOrganizerAtChecker67.sizes
            GroupedBalancedWire67.decode GroupedBalancedWire67.decode
            pk transcript forgery) budget)
        remaining state))
    (won : outcome.won = true) :
    ∃ message signature,
      outcome.candidate = some (message, signature) ∧
      outcome.transcript = transcript ∧
      (message, signature) ∉
        GroupedBalancedWireTranscript67.responses transcript ∧
      some (true, final.exposed, final.residual) ∈ support
        (stopped table state.exposed
          (GroupedBalancedVerifierCache67.compile
            (GroupedBalancedVerifyOracle67.verify pk message signature)
            state.exposed state.residual)) ∧
      final.signedBottom = state.signedBottom := by
  cases forgery with
  | witness message witness =>
      let signature := GroupedBalancedWire67.decode witness
      let finish := fun accepted : Bool =>
        (⟨accepted && transcript.freshMessage message,
          some (message, signature), transcript⟩ :
          Result GroupedBalancedOrganizerAtChecker67.sizes)
      have checked : some (some (some outcome, trace), left, final) ∈ support
          (execute table
            (eagerCutoffView answers cache
              (GroupedBalancedGraphInteractionGame67.ofHash
                (GroupedBalancedVerifyOracle67.verify pk message signature)
                (fun accepted => .done (finish accepted))) budget)
            remaining state) := by
        simpa only [ofCheck, signature, finish] using member
      obtain ⟨accepted, equal, raw, signedEq⟩ :=
        GroupedBalancedEagerVerifierBudget67.completed answers table cache
          (GroupedBalancedVerifyOracle67.verify pk message signature)
          finish budget remaining state final initial
          (some outcome) trace left checked (by simp)
      have outcomeEq : outcome = finish accepted := Option.some.inj equal
      have both : (accepted && transcript.freshMessage message) = true := by
        simpa only [outcomeEq, finish] using won
      have acceptedTrue := (Bool.and_eq_true_iff.mp both).1
      have freshTrue := (Bool.and_eq_true_iff.mp both).2
      refine ⟨message, signature, ?_, ?_, ?_, ?_, signedEq⟩
      · simp only [outcomeEq, finish]
      · simp only [outcomeEq, finish]
      · exact GroupedBalancedWireTranscript67.fresh_message
          transcript message signature freshTrue
      · simpa only [acceptedTrue] using raw
  | signature message wire =>
      let signature := GroupedBalancedWire67.decode wire
      let finish := fun accepted : Bool =>
        (⟨accepted && transcript.freshSignature message wire,
          some (message, signature), transcript⟩ :
          Result GroupedBalancedOrganizerAtChecker67.sizes)
      have checked : some (some (some outcome, trace), left, final) ∈ support
          (execute table
            (eagerCutoffView answers cache
              (GroupedBalancedGraphInteractionGame67.ofHash
                (GroupedBalancedVerifyOracle67.verify pk message signature)
                (fun accepted => .done (finish accepted))) budget)
            remaining state) := by
        simpa only [ofCheck, signature, finish] using member
      obtain ⟨accepted, equal, raw, signedEq⟩ :=
        GroupedBalancedEagerVerifierBudget67.completed answers table cache
          (GroupedBalancedVerifyOracle67.verify pk message signature)
          finish budget remaining state final initial
          (some outcome) trace left checked (by simp)
      have outcomeEq : outcome = finish accepted := Option.some.inj equal
      have both : (accepted && transcript.freshSignature message wire) = true := by
        simpa only [outcomeEq, finish] using won
      have acceptedTrue := (Bool.and_eq_true_iff.mp both).1
      have freshTrue := (Bool.and_eq_true_iff.mp both).2
      refine ⟨message, signature, ?_, ?_, ?_, ?_, signedEq⟩
      · simp only [outcomeEq, finish]
      · simp only [outcomeEq, finish]
      · exact GroupedBalancedWireTranscript67.fresh_signature
          transcript message wire freshTrue
      · simpa only [acceptedTrue] using raw

#print axioms completed_winning_check

end SigGolfCandidate.Hypertree.GroupedBalancedOrganizerCheckBridge67
