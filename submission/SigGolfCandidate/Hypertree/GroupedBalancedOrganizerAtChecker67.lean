import SigGolfCandidate.Hypertree.GroupedBalancedEagerDecompose67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphOrganizerView67
import SigGolfCandidate.Hypertree.GroupedBalancedWireTranscript67

/-! Every winning finite organizer execution reaches the real final
verification Interaction; no abstract checker assumption is needed. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedOrganizerAtChecker67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphMonitorSignCoupling67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedIdealEagerCutoff67
open GroupedBalancedGraphOrganizerView67
open GroupedBalancedEagerDecompose67
open GroupedBalancedGraphMonitorInvariant67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

abbrev sizes : Sizes := GroupedBalancedWireTranscript67.sizes

def AtChecker (answers : SecurityGraphIdeal.PrivateTable)
    (table : PointTable) (cache : QueryCache PointSpec)
    (pk : PublicKey)
    (outcome : Result sizes) (trace : List Action)
    (left : Nat) (final : State) : Prop :=
  ∃ (transcript : SigGolf.Transcript sizes)
    (forgery : SigGolf.Forgery sizes)
    (budget remaining : Nat) (state : State)
    (prefixLog checkerTrace : List Action),
    trace = prefixLog ++ checkerTrace ∧
      Safe table state.signedBottom state.exposed state.residual ∧
      some (some (some outcome, checkerTrace), left, final) ∈ support
        (execute table
          (eagerCutoffView answers cache
            (ofCheck sizes GroupedBalancedWire67.decode
              GroupedBalancedWire67.decode pk transcript forgery)
            budget) remaining state)

theorem winning_at_checker
    (answers : SecurityGraphIdeal.PrivateTable)
    (table : PointTable) (cache : QueryCache PointSpec)
    (pk : PublicKey) (adversary : SigGolf.Adversary sizes)
    (rounds : Nat) (adversaryState : adversary.State)
    (transcript : SigGolf.Transcript sizes)
    (budget remaining : Nat) (state final : State)
    (initial : Safe table state.signedBottom state.exposed state.residual)
    (outcome : Result sizes) (trace : List Action) (left : Nat)
    (member : some (some (some outcome, trace), left, final) ∈ support
      (execute table
        (eagerCutoffView answers cache
          (ofInteract sizes GroupedBalancedWire67.wire
            GroupedBalancedWire67.decode GroupedBalancedWire67.decode
            adversary pk rounds adversaryState transcript)
          budget) remaining state))
    (won : outcome.won = true) :
    AtChecker answers table cache pk outcome trace left final := by
  induction rounds generalizing adversaryState transcript budget remaining state trace with
  | zero =>
      simp only [ofInteract, eagerCutoffView, execute,
        support_pure, Set.mem_singleton_iff] at member
      cases member
      cases won
  | succ rounds ih =>
      rw [ofInteract] at member
      cases action : adversary.step adversaryState with
      | submit forgery =>
          rw [action] at member
          exact ⟨transcript, forgery, budget, remaining, state,
            [], trace, by simp, initial, member⟩
      | step next =>
          rw [action] at member
          exact ih next transcript budget remaining state initial trace member
      | sample n resume =>
          rw [action] at member
          simp only [eagerCutoffView, execute,
            mem_support_bind_iff] at member
          obtain ⟨answer, _, tail⟩ := member
          exact ih (resume answer) transcript budget remaining state initial
            trace tail
      | hash input resume =>
          rw [action] at member
          cases budget with
          | zero =>
              simp only [eagerCutoffView, execute,
                support_pure, Set.mem_singleton_iff] at member
              cases member
          | succ budget =>
              cases remaining with
              | zero =>
                  simp only [eagerCutoffView, execute,
                    support_pure, Set.mem_singleton_iff] at member
                  cases member
              | succ remaining =>
                  obtain ⟨answer, nextState, tailTrace, traceEq,
                    signedEq, nextSafe, tailMember⟩ :=
                    hash_successor_safe answers table cache input
                      (fun answer => ofInteract sizes
                        GroupedBalancedWire67.wire
                        GroupedBalancedWire67.decode
                        GroupedBalancedWire67.decode adversary pk
                        rounds (resume answer)
                        { transcript with
                          hashCalls := transcript.hashCalls + 1 })
                      budget remaining state final initial
                      (some outcome) trace left
                      (by simpa only [eagerCutoffView] using member)
                  obtain ⟨signed, forgery, checkBudget, checkRemaining,
                    checkState, prefixLog, checkTrace, prefixEq,
                    checkSafe, checkMember⟩ :=
                    ih (resume answer)
                      { transcript with
                        hashCalls := transcript.hashCalls + 1 }
                      budget remaining nextState nextSafe tailTrace tailMember
                  refine ⟨signed, forgery, checkBudget, checkRemaining,
                    checkState, .publicHash input :: prefixLog,
                    checkTrace, ?_, checkSafe, checkMember⟩
                  rw [traceEq, prefixEq]
                  rfl
      | sign request resume =>
          rw [action] at member
          dsimp only at member
          by_cases allowed : transcript.signingRequests < LIFETIME
          · rw [if_pos allowed] at member
            cases budget with
            | zero =>
                simp only [eagerCutoffView, execute,
                  support_pure, Set.mem_singleton_iff] at member
                cases member
            | succ budget =>
                cases budget with
                | zero =>
                    simp only [eagerCutoffView, execute,
                      support_pure, Set.mem_singleton_iff] at member
                    cases member
                | succ budget =>
                    let randomizer := answers (.randomizer request.message)
                    let input := SecurityRandomOracle.indexInput
                      request.message randomizer
                    obtain ⟨indexAnswer, nextState, tailTrace,
                      traceEq, present, signedEq, nextSafe, tailMember⟩ :=
                      sign_successor_safe answers table cache request.message
                        (fun signature =>
                          let wire := GroupedBalancedWire67.wire signature
                          let updated : SigGolf.Transcript sizes :=
                            { transcript with
                              signed := (request.message, wire) ::
                                transcript.signed
                              signingRequests := transcript.signingRequests + 1 }
                          ofInteract sizes GroupedBalancedWire67.wire
                            GroupedBalancedWire67.decode
                            GroupedBalancedWire67.decode adversary pk rounds
                            (resume (some wire)) updated)
                        budget remaining state final initial
                        (some outcome) trace left
                        (by simpa only [eagerCutoffView] using member)
                    let index : BitVec 160 := indexAnswer.extractLsb' 0 160
                    let bottomAnswer := table (.inr (.inl index))
                    let signature := GroupedBalancedGraphHonestSignView67.signatureFromAnswers
                      cache randomizer index bottomAnswer
                    let wire := GroupedBalancedWire67.wire signature
                    let updated : SigGolf.Transcript sizes :=
                      { transcript with
                        signed := (request.message, wire) :: transcript.signed
                        signingRequests := transcript.signingRequests + 1 }
                    obtain ⟨signed, forgery, checkBudget, checkRemaining,
                      checkState, prefixLog, checkTrace, prefixEq,
                      checkSafe, checkMember⟩ :=
                      ih (resume (some wire)) updated budget remaining
                        (signed nextState index bottomAnswer)
                        nextSafe tailTrace
                        (by simpa only [signature, wire, updated]
                          using tailMember)
                    refine ⟨signed, forgery, checkBudget, checkRemaining,
                      checkState, .privateHash :: .publicHash input :: prefixLog,
                      checkTrace, ?_, checkSafe, checkMember⟩
                    rw [traceEq, prefixEq]
                    rfl
          · rw [if_neg allowed] at member
            simp only [eagerCutoffView, execute,
              support_pure, Set.mem_singleton_iff] at member
            cases member
            cases won

#print axioms winning_at_checker

end SigGolfCandidate.Hypertree.GroupedBalancedOrganizerAtChecker67
