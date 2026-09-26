import SigGolfCandidate.Hypertree.GroupedBalancedOrganizerCoherence67

/-! The actual winning organizer checker is reached with an honest decoded
response history and exactly the bottom indices authorized by that history. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedOrganizerCoherentChecker67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphMonitorSignCoupling67
open GroupedBalancedGraphMonitorInvariant67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedIdealEagerCutoff67
open GroupedBalancedGraphOrganizerView67
open GroupedBalancedEagerDecompose67
open GroupedBalancedOrganizerCoherence67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

abbrev sizes : Sizes := GroupedBalancedOrganizerCoherence67.sizes

def AtChecker (hash : Hash) (secretKey : SecretKey)
    (answers : SecurityGraphIdeal.PrivateTable)
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
      Coherent hash secretKey state transcript ∧
      some (some (some outcome, checkerTrace), left, final) ∈ support
        (execute table
          (eagerCutoffView answers cache
            (ofCheck sizes GroupedBalancedWire67.decode
              GroupedBalancedWire67.decode pk transcript forgery)
            budget) remaining state)

theorem winning_at_checker
    (hash : Hash) (secretKey : SecretKey)
    (answers : SecurityGraphIdeal.PrivateTable)
    (table : PointTable) (cache : QueryCache PointSpec)
    (pk : PublicKey) (adversary : SigGolf.Adversary sizes)
    (rounds : Nat) (adversaryState : adversary.State)
    (transcript : SigGolf.Transcript sizes)
    (budget remaining : Nat) (state final : State)
    (initial : Safe table state.signedBottom state.exposed state.residual)
    (coherent : Coherent hash secretKey state transcript)
    (finalAgree : final.residual.AgreesWithFn hash)
    (signLaw : SignLaw hash secretKey answers table cache)
    (outcome : Result sizes) (trace : List Action) (left : Nat)
    (member : some (some (some outcome, trace), left, final) ∈ support
      (execute table
        (eagerCutoffView answers cache
          (ofInteract sizes GroupedBalancedWire67.wire
            GroupedBalancedWire67.decode GroupedBalancedWire67.decode
            adversary pk rounds adversaryState transcript)
          budget) remaining state))
    (won : outcome.won = true) :
    AtChecker hash secretKey answers table cache pk
      outcome trace left final := by
  induction rounds generalizing adversaryState transcript budget remaining
      state trace with
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
            [], trace, by simp, initial, coherent, member⟩
      | step next =>
          rw [action] at member
          exact ih next transcript budget remaining state initial coherent
            trace member
      | sample n resume =>
          rw [action] at member
          simp only [eagerCutoffView, execute,
            mem_support_bind_iff] at member
          obtain ⟨answer, _, tail⟩ := member
          exact ih (resume answer) transcript budget remaining state
            initial coherent trace tail
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
                  have nextCoherent : Coherent hash secretKey nextState
                      { transcript with hashCalls :=
                          transcript.hashCalls + 1 } := by
                    exact ⟨coherent.1,
                      by simpa only [GroupedBalancedWireTranscript67.responses]
                        using signedEq.trans coherent.2⟩
                  obtain ⟨signedTranscript, forgery, checkBudget,
                    checkRemaining, checkState, prefixLog, checkTrace,
                    prefixEq, checkSafe, checkCoherent, checkMember⟩ :=
                    ih (resume answer)
                      { transcript with hashCalls := transcript.hashCalls + 1 }
                      budget remaining nextState nextSafe nextCoherent
                      tailTrace tailMember
                  refine ⟨signedTranscript, forgery, checkBudget,
                    checkRemaining, checkState,
                    .publicHash input :: prefixLog, checkTrace,
                    ?_, checkSafe, checkCoherent, checkMember⟩
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
                    have finalIndex : final.residual input =
                        some indexAnswer :=
                      GroupedBalancedStoppedCacheMonotone67.execute_preserves
                        table
                        (eagerCutoffView answers cache
                          (ofInteract sizes GroupedBalancedWire67.wire
                            GroupedBalancedWire67.decode
                            GroupedBalancedWire67.decode adversary pk rounds
                            (resume (some wire)) updated) budget)
                        remaining (signed nextState index bottomAnswer)
                        final (some outcome, tailTrace) left
                        (by simpa only [signature, wire, updated]
                          using tailMember)
                        input indexAnswer
                        (by simpa only [GroupedBalancedGraphMonitorSignCompiler67.signed]
                          using present)
                    have hashIndex : hash input = indexAnswer :=
                      finalAgree finalIndex
                    have honestSignature : signature =
                        GroupedBalancedScheme67.sign hash secretKey
                          request.message := by
                      exact (signLaw request.message indexAnswer hashIndex).symm
                    have indexEq : Reference.indexOf hash request.message
                        signature.randomizer = index := by
                      change (hash input).extractLsb' 0 160 = index
                      rw [hashIndex]
                    have stateCoherent : Coherent hash secretKey nextState
                        transcript := ⟨coherent.1, signedEq.trans coherent.2⟩
                    have nextCoherent : Coherent hash secretKey
                        (signed nextState index bottomAnswer) updated := by
                      simpa only [updated, signature, wire,
                        GroupedBalancedWireTranscript67.afterSign] using
                        (GroupedBalancedOrganizerCoherence67.signed
                          hash secretKey nextState transcript request.message
                          signature index bottomAnswer stateCoherent
                          honestSignature indexEq)
                    obtain ⟨signedTranscript, forgery, checkBudget,
                      checkRemaining, checkState, prefixLog, checkTrace,
                      prefixEq, checkSafe, checkCoherent, checkMember⟩ :=
                      ih (resume (some wire)) updated budget remaining
                        (signed nextState index bottomAnswer)
                        nextSafe nextCoherent tailTrace
                        (by simpa only [signature, wire, updated]
                          using tailMember)
                    refine ⟨signedTranscript, forgery, checkBudget,
                      checkRemaining, checkState,
                      .privateHash :: .publicHash input :: prefixLog,
                      checkTrace, ?_, checkSafe, checkCoherent, checkMember⟩
                    rw [traceEq, prefixEq]
                    rfl
          · rw [if_neg allowed] at member
            simp only [eagerCutoffView, execute,
              support_pure, Set.mem_singleton_iff] at member
            cases member
            cases won

#print axioms winning_at_checker

end SigGolfCandidate.Hypertree.GroupedBalancedOrganizerCoherentChecker67
