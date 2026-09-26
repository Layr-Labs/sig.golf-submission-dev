import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledEagerHashHandoff67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledCheckerProgram67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAuditMonotone67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphOrganizerView67

/-! Every signed wire response in a completed organizer execution has a
corresponding message in the ghost H5 audit of that same execution. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledOrganizerTranscript67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphOrganizerView67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedIdealEagerCutoff67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledJoint67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false

def Covers (sizes : Sizes) (transcript : SigGolf.Transcript sizes)
    (audit : Audit) : Prop :=
  ∀ entry ∈ transcript.signed, entry.1 ∈ audit.signedMessages

theorem Covers.empty (sizes : Sizes) (audit : Audit) :
    Covers sizes {} audit := by
  intro entry member
  cases member

theorem Covers.mono (sizes : Sizes)
    (transcript : SigGolf.Transcript sizes)
    (audit audit' : Audit)
    (covered : Covers sizes transcript audit)
    (subset : audit.signedMessages ⊆ audit'.signedMessages) :
    Covers sizes transcript audit' := by
  intro entry member
  exact subset (covered entry member)

theorem Covers.hashStep (sizes : Sizes)
    (transcript : SigGolf.Transcript sizes)
    (audit audit' : Audit)
    (covered : Covers sizes transcript audit)
    (subset : audit.signedMessages ⊆ audit'.signedMessages) :
    Covers sizes { transcript with hashCalls := transcript.hashCalls + 1 }
      audit' := by
  exact Covers.mono sizes transcript audit audit' covered subset

theorem Covers.signStep (sizes : Sizes)
    (transcript : SigGolf.Transcript sizes)
    (audit audit' : Audit) (message : Message)
    (wire : Bytes sizes.signature)
    (covered : Covers sizes transcript audit)
    (subset : audit.signedMessages ⊆ audit'.signedMessages)
    (present : message ∈ audit'.signedMessages) :
    Covers sizes
      { transcript with
        signed := (message, wire) :: transcript.signed
        signingRequests := transcript.signingRequests + 1 } audit' := by
  intro entry member
  simp only [List.mem_cons] at member
  rcases member with same | old
  · simpa only [same] using present
  · exact subset (covered entry old)

theorem completed_covers (sizes : Sizes)
    (encode : GroupedBalancedScheme67.Signature → Bytes sizes.signature)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (answers : SecurityGraphIdeal.PrivateTable)
    (cache : QueryCache PointSpec) (table : PointTable)
    (pk : PublicKey) (adversary : SigGolf.Adversary sizes)
    (rounds : Nat) (adversaryState : adversary.State)
    (transcript : SigGolf.Transcript sizes)
    (budget secret remaining : Nat) (state : State) (calls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat)
    (audit : Audit) (covered : Covers sizes transcript audit)
    (result :
      (GroupedBalancedGraphIndexJoint67.JointOutcome
        ((Option (Result sizes) × List Action) × Nat) × List Draw) × Audit)
    (outcome : Result sizes) (trace : List Action) (secretOut : Nat)
    (member : result ∈ support (run
      (compile table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          (eagerCutoffView answers cache
            (ofInteract sizes encode decodeWitness decodeSignature
              adversary pk rounds adversaryState transcript) budget)
            secret)
        remaining state calls signedMessages bad tests) audit))
    (returned : result.1.1.value.value =
      some ((some outcome, trace), secretOut)) :
    Covers sizes outcome.transcript result.2 := by
  induction rounds generalizing adversaryState transcript budget secret
      remaining state calls signedMessages bad tests audit result outcome trace
      secretOut with
  | zero =>
      simp only [ofInteract, eagerCutoffView,
        GroupedBalancedGraphIndexJointClassTrace67.annotate,
        GroupedBalancedIndexLabeledJoint67.compile,
        GroupedBalancedIndexLabeledAudit67.run, support_pure,
        Set.mem_singleton_iff] at member
      subst result
      cases returned
      simpa only [Covers] using covered
  | succ rounds ih =>
      rw [ofInteract] at member
      cases action : adversary.step adversaryState with
      | submit forgery =>
          rw [action] at member
          have subset : audit.signedMessages ⊆ result.2.signedMessages :=
            GroupedBalancedIndexLabeledAuditMonotone67.run_signed_subset
              _ audit result member
          cases forgery with
          | witness message witness =>
              let signature := decodeWitness witness
              let finish := fun accepted : Bool =>
                (⟨accepted && transcript.freshMessage message,
                  some (message, signature), transcript⟩ : Result sizes)
              have checked : result ∈ support (run
                  (compile table
                    (GroupedBalancedGraphIndexJointClassTrace67.annotate
                      (eagerCutoffView answers cache
                        (GroupedBalancedGraphInteractionGame67.ofHash
                          (GroupedBalancedVerifyOracle67.verify pk message signature)
                          (fun accepted => .done (finish accepted))) budget)
                      secret)
                    remaining state calls signedMessages bad tests) audit) := by
                simpa only [ofCheck, signature, finish] using member
              obtain ⟨accepted, outcomeEq⟩ :=
                GroupedBalancedIndexLabeledCheckerProgram67.checker_return
                  (GroupedBalancedVerifyOracle67.verify pk message signature)
                  finish answers table cache budget secret remaining state
                  calls signedMessages bad tests audit result outcome trace
                  secretOut checked returned
              simpa only [outcomeEq, finish] using
                (Covers.mono sizes transcript audit result.2 covered subset)
          | signature message wire =>
              let signature := decodeSignature wire
              let finish := fun accepted : Bool =>
                (⟨accepted && transcript.freshSignature message wire,
                  some (message, signature), transcript⟩ : Result sizes)
              have checked : result ∈ support (run
                  (compile table
                    (GroupedBalancedGraphIndexJointClassTrace67.annotate
                      (eagerCutoffView answers cache
                        (GroupedBalancedGraphInteractionGame67.ofHash
                          (GroupedBalancedVerifyOracle67.verify pk message signature)
                          (fun accepted => .done (finish accepted))) budget)
                      secret)
                    remaining state calls signedMessages bad tests) audit) := by
                simpa only [ofCheck, signature, finish] using member
              obtain ⟨accepted, outcomeEq⟩ :=
                GroupedBalancedIndexLabeledCheckerProgram67.checker_return
                  (GroupedBalancedVerifyOracle67.verify pk message signature)
                  finish answers table cache budget secret remaining state
                  calls signedMessages bad tests audit result outcome trace
                  secretOut checked returned
              simpa only [outcomeEq, finish] using
                (Covers.mono sizes transcript audit result.2 covered subset)
      | step nextState =>
          rw [action] at member
          exact ih nextState transcript budget secret remaining state calls
            signedMessages bad tests audit covered result outcome trace
            secretOut member returned
      | sample n resume =>
          rw [action] at member
          simp only [eagerCutoffView,
            GroupedBalancedGraphIndexJointClassTrace67.annotate,
            GroupedBalancedIndexLabeledJoint67.compile,
            GroupedBalancedIndexLabeledAudit67.run,
            mem_support_bind_iff] at member
          obtain ⟨answer, _, child⟩ := member
          exact ih (resume answer) transcript budget secret remaining state
            calls signedMessages bad tests audit covered result outcome trace
            secretOut child returned
      | hash input resume =>
          rw [action] at member
          cases budget with
          | zero =>
              simp only [eagerCutoffView,
                GroupedBalancedGraphIndexJointClassTrace67.annotate,
                GroupedBalancedIndexLabeledJoint67.compile,
                GroupedBalancedIndexLabeledAudit67.run,
                support_pure, Set.mem_singleton_iff] at member
              subst result
              cases returned
          | succ budget =>
              cases remaining with
              | zero =>
                  simp only [eagerCutoffView,
                    GroupedBalancedGraphIndexJointClassTrace67.annotate,
                    GroupedBalancedIndexLabeledJoint67.compile,
                    GroupedBalancedIndexLabeledAudit67.run,
                    support_pure, Set.mem_singleton_iff] at member
                  subst result
                  cases returned
              | succ remaining =>
                  let updatedTranscript : SigGolf.Transcript sizes :=
                    { transcript with hashCalls := transcript.hashCalls + 1 }
                  change result ∈ support (run
                    (compile table
                      (GroupedBalancedGraphIndexJointClassTrace67.annotate
                        (eagerCutoffView answers cache
                          (.hash input (fun answer =>
                            ofInteract sizes encode decodeWitness
                              decodeSignature adversary pk rounds
                              (resume answer) updatedTranscript))
                          (budget + 1)) secret)
                      (remaining + 1) state calls signedMessages bad tests)
                    audit) at member
                  generalize hContinuation :
                    (fun answer => ofInteract sizes encode decodeWitness
                      decodeSignature adversary pk rounds (resume answer)
                      updatedTranscript) = continuation at member
                  generalize hHashView : eagerCutoffView answers cache
                    (.hash input continuation) (budget + 1) = hashView
                    at member
                  obtain ⟨answer, updated, calls', bad', tests', nextAudit,
                      tail, tailTrace, tailMember, subset, auditEq,
                      tailValue⟩ :=
                    GroupedBalancedIndexLabeledEagerHashHandoff67.eager_hash_handoff_view
                      answers cache table input continuation budget secret
                      remaining hashView hHashView.symm
                      state calls signedMessages bad tests audit
                      result outcome trace secretOut member returned
                  rw [← hContinuation] at tailMember
                  have nextCovered : Covers sizes updatedTranscript nextAudit :=
                    Covers.hashStep sizes transcript audit nextAudit covered
                      subset
                  have tailCovered := ih (resume answer) updatedTranscript
                    budget (secret +
                      GroupedBalancedGraphIndexJointClassTrace67.secretCharge input)
                    remaining updated calls' signedMessages bad' tests'
                    nextAudit nextCovered tail outcome tailTrace secretOut
                    tailMember tailValue
                  simpa only [auditEq] using tailCovered
      | sign request resume =>
          rw [action] at member
          simp only [] at member
          by_cases allowed : transcript.signingRequests < LIFETIME
          · rw [if_pos allowed] at member
            cases budget with
            | zero =>
                simp only [eagerCutoffView,
                  GroupedBalancedGraphIndexJointClassTrace67.annotate,
                  GroupedBalancedIndexLabeledJoint67.compile,
                  GroupedBalancedIndexLabeledAudit67.run,
                  support_pure, Set.mem_singleton_iff] at member
                subst result
                cases returned
            | succ budget =>
                cases budget with
                | zero =>
                    simp only [eagerCutoffView,
                      GroupedBalancedGraphIndexJointClassTrace67.annotate,
                      GroupedBalancedIndexLabeledJoint67.compile,
                      GroupedBalancedIndexLabeledAudit67.run,
                      support_pure, Set.mem_singleton_iff] at member
                    subst result
                    cases returned
                | succ budget =>
                    let updatedTranscript :=
                      fun signature : GroupedBalancedScheme67.Signature =>
                        { transcript with
                          signed := (request.message, encode signature) ::
                            transcript.signed
                          signingRequests := transcript.signingRequests + 1 }
                    change result ∈ support (run
                      (compile table
                        (GroupedBalancedGraphIndexJointClassTrace67.annotate
                          (eagerCutoffView answers cache
                            (.sign request.message (fun signature =>
                              ofInteract sizes encode decodeWitness
                                decodeSignature adversary pk rounds
                                (resume (some (encode signature)))
                                (updatedTranscript signature)))
                            (budget + 2)) secret)
                        remaining state calls signedMessages bad tests)
                      audit) at member
                    generalize hContinuation :
                      (fun signature =>
                        ofInteract sizes encode decodeWitness
                          decodeSignature adversary pk rounds
                          (resume (some (encode signature)))
                          (updatedTranscript signature)) = continuation
                      at member
                    generalize hSignView : eagerCutoffView answers cache
                      (.sign request.message continuation) (budget + 2) =
                      signView at member
                    obtain ⟨indexAnswer, residual, nextAudit,
                        tail, tailTrace, tailMember, signedEq,
                        present, auditEq, tailValue⟩ :=
                      GroupedBalancedIndexLabeledEagerSignHandoff67.eager_sign_handoff_view
                        answers cache table request.message continuation
                        budget secret remaining signView hSignView.symm
                        state calls signedMessages bad tests audit result
                        outcome trace secretOut member returned
                    rw [← hContinuation] at tailMember
                    let index : BitVec 160 := indexAnswer.extractLsb' 0 160
                    let randomizer := answers (.randomizer request.message)
                    let signature :=
                      GroupedBalancedGraphHonestSignView67.signatureFromAnswers
                        cache randomizer index (table (.inr (.inl index)))
                    have subset : audit.signedMessages ⊆
                        nextAudit.signedMessages := by
                      rw [signedEq]
                      exact Finset.subset_insert _ _
                    have nextCovered : Covers sizes
                        (updatedTranscript signature) nextAudit :=
                      Covers.signStep sizes transcript audit nextAudit
                        request.message (encode signature) covered subset
                        present
                    have tailCovered := ih (resume (some (encode signature)))
                      (updatedTranscript signature) budget secret remaining
                      (signed { state with residual := residual } index
                        (table (.inr (.inl index)))) calls
                      (insert request.message signedMessages) bad tests
                      nextAudit nextCovered tail outcome tailTrace secretOut
                      tailMember tailValue
                    simpa only [auditEq] using tailCovered
          · rw [if_neg allowed] at member
            simp only [eagerCutoffView,
              GroupedBalancedGraphIndexJointClassTrace67.annotate,
              GroupedBalancedIndexLabeledJoint67.compile,
              GroupedBalancedIndexLabeledAudit67.run,
              support_pure, Set.mem_singleton_iff] at member
            subst result
            cases returned
            simpa only [Covers] using covered

#print axioms Covers.signStep
#print axioms completed_covers

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledOrganizerTranscript67
