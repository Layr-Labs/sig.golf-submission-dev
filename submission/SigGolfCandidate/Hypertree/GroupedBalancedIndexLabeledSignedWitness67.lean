import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCompiler67


/-! The sampled labelled experiment retains prereveal nonce coverage. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceGlobal67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledNonceCovered67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option linter.constructorNameAsVariable false
open scoped Classical

theorem global_nonce_covered {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledGlobal67.global view remaining) {}),
      NonceCovered result.2 := by
  intro result member
  rw [GroupedBalancedIndexLabeledGlobal67.global,
    GroupedBalancedIndexLabeledAuditLift67.run_unmarked,
    mem_support_bind_iff] at member
  obtain ⟨table, _, child⟩ := member
  exact GroupedBalancedIndexLabeledNonceCompiler67.start_nonce_covered
    table view remaining result child

theorem audited_nonce_covered {α : Type}
    (interaction : QueryCache PointSpec →
      GroupedBalancedGraphInteraction67.Interaction α)
    (budget : Nat) :
    ∀ result ∈ support
      (GroupedBalancedIndexLabeledAudit67.auditedAnnotatedGlobal
        interaction budget),
      NonceCovered result.2 := by
  intro result member
  unfold GroupedBalancedIndexLabeledAudit67.auditedAnnotatedGlobal at member
  simp only [mem_support_bind_iff] at member
  obtain ⟨answers, _, child⟩ := member
  exact global_nonce_covered _ budget result child

theorem audited_first_sign_hit {α : Type}
    (interaction : QueryCache PointSpec →
      GroupedBalancedGraphInteraction67.Interaction α)
    (budget : Nat)
    (result : ((GroupedBalancedGraphIndexJoint67.JointOutcome
      ((Option α × List GroupedBalancedGameQueryTrace67.Action) × Nat) ×
      List GroupedBalancedIndexLabeledProgram67.Draw) × Audit))
    (member : result ∈ support
      (GroupedBalancedIndexLabeledAudit67.auditedAnnotatedGlobal
        interaction budget))
    (message : Message) (nonce : Bytes 32)
    (unsigned : message ∉ result.2.signedMessages)
    (present : result.2.h5cache
      (SecurityRandomOracle.indexInput message nonce) ≠ none) :
    (message, nonce) ∈ result.2.nonceGuesses :=
  firstSignHit result.2 (audited_nonce_covered interaction budget result member)
    message nonce unsigned present

#print axioms global_nonce_covered
#print axioms audited_nonce_covered
#print axioms audited_first_sign_hit

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceGlobal67


/-! A first signer occurrence leaves either a prereveal nonce guess or a
marked H5 draw. The statement uses parsed signer pairs and does not yet
identify their nonces with the sampled private nonce table. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledSignedWitness67
open SigGolf OracleComp OracleSpec Reference SecurityRandomOracle
open GroupedBalancedIndexLabeledAudit67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

def SignedWitness (audit : Audit) : Prop :=
  ∀ pair ∈ audit.signedPairs,
    pair ∈ audit.nonceGuesses ∨
      ∃ index : BitVec 160,
        (indexInput pair.1 pair.2, (true, index)) ∈ audit.draws

theorem empty : SignedWitness {} := by
  intro pair member
  cases member

theorem publicStep (audit : Audit) (pair : Message × Bytes 32)
    (witness : SignedWitness audit) :
    SignedWitness (GroupedBalancedIndexLabeledAudit67.publicStep audit pair) := by
  intro earlier member
  by_cases signed : pair.1 ∈ audit.signedMessages
  · simpa [GroupedBalancedIndexLabeledAudit67.publicStep, signed]
      using witness earlier (by simpa
        [GroupedBalancedIndexLabeledAudit67.publicStep, signed] using member)
  · have old : earlier ∈ audit.signedPairs := by
      simpa [GroupedBalancedIndexLabeledAudit67.publicStep, signed] using member
    rcases witness earlier old with guess | marked
    · exact Or.inl (by simp
        [GroupedBalancedIndexLabeledAudit67.publicStep, signed, guess])
    · exact Or.inr (by simpa
        [GroupedBalancedIndexLabeledAudit67.publicStep, signed] using marked)

theorem drawStep (audit : Audit) (input : Query) (mark : Bool)
    (answer : BitVec 256) (witness : SignedWitness audit) :
    SignedWitness
      { audit with
        h5cache := audit.h5cache.cacheQuery input answer
        draws := audit.draws ++
          [(input, (mark, answer.extractLsb' 0 160))] } := by
  intro pair member
  rcases witness pair member with guess | ⟨index, marked⟩
  · exact Or.inl guess
  · exact Or.inr ⟨index, List.mem_append_left _ marked⟩

theorem signStep (audit : Audit) (pair : Message × Bytes 32)
    (witness : SignedWitness audit)
    (known : pair ∈ audit.nonceGuesses ∨
      ∃ index : BitVec 160,
        (indexInput pair.1 pair.2, (true, index)) ∈ audit.draws) :
    SignedWitness (GroupedBalancedIndexLabeledAudit67.signStep audit pair) := by
  intro earlier member
  by_cases signed : pair.1 ∈ audit.signedMessages
  · have old : earlier ∈ audit.signedPairs := by
      simpa [GroupedBalancedIndexLabeledAudit67.signStep, signed] using member
    simpa [GroupedBalancedIndexLabeledAudit67.signStep, signed]
      using witness earlier old
  · have split : earlier = pair ∨ earlier ∈ audit.signedPairs := by
      simpa [GroupedBalancedIndexLabeledAudit67.signStep, signed] using member
    rcases split with same | old
    · subst earlier
      simpa [GroupedBalancedIndexLabeledAudit67.signStep, signed] using known
    · simpa [GroupedBalancedIndexLabeledAudit67.signStep, signed]
        using witness earlier old

theorem signStep_repeat (audit : Audit) (pair : Message × Bytes 32)
    (witness : SignedWitness audit)
    (signed : pair.1 ∈ audit.signedMessages) :
    SignedWitness (GroupedBalancedIndexLabeledAudit67.signStep audit pair) := by
  simpa [SignedWitness, GroupedBalancedIndexLabeledAudit67.signStep,
    signed] using witness

theorem first_pair (audit : Audit) (witness : SignedWitness audit)
    (pair : Message × Bytes 32) (member : pair ∈ audit.signedPairs) :
    pair ∈ audit.nonceGuesses ∨
      ∃ index : BitVec 160,
        (indexInput pair.1 pair.2, (true, index)) ∈ audit.draws :=
  witness pair member

#print axioms publicStep
#print axioms drawStep
#print axioms signStep

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledSignedWitness67
