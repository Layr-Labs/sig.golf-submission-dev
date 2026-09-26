import SigGolfCandidate.Hypertree.GroupedBalancedNonceExperiment67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedNonceTrack67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedNonceSafeProgram67. -/
section
/-! Exact relation between the passive nonce cache and signed-message audit
at public-query boundaries. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceTrack67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedIndexLabeledAudit67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

def Tracks (cache : SecurityNonceMonitor.NonceCache) (audit : Audit) : Prop :=
  ∀ message, cache message = none ↔ message ∉ audit.signedMessages

@[simp] theorem tracks_empty : Tracks ∅ {} := by
  intro message
  simp [Tracks]

theorem Tracks.public {cache : SecurityNonceMonitor.NonceCache}
    {audit : Audit} (tracked : Tracks cache audit)
    (pair : Message × Bytes 32) :
    Tracks cache (publicStep audit pair) := by
  intro message
  by_cases signed : pair.1 ∈ audit.signedMessages <;>
    simpa [publicStep, signed] using tracked message

theorem Tracks.sign {cache : SecurityNonceMonitor.NonceCache}
    {audit : Audit} (tracked : Tracks cache audit)
    (message : Message) (nonce : BitVec 256)
    (pair : Message × Bytes 32) (same : pair.1 = message) :
    Tracks (cache.cacheQuery message nonce) (signStep audit pair) := by
  intro other
  by_cases equal : other = message
  · subst other
    simp [signStep, same]
  · rw [QueryCache.cacheQuery_of_ne _ _ equal, tracked other]
    simp [signStep, same, equal]

theorem Tracks.doubleSign {cache : SecurityNonceMonitor.NonceCache}
    {audit : Audit} (tracked : Tracks cache audit)
    (message : Message) (nonce : BitVec 256)
    (pair : Message × Bytes 32) (same : pair.1 = message) :
    Tracks ((cache.cacheQuery message nonce).cacheQuery message nonce)
      (signStep audit pair) := by
  intro other
  by_cases equal : other = message
  · subst other
    simp [signStep, same]
  · rw [QueryCache.cacheQuery_of_ne _ _ equal,
      QueryCache.cacheQuery_of_ne _ _ equal, tracked other]
    simp [signStep, same, equal]

noncomputable def hits (nonces : SecurityGraphFactor.NonceTable)
    (audit : Audit) : Bool :=
  audit.nonceGuesses.any (fun pair => decide (nonces pair.1 = pair.2))

noncomputable def annotate {α : Type}
    (nonces : SecurityGraphFactor.NonceTable)
    (result : ((α × List GroupedBalancedIndexLabeledProgram67.Draw) × Audit)) :
    SecurityNonceProgram.Outcome
      ((α × List GroupedBalancedIndexLabeledProgram67.Draw) × Audit) :=
  ⟨result, hits nonces result.2, result.2.nonceGuesses.length⟩

noncomputable def accumulate {α : Type}
    (nonces : SecurityGraphFactor.NonceTable) (audit : Audit)
    (result : SecurityNonceProgram.Outcome α) :
    SecurityNonceProgram.Outcome α :=
  ⟨result.value, hits nonces audit || result.bad,
    audit.nonceGuesses.length + result.guesses⟩

@[simp] theorem accumulate_sign {α : Type}
    (nonces : SecurityGraphFactor.NonceTable) (audit : Audit)
    (pair : Message × Bytes 32)
    (result : SecurityNonceProgram.Outcome α) :
    accumulate nonces (signStep audit pair) result =
      accumulate nonces audit result := by
  rfl

theorem accumulate_sign_fun {α : Type}
    (nonces : SecurityGraphFactor.NonceTable) (audit : Audit)
    (pair : Message × Bytes 32) :
    accumulate (α := α) nonces (signStep audit pair) =
      accumulate nonces audit := by
  funext result
  exact accumulate_sign nonces audit pair result

theorem accumulate_draw_fun {α : Type}
    (nonces : SecurityGraphFactor.NonceTable) (audit : Audit)
    (input : Query) (mark : Bool) (answer : BitVec 256) :
    accumulate (α := α) nonces
      { audit with
        h5cache := audit.h5cache.cacheQuery input answer
        draws := audit.draws ++
          [(input, (mark, answer.extractLsb' 0 160))] } =
      accumulate nonces audit := by
  rfl

theorem Tracks.draw {cache : SecurityNonceMonitor.NonceCache}
    {audit : Audit} (tracked : Tracks cache audit)
    (input : Query) (mark : Bool) (answer : BitVec 256) :
    Tracks cache
      { audit with
        h5cache := audit.h5cache.cacheQuery input answer
        draws := audit.draws ++
          [(input, (mark, answer.extractLsb' 0 160))] } := by
  exact tracked

theorem accumulate_public {α : Type}
    (nonces : SecurityGraphFactor.NonceTable)
    (cache : SecurityNonceMonitor.NonceCache)
    (audit : Audit) (tracked : Tracks cache audit)
    (pair : Message × Bytes 32)
    (next : SecurityNonceProgram.Program α) :
    accumulate nonces audit <$>
      SecurityNonceProgram.run nonces cache
        (if pair.1 ∈ audit.signedMessages then next
          else .guess pair.1 pair.2 next) =
    accumulate nonces (publicStep audit pair) <$>
      SecurityNonceProgram.run nonces cache next := by
  by_cases signed : pair.1 ∈ audit.signedMessages
  · simp only [publicStep, if_pos signed]
  · have hidden : cache pair.1 = none := (tracked pair.1).2 signed
    simp only [if_neg signed, SecurityNonceProgram.run, hidden,
      decide_true, Bool.true_and, Functor.map_map]
    congr 1
    funext result
    simp only [accumulate, hits, publicStep, if_neg signed,
      List.any_cons, List.length_cons, SecurityNonceProgram.addGuess,
      Bool.true_and, ↓reduceIte]
    congr 1
    · simp only [Bool.or_assoc, Bool.or_comm]
    · omega

#print axioms Tracks.sign
#print axioms accumulate_public

end SigGolfCandidate.Hypertree.GroupedBalancedNonceTrack67

end

/-! A syntactic discipline for the short interval between obtaining a signer
randomizer and recording its H5 index query. No public query is possible in
that interval. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceSafeProgram67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedNonceProgram67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

mutual
  inductive Safe {α : Type} : Program α → Prop where
    | pure (value : α) : Safe (.pure value)
    | draw (input : Query) (mark : Bool)
        (next : BitVec 256 → Program α)
        (children : ∀ answer, Safe (next answer)) :
        Safe (.draw input mark next)
    | recordPublic (pair : Message × Bytes 32)
        (next : Program α) (child : Safe next) :
        Safe (.recordPublic pair next)
    | recordSign (pair : Message × Bytes 32)
        (next : Program α) (child : Safe next) :
        Safe (.recordSign pair next)
    | coin (n : Nat) (next : Fin (n + 1) → Program α)
        (children : ∀ answer, Safe (next answer)) :
        Safe (.coin n next)
    | nonce (message : Message)
        (next : BitVec 256 → Program α)
        (children : ∀ answer, Pending message (next answer)) :
        Safe (.nonce message next)

  inductive Pending {α : Type} : Message → Program α → Prop where
    | recordSign (message : Message) (pair : Message × Bytes 32)
        (same : pair.1 = message)
        (next : Program α) (child : Safe next) :
        Pending message (.recordSign pair next)
    | draw (message : Message) (input : Query) (mark : Bool)
        (next : BitVec 256 → Program α)
        (children : ∀ answer, Pending message (next answer)) :
        Pending message (.draw input mark next)
end

end SigGolfCandidate.Hypertree.GroupedBalancedNonceSafeProgram67
