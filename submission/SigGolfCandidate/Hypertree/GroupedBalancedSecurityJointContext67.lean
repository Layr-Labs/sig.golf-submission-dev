import SigGolfCandidate.Hypertree.GroupedBalancedSecurityJointPhases67
import SigGolfCandidate.Hypertree.SecurityBytecodeCoupling

/-! Contextual replacement of the actual keygen and signer HashSpec programs
inside any adaptive lazy-oracle continuation, after joint source/graph
presampling. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityJointContext67
open SigGolf OracleComp OracleSpec Reference SecurityCache SecurityGraphHidden
open GroupedBalancedPrivateFactors67 GroupedBalancedSecurityGraph67
open GroupedBalancedSecurityJointPresample67
open GroupedBalancedSecurityJointTable67
open GroupedBalancedSecuritySourceHybrid67
open scoped Classical
set_option maxRecDepth 8192

private abbrev submission := GroupedBalancedProgram67ByteSign.submission

def Known (secretKey : SecretKey) (answers : PrivateTable)
    (labels : Labels) (cache : QueryCache HashSpec) : Prop :=
  ∀ hash : Hash, cache.AgreesWithFn hash →
    (jointCache secretKey answers labels).AgreesWithFn hash

theorem known_initial (secretKey : SecretKey)
    (answers : PrivateTable) (labels : Labels) :
    Known secretKey answers labels (jointCache secretKey answers labels) := by
  intro hash agree
  exact agree

def semanticKeygen (answers : PrivateTable) (labels : Labels)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable) :
    OracleComp HashSpec (Option (PublicKey × Cache) × Nat) :=
  pure (some (GroupedBalancedGraphMonitorSetupBound67.rootPublic
    (tableOf answers labels ghosts), (0 : Cache)),3983)

noncomputable def semanticSign (secretKey : SecretKey)
    (table : GroupedBalancedGraphPassive67.PointTable)
    (request : SigningRequest) :
    OracleComp HashSpec (Option (Bytes submission.sizes.signature) × Nat) := do
  let randomizer ← HashSpec.query
    (SecurityRandomOracle.randomizerInput secretKey request.message)
  let indexAnswer ← HashSpec.query
    (SecurityRandomOracle.indexInput request.message randomizer)
  let index : BitVec 160 := indexAnswer.extractLsb' 0 160
  pure (some (GroupedBalancedWire67.wire
    (GroupedBalancedGraphHonestSignView67.signatureFromAnswers
      (GroupedBalancedGraphMonitorSetup67.cache table) randomizer index
      (table (.inr (.inl index))))),122548)

theorem keygen_fixed (secretKey : SecretKey)
    (answers : PrivateTable) (labels : Labels)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable) (hash : Hash)
    (agree : (jointCache secretKey answers labels).AgreesWithFn hash) :
    evalWithAnswerFn hash
      (GroupedBalancedSecurityObservedPhases67.view <$>
        submission.run .keygen secretKey) =
      evalWithAnswerFn hash (semanticKeygen answers labels ghosts) := by
  simpa only [semanticKeygen, evalWithAnswerFn_pure] using
    GroupedBalancedSecurityJointPhases67.machine_keygen_of_joint
      secretKey answers labels ghosts hash agree

theorem sign_fixed (secretKey : SecretKey)
    (answers : PrivateTable) (labels : Labels)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable)
    (hash : Hash)
    (agree : (jointCache secretKey answers labels).AgreesWithFn hash)
    (request : SigningRequest) :
    evalWithAnswerFn hash
      (GroupedBalancedSecurityObservedPhases67.view <$>
        submission.signingOracle secretKey request) =
      evalWithAnswerFn hash
        (semanticSign secretKey (tableOf answers labels ghosts) request) := by
  have phase := GroupedBalancedSecurityJointPhases67.machine_sign_of_joint
    secretKey answers labels ghosts hash agree request
  calc
    _ = (some (GroupedBalancedWire67.wire
          (GroupedBalancedGraphHonestSignView67.signatureFromAnswers
            (GroupedBalancedGraphMonitorSetup67.cache
              (tableOf answers labels ghosts))
            (hash (SecurityRandomOracle.randomizerInput secretKey request.message))
            ((hash (SecurityRandomOracle.indexInput request.message
              (hash (SecurityRandomOracle.randomizerInput secretKey request.message)))).extractLsb' 0 160)
            ((tableOf answers labels ghosts) (.inr (.inl
              ((hash (SecurityRandomOracle.indexInput request.message
                (hash (SecurityRandomOracle.randomizerInput secretKey request.message)))).extractLsb' 0 160)))))),122548) := phase
    _ = _ := by
      simp only [semanticSign,evalWithAnswerFn_bind,evalWithAnswerFn_pure]
      rfl

/-- The keygen machine can be replaced by a pure known organizer result inside
any adaptive continuation. The 3983 charged calls remain in that result. -/
theorem keygen_context {β : Type}
    (secretKey : SecretKey) (answers : PrivateTable) (labels : Labels)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable)
    (cache : QueryCache HashSpec)
    (known : Known secretKey answers labels cache)
    (next : (Option (PublicKey × Cache) × Nat) → OracleComp World β) :
    𝒮[observe
      ((GroupedBalancedSecurityObservedPhases67.view <$>
        submission.run .keygen secretKey).liftComp World >>= next) cache] =
    𝒮[observe
      ((semanticKeygen answers labels ghosts).liftComp World >>= next) cache] := by
  exact SecurityBytecode.contextual_equivalence_at _ _ next cache
    (fun hash agree => keygen_fixed secretKey answers labels ghosts hash (known hash agree))

/-- The signer machine can be replaced by its H6/H5 graph-view program in any
adaptive continuation. The exact 122548 charged calls remain in its result. -/
theorem sign_context {β : Type}
    (secretKey : SecretKey) (answers : PrivateTable) (labels : Labels)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable)
    (cache : QueryCache HashSpec)
    (known : Known secretKey answers labels cache)
    (request : SigningRequest)
    (next : (Option (Bytes submission.sizes.signature) × Nat) → OracleComp World β) :
    𝒮[observe
      ((GroupedBalancedSecurityObservedPhases67.view <$>
        submission.signingOracle secretKey request).liftComp World >>= next) cache] =
    𝒮[observe
      ((semanticSign secretKey (tableOf answers labels ghosts) request).liftComp World >>=
        next) cache] := by
  exact SecurityBytecode.contextual_equivalence_at _ _ next cache
    (fun hash agree => sign_fixed secretKey answers labels ghosts hash
      (known hash agree) request)

#print axioms keygen_context
#print axioms sign_context

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityJointContext67
