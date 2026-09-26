import SigGolfCandidate.Hypertree.GroupedBalancedSecuritySourceHybrid67
import SigGolfCandidate.Hypertree.GroupedBalancedSecurityProgrammedKeygen67
import SigGolfCandidate.Hypertree.GroupedBalancedSecurityProgrammedSign67

/-! Concrete direct67 machine phases under a total hash extending the jointly
sampled private source cache. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityJointPhases67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedPrivateDerivation67 GroupedBalancedPrivateFactors67
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedSecurityJointPresample67
open GroupedBalancedSecurityJointTable67
open GroupedBalancedSecuritySourceHybrid67
open GroupedBalancedGraphProgrammedReference67
open scoped Classical
set_option maxRecDepth 8192

private abbrev submission := GroupedBalancedProgram67ByteSign.submission

theorem source_answers (secretKey : SecretKey)
    (answers : PrivateTable) (residual : Hash)
    (agree : (sourceCache secretKey answers).AgreesWithFn residual) :
    GroupedBalancedGraphReference67.sourceAnswers residual secretKey =
      privateOfAnswers answers := by
  unfold GroupedBalancedGraphReference67.sourceAnswers privateOfAnswers
  congr 1
  · funext index
    change residual (input secretKey (.bottom index)) = answers (.bottom index)
    exact agree (source_cache_lookup secretKey answers (.bottom index) trivial)
  · funext base leaf pair
    change residual (input secretKey (.upper base leaf pair)) =
      answers (.upper base leaf pair)
    exact agree (source_cache_lookup secretKey answers (.upper base leaf pair) trivial)

theorem source_answers_of_joint (secretKey : SecretKey)
    (answers : PrivateTable) (labels : Labels) (hash : Hash)
    (agree : (jointCache secretKey answers labels).AgreesWithFn hash) :
    GroupedBalancedGraphReference67.sourceAnswers hash secretKey =
      privateOfAnswers answers := by
  unfold GroupedBalancedGraphReference67.sourceAnswers privateOfAnswers
  congr 1
  · funext index
    change hash (input secretKey (.bottom index)) = answers (.bottom index)
    exact agree (joint_source_lookup secretKey answers labels
      (.bottom index) trivial)
  · funext base leaf pair
    change hash (input secretKey (.upper base leaf pair)) =
      answers (.upper base leaf pair)
    exact agree (joint_source_lookup secretKey answers labels
      (.upper base leaf pair) trivial)

theorem joint_hash_fixed_point (secretKey : SecretKey)
    (answers : PrivateTable) (labels : Labels) (hash : Hash)
    (agree : (jointCache secretKey answers labels).AgreesWithFn hash) :
    hash = programmedGrouped hash secretKey labels := by
  have sourceEq := source_answers_of_joint secretKey answers labels hash agree
  funext query
  unfold programmedGrouped
  rw [sourceEq]
  rw [GroupedBalancedGraphOracle67.programmed_hash]
  cases canonical : GroupedBalancedGraphOracle67.canonical
      (privateOfAnswers answers) labels query with
  | none => rfl
  | some value =>
      have cached : jointCache secretKey answers labels query = some value := by
        change GroupedBalancedGraphOracle67.embed
          (privateOfAnswers answers) labels
          (sourceCache secretKey answers) query = some value
        rw [GroupedBalancedGraphOracle67.embed_lookup, canonical]
      exact agree cached

theorem machine_keygen (secretKey : SecretKey)
    (answers : PrivateTable) (labels : Labels)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable)
    (residual : Hash) :
    evalWithAnswerFn (programmedGrouped residual secretKey labels)
      (GroupedBalancedSecurityObservedPhases67.view <$>
        submission.run .keygen secretKey) =
      (some (GroupedBalancedGraphMonitorSetupBound67.rootPublic
        (tableOf answers labels ghosts), (0 : Cache)),3983) := by
  rw [← labelsOf_tableOf answers labels ghosts]
  exact GroupedBalancedSecurityProgrammedKeygen67.table_root residual secretKey
    (tableOf answers labels ghosts)

theorem machine_sign (secretKey : SecretKey)
    (answers : PrivateTable) (labels : Labels)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable)
    (residual : Hash)
    (agree : (sourceCache secretKey answers).AgreesWithFn residual)
    (request : SigningRequest) :
    let table := tableOf answers labels ghosts
    let hash := programmedGrouped residual secretKey labels
    let randomizer := residual
      (SecurityRandomOracle.randomizerInput secretKey request.message)
    let indexAnswer := residual
      (SecurityRandomOracle.indexInput request.message randomizer)
    let index : BitVec 160 := indexAnswer.extractLsb' 0 160
    evalWithAnswerFn hash (GroupedBalancedSecurityObservedPhases67.view <$>
      submission.signingOracle secretKey request) =
      (some (GroupedBalancedWire67.wire
        (GroupedBalancedGraphHonestSignView67.signatureFromAnswers
          (GroupedBalancedGraphMonitorSetup67.cache table) randomizer index
          (table (.inr (.inl index))))),122548) := by
  dsimp only
  apply GroupedBalancedSecurityProgrammedSign67.graph_signature residual
    secretKey labels (tableOf answers labels ghosts)
  · exact (labelsOf_tableOf answers labels ghosts).symm
  · intro index
    rw [source_answers secretKey answers residual agree]
    exact (bottom_tableOf answers labels ghosts index).symm
  · intro base leaf chain
    rw [source_answers secretKey answers residual agree]
    exact (source_tableOf answers labels ghosts base leaf chain).symm

/-- The keygen machine observation is valid for every completion of the
actual joint lazy-oracle cache, without assuming a separate planted hash. -/
theorem machine_keygen_of_joint (secretKey : SecretKey)
    (answers : PrivateTable) (labels : Labels)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable)
    (hash : Hash)
    (agree : (jointCache secretKey answers labels).AgreesWithFn hash) :
    evalWithAnswerFn hash
      (GroupedBalancedSecurityObservedPhases67.view <$>
        submission.run .keygen secretKey) =
      (some (GroupedBalancedGraphMonitorSetupBound67.rootPublic
        (tableOf answers labels ghosts), (0 : Cache)),3983) := by
  have fixed := joint_hash_fixed_point secretKey answers labels hash agree
  rw [fixed]
  exact machine_keygen secretKey answers labels ghosts hash

/-- The signer machine observation uses the same sampled source table and
retains its exact 122548 hash-call count for an arbitrary attacker cache. -/
theorem machine_sign_of_joint (secretKey : SecretKey)
    (answers : PrivateTable) (labels : Labels)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable)
    (hash : Hash)
    (agree : (jointCache secretKey answers labels).AgreesWithFn hash)
    (request : SigningRequest) :
    let table := tableOf answers labels ghosts
    let randomizer := hash
      (SecurityRandomOracle.randomizerInput secretKey request.message)
    let indexAnswer := hash
      (SecurityRandomOracle.indexInput request.message randomizer)
    let index : BitVec 160 := indexAnswer.extractLsb' 0 160
    evalWithAnswerFn hash (GroupedBalancedSecurityObservedPhases67.view <$>
      submission.signingOracle secretKey request) =
      (some (GroupedBalancedWire67.wire
        (GroupedBalancedGraphHonestSignView67.signatureFromAnswers
          (GroupedBalancedGraphMonitorSetup67.cache table) randomizer index
          (table (.inr (.inl index))))),122548) := by
  dsimp only
  have sourceEq := source_answers_of_joint secretKey answers labels hash agree
  have fixed := joint_hash_fixed_point secretKey answers labels hash agree
  have phase := GroupedBalancedSecurityProgrammedSign67.graph_signature
    hash secretKey labels (tableOf answers labels ghosts)
    (labelsOf_tableOf answers labels ghosts).symm
    (by intro index
        rw [sourceEq]
        exact (bottom_tableOf answers labels ghosts index).symm)
    (by intro base leaf chain
        rw [sourceEq]
        exact (source_tableOf answers labels ghosts base leaf chain).symm)
    request
  rw [← fixed] at phase
  exact phase

#print axioms source_answers
#print axioms joint_hash_fixed_point
#print axioms machine_keygen
#print axioms machine_sign
#print axioms machine_keygen_of_joint
#print axioms machine_sign_of_joint

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityJointPhases67
