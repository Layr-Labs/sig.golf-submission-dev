import SigGolfCandidate.Hypertree.SecurityAtomicCounts
import SigGolfCandidate.Hypertree.SecurityExperiment
import SigGolfCandidate.Hypertree.SecurityAtomicCutoffRun

/-! Inlined from SigGolfCandidate.Hypertree.SecurityAtomicCountsSign; its only importer was SigGolfCandidate.Hypertree.SecurityExperimentAtomic. -/
section
namespace SigGolfCandidate.Hypertree.SecurityAtomicCounts
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGameHop SecurityAtomicCutoff
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- The digit split changes intermediate values but never the total seven-step
chain work, on every independent answer history. -/
theorem signChain (address : ChainAddress) (message : Digest) :
    Queries (SecurityIdealSign.signChain address message) 8 := by
  have all : Queries (SecurityIdealSign.signChain address message)
      (1 + ((digit message address.chain).val + (7 - (digit message address.chain).val))) := by
    unfold SecurityIdealSign.signChain
    simpa only [map_eq_pure_bind] using
      (secret address).bind _ (fun value =>
        (publicCall (walk _ 0 (digit message address.chain).val value
          (chainHash address.level.val address.tree.toNat address.side address.chain))).bind _
          (fun fragment => (publicCall (walk _ (digit message address.chain).val
            (7 - (digit message address.chain).val) fragment
            (chainHash address.level.val address.tree.toNat address.side address.chain))).map
              (fun last => (fragment, last))))
  have digitBound := (digit message address.chain).isLt
  have total : 1 + ((digit message address.chain).val + (7 - (digit message address.chain).val)) = 8 := by omega
  rw [total] at all
  exact all

private theorem nodeChoice (level tree : Nat) (side : Bool) (sibling current : Digest) :
    Queries (if side then SecurityReference.node level tree sibling current
      else SecurityReference.node level tree current sibling) 1 := by
  cases side <;> exact node _ _ _ _

theorem signLayerWithRoot (level : Fin 160) (tree : BitVec 192) (side : Bool) (message : Digest) :
    Queries (SecurityIdealSign.signLayerWithRoot level tree side message)
      (if level.val = 0 then 5 else 739) := by
  by_cases bottom : level.val = 0
  · have sibling : Queries (SecurityIdealKeygen.leafRoot level tree (!side)) 2 := by
      simpa only [if_pos bottom] using leafRoot level tree (!side)
    simp only [SecurityIdealSign.signLayerWithRoot, if_pos bottom]
    simpa only [map_eq_pure_bind] using
      (secret ⟨level, tree, side, 0⟩).bind _ (fun fragment =>
        (publicCall (chainHash level.val tree.toNat side 0 0 fragment)).bind _ (fun current =>
          sibling.bind _ (fun sibling => (publicCall (nodeChoice level.val tree.toNat side sibling current)).map
            (fun root => ((⟨fun i => if i = 0 then fragment else 0, sibling⟩ : LayerSignature), root)))))
  · have sibling : Queries (SecurityIdealKeygen.leafRoot level tree (!side)) 369 := by
      simpa only [if_neg bottom] using leafRoot level tree (!side)
    simp only [SecurityIdealSign.signLayerWithRoot, if_neg bottom]
    simpa only [map_eq_pure_bind] using
      (sequenceFin 46 8 _ (fun chain => signChain ⟨level, tree, side, chain⟩ message)).bind _ (fun chains =>
        (publicCall (compressLeaf level.val tree.toNat side (fun i => (chains i).2))).bind _ (fun current =>
          sibling.bind _ (fun sibling => (publicCall (nodeChoice level.val tree.toNat side sibling current)).map
            (fun root => ((⟨fun i => (chains i).1, sibling⟩ : LayerSignature), root)))))

theorem signUpper (count level index : Nat) (hl : count + level ≤ 160) (hi : index < 2 ^ 192)
    (message : Digest) (positive : 0 < level) :
    Queries (SecurityIdealSign.signUpper count level index hl hi message) (739 * count) := by
  induction count generalizing level index message with
  | zero => exact Queries.pure _
  | succ count ih =>
    have first : Queries (SecurityIdealSign.signLayerWithRoot ⟨level, by omega⟩
        (BitVec.ofNat 192 (index / 2)) (index % 2 == 1) message) 739 := by
      simpa only [if_neg (by omega : level ≠ 0)] using
        signLayerWithRoot ⟨level, by omega⟩ (BitVec.ofNat 192 (index / 2)) (index % 2 == 1) message
    simpa only [SecurityIdealSign.signUpper, Nat.mul_succ, Nat.add_comm, map_eq_pure_bind] using
      first.bind _ (fun layer =>
        (ih (level + 1) (index / 2) (by omega) (lt_of_le_of_lt (Nat.div_le_self ..) hi) layer.2 (by omega)).map
          (fun rest => layer.1 :: rest))

theorem randomizer (message : Message) : Queries (SecurityIdealSign.randomizer message) 1 := by
  change Queries (liftM (SplitWorld.query (.inl (.randomizer message)))) 1
  exact Queries.ask (spec := SplitWorld) _

theorem randomizedIndex (message : Message) :
    Queries (SecurityIdealSign.randomizedIndex message) 2 := by
  unfold SecurityIdealSign.randomizedIndex
  simpa only [map_eq_pure_bind] using
    (randomizer message).bind _ (fun nonce =>
      (publicCall (Queries.ask (spec := HashSpec) (SecurityRandomOracle.indexInput message nonce))).map
        (fun answer => (nonce, answer.extractLsb' 0 160)))

/-- Full ideal signer query shape is constant for every possible oracle history,
not only answers induced by a consistent function or secretKeyed oracle. -/
theorem signCompact_queries (message : Message) :
    Queries (SecurityIdealSign.signCompact message) 117508 := by
  unfold SecurityIdealSign.signCompact
  refine Queries.bind (nextCost := 117506) (randomizedIndex message) _ ?_
  intro ri
  refine Queries.bind (cost := 5) (nextCost := 117501) ?_ _ ?_
  · exact signLayerWithRoot ⟨0, by decide⟩ _ _ _
  · intro bottom
    refine Queries.bind (cost := 117501) (nextCost := 0) ?_ _ ?_
    · exact signUpper 159 1 (ri.2.toNat / 2) _ _ bottom.2 (by decide)
    · intro upper
      exact Queries.pure _

/-- Organizer-charge instance used by the atomic cutoff macro. -/
theorem signCompact (message : Message) :
    FixedCost ((SecurityIdealSign.signCompact message).liftComp GameWorld) 117508 :=
  (signCompact_queries message).fixedCost

/-- Serialization is pure and therefore the actual wire-signing interface has
the same fixed structural charge. -/
theorem signWire (message : Message) :
    FixedCost ((SecurityExperiment.signWire message).liftComp GameWorld) 117508 :=
  ((signCompact_queries message).map SecurityExperiment.serialize).fixedCost

end SigGolfCandidate.Hypertree.SecurityAtomicCounts

end

namespace SigGolfCandidate.Hypertree.SecurityExperimentAtomic
open SigGolf OracleComp OracleSpec SecurityDerivation SecurityGameHop SecuritySeparation
  SecurityBudget SecurityExperiment SecurityAtomicCutoff
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- The exact transcript update of the reference signing action, including a
failed response. The external counted/cutoff semantics charges the hash work. -/
def afterSign (transcript : Transcript submission.sizes) (message : Message)
    (response : Option (Bytes submission.sizes.signature)) : Transcript submission.sizes :=
  { transcript with
    signed := match response with
      | none => transcript.signed
      | some signature => (message, signature) :: transcript.signed
    signingRequests := transcript.signingRequests + 1 }

def signContinuation (adversary : Adversary submission.sizes) (pk : PublicKey) (rounds : Nat)
    (transcript : Transcript submission.sizes) (request : SigningRequest)
    (resume : Option (Bytes submission.sizes.signature) → adversary.State)
    (response : Option (Bytes submission.sizes.signature)) : OracleComp GameWorld Result :=
  interact adversary pk rounds (resume response) (afterSign transcript request.message response)

/-- Key generation is the actual first block of the reference experiment. -/
theorem program_cutoff_enough (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) (enough : 739 ≤ budget) :
    cutoff (program publicCache adversary rounds) budget = (do
      let pk ← SecurityIdealKeygen.keygen.liftComp GameWorld
      cutoff (interact adversary pk rounds (adversary.initial pk publicCache) {}) (budget - 739)) :=
  SecurityAtomicCounts.keygen.bind_enough _ budget enough

/-- Exact terminal-output scheduling rule for the actual experiment's keygen,
under the actual ideal game oracle and an arbitrary current cache. -/
theorem program_atomic_run (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) (cache : SplitCache) :
    𝒮[(simulateQ idealGameOracle (cutoff (program publicCache adversary rounds) budget)).run' cache] =
      if 739 ≤ budget then
        𝒮[(simulateQ idealGameOracle (do
          let pk ← SecurityIdealKeygen.keygen.liftComp GameWorld
          cutoff (interact adversary pk rounds (adversary.initial pk publicCache) {}) (budget - 739))).run' cache]
      else 𝒮[(pure (none : Option Result) : ProbComp (Option Result))] :=
  SecurityAtomicCounts.keygen.ideal_atomic_run _ cache budget

/-- Sufficient keygen budget retains its complete resulting oracle state before
entering the adversary with precisely the remaining budget. -/
theorem program_run_enough (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) (cache : SplitCache) (enough : 739 ≤ budget) :
    (simulateQ idealGameOracle (cutoff (program publicCache adversary rounds) budget)).run cache =
      ((simulateQ idealGameOracle (SecurityIdealKeygen.keygen.liftComp GameWorld)).run cache >>= fun first =>
        (simulateQ idealGameOracle (cutoff
          (interact adversary first.1 rounds (adversary.initial first.1 publicCache) {}) (budget - 739))).run first.2) :=
  SecurityAtomicCounts.keygen.run_bind_enough idealGameOracle _ cache budget enough

/-- An unaffordable keygen has no completed experiment output. -/
theorem program_run_insufficient (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) (cache : SplitCache) (short : budget < 739) :
    𝒮[(simulateQ idealGameOracle (cutoff (program publicCache adversary rounds) budget)).run' cache] =
      𝒮[(pure (none : Option Result) : ProbComp (Option Result))] := by
  rw [program_atomic_run, if_neg (by omega)]

/-- Unfold only the actual signing action; the 117508-query body stays opaque. -/
theorem interact_sign (adversary : Adversary submission.sizes) (pk : PublicKey) (rounds : Nat)
    (state : adversary.State) (transcript : Transcript submission.sizes) (request : SigningRequest)
    (resume : Option (Bytes submission.sizes.signature) → adversary.State)
    (action : adversary.step state = .sign request resume)
    (allowed : transcript.signingRequests < LIFETIME) :
    interact adversary pk (rounds + 1) state transcript =
      ((signWire request.message).liftComp GameWorld >>=
        signContinuation adversary pk rounds transcript request resume) := by
  simp only [interact, action, if_pos allowed]
  rfl

/-- The exact signing response resumes the actual adversary and updates exactly
one signing slot before execution continues with the remaining budget. -/
theorem interact_sign_cutoff_enough (adversary : Adversary submission.sizes) (pk : PublicKey)
    (rounds budget : Nat) (state : adversary.State) (transcript : Transcript submission.sizes)
    (request : SigningRequest) (resume : Option (Bytes submission.sizes.signature) → adversary.State)
    (action : adversary.step state = .sign request resume)
    (allowed : transcript.signingRequests < LIFETIME) (enough : 117508 ≤ budget) :
    cutoff (interact adversary pk (rounds + 1) state transcript) budget = (do
      let response ← (signWire request.message).liftComp GameWorld
      cutoff (signContinuation adversary pk rounds transcript request resume response) (budget - 117508)) := by
  rw [interact_sign adversary pk rounds state transcript request resume action allowed]
  exact (SecurityAtomicCounts.signWire request.message).bind_enough _ budget enough

/-- Stateful signing-block decomposition under the actual ideal oracle. -/
theorem interact_sign_run_enough (adversary : Adversary submission.sizes) (pk : PublicKey)
    (rounds budget : Nat) (state : adversary.State) (transcript : Transcript submission.sizes)
    (request : SigningRequest) (resume : Option (Bytes submission.sizes.signature) → adversary.State)
    (cache : SplitCache) (action : adversary.step state = .sign request resume)
    (allowed : transcript.signingRequests < LIFETIME) (enough : 117508 ≤ budget) :
    (simulateQ idealGameOracle (cutoff (interact adversary pk (rounds + 1) state transcript) budget)).run cache =
      ((simulateQ idealGameOracle ((signWire request.message).liftComp GameWorld)).run cache >>= fun first =>
        (simulateQ idealGameOracle (cutoff
          (signContinuation adversary pk rounds transcript request resume first.1) (budget - 117508))).run first.2) := by
  rw [interact_sign adversary pk rounds state transcript request resume action allowed]
  exact (SecurityAtomicCounts.signWire request.message).run_bind_enough idealGameOracle _ cache budget enough

/-- Signing at the lifetime limit returns the reference failure result without
entering the signing block, for every remaining query budget. -/
theorem interact_sign_lifetime (adversary : Adversary submission.sizes) (pk : PublicKey)
    (rounds budget : Nat) (state : adversary.State) (transcript : Transcript submission.sizes)
    (request : SigningRequest) (resume : Option (Bytes submission.sizes.signature) → adversary.State)
    (action : adversary.step state = .sign request resume)
    (exhausted : LIFETIME ≤ transcript.signingRequests) :
    cutoff (interact adversary pk (rounds + 1) state transcript) budget =
      pure (some (⟨false, none, transcript⟩ : Result)) := by
  simp only [interact, action, if_neg (by omega : ¬transcript.signingRequests < LIFETIME), cutoff_pure]

/-- Complete actual signing-action scheduling, with both lifetime and hash-call
gates. No extra no-failure or fixed-H assumptions are required. -/
theorem interact_sign_atomic_run (adversary : Adversary submission.sizes) (pk : PublicKey)
    (rounds budget : Nat) (state : adversary.State) (transcript : Transcript submission.sizes)
    (request : SigningRequest) (resume : Option (Bytes submission.sizes.signature) → adversary.State)
    (cache : SplitCache) (action : adversary.step state = .sign request resume) :
    𝒮[(simulateQ idealGameOracle (cutoff (interact adversary pk (rounds + 1) state transcript) budget)).run' cache] =
      if transcript.signingRequests < LIFETIME then
        if 117508 ≤ budget then
          𝒮[(simulateQ idealGameOracle (do
            let response ← (signWire request.message).liftComp GameWorld
            cutoff (signContinuation adversary pk rounds transcript request resume response) (budget - 117508))).run' cache]
        else 𝒮[(pure (none : Option Result) : ProbComp (Option Result))]
      else 𝒮[(pure (some (⟨false, none, transcript⟩ : Result)) : ProbComp (Option Result))] := by
  by_cases allowed : transcript.signingRequests < LIFETIME
  · rw [if_pos allowed, interact_sign adversary pk rounds state transcript request resume action allowed]
    exact (SecurityAtomicCounts.signWire request.message).ideal_atomic_run _ cache budget
  · rw [if_neg allowed, interact_sign_lifetime adversary pk rounds budget state transcript request resume action (by omega)]
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]

/-- Insufficient signing budget aborts before any completed response is delivered
to the adversary, even though the attempted prefix may have touched hidden cache state. -/
theorem interact_sign_run_insufficient (adversary : Adversary submission.sizes) (pk : PublicKey)
    (rounds budget : Nat) (state : adversary.State) (transcript : Transcript submission.sizes)
    (request : SigningRequest) (resume : Option (Bytes submission.sizes.signature) → adversary.State)
    (cache : SplitCache) (action : adversary.step state = .sign request resume)
    (allowed : transcript.signingRequests < LIFETIME) (short : budget < 117508) :
    𝒮[(simulateQ idealGameOracle (cutoff (interact adversary pk (rounds + 1) state transcript) budget)).run' cache] =
      𝒮[(pure (none : Option Result) : ProbComp (Option Result))] := by
  rw [interact_sign_atomic_run adversary pk rounds budget state transcript request resume cache action,
    if_pos allowed, if_neg (by omega)]

end SigGolfCandidate.Hypertree.SecurityExperimentAtomic
