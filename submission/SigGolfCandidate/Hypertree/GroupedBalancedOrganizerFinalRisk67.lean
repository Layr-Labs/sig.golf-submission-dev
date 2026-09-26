import SigGolfCandidate.Hypertree.GroupedBalancedOrganizerWinningExtraction67
import SigGolfCandidate.Hypertree.GroupedBalancedNonceFullRisk67
import SigGolfCandidate.Hypertree.GroupedBalancedPlantedRealJointUnion67
import SigGolfCandidate.Hypertree.GroupedBalancedNonceCommonProjection67

/-! A completed direct67 organizer win is charged to the four events in the
single paired graph, H5, nonce, and secret-key experiment. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedOrganizerFinalRisk67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphIndexJointClassTrace67
open GroupedBalancedPlantedEagerOrganizerRisk67
open GroupedBalancedOrganizerWinningExtraction67
open GroupedBalancedPlantedEagerUnion67
open GroupedBalancedEagerSecretHit67
open SecuritySecretKey SecurityGameHop
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

abbrev Result := GroupedBalancedGraphOrganizerView67.Result sizes
abbrev Paired := GroupedBalancedPairedStoppedFresh67.PairedResult Result

def FourRisk (pair : SecretKey × Paired) : Prop :=
  ((pair.2.2.1.1.bad = true ∨
    SecurityIndexTrace.Conflict
      (pair.2.2.1.2.map Prod.snd)) ∨
   SecurityMonitorIndexContact.NonceHit
    (fun message => pair.2.1 (.randomizer message))
    (GroupedBalancedIndexLabeledHistory67.history
      pair.2.2.2 pair.2.2.1.2)) ∨
  SecretKeyHitTrace
    (stoppedInputs
      (eraseRun
        (pair.2.2.1.1,
          pair.2.2.1.2.map Prod.snd))) pair.1

theorem completed_winner_four_risk
    (adversary : SigGolf.Adversary sizes)
    (publicCache : Cache) (rounds budget : Nat)
    (pair : SecretKey × Paired)
    (member : pair.2 ∈ support
      (GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
        (organizerInteraction sizes GroupedBalancedWire67.wire
          GroupedBalancedWire67.decode GroupedBalancedWire67.decode
          adversary publicCache rounds) budget))
    (winner : ∃ outcome : Result, ∃ trace : List GroupedBalancedGameQueryTrace67.Action,
      ∃ count : Nat,
        pair.2.2.1.1.value.value = some ((some outcome, trace), count) ∧
          outcome.won = true) :
    FourRisk pair := by
  by_cases bad : pair.2.2.1.1.bad = true
  · exact Or.inl (Or.inl (Or.inl bad))
  by_cases hit : SecretKeyHitTrace
      (stoppedInputs
        (eraseRun
          (pair.2.2.1.1,
            pair.2.2.1.2.map Prod.snd))) pair.1
  · exact Or.inr hit
  obtain ⟨outcome, trace, count, completed, won⟩ := winner
  have clean : pair.2.2.1.1.bad = false := by
    cases flag : pair.2.2.1.1.bad <;> simp_all
  have noHit : ¬SecretKeyHitTrace
      (GroupedBalancedGameQueryTrace67.secretInputs trace) pair.1 := by
    intro traceHit
    apply hit
    simpa only [stoppedInputs, eraseRun, eraseOutcome, completed,
      Option.map_some] using traceHit
  have extracted := paired_winning_risk adversary publicCache rounds budget
    pair.1 pair.2 member clean outcome trace count completed won noHit
  rcases extracted with conflict | nonce
  · exact Or.inl (Or.inl (Or.inr conflict))
  · exact Or.inl (Or.inr nonce)

#print axioms completed_winner_four_risk

theorem completed_winner_probability_le_budget
    (adversary : SigGolf.Adversary sizes)
    (publicCache : Cache) (rounds budget : Nat) :
    Pr[fun pair : SecretKey × Paired =>
      ∃ outcome : Result,
        ∃ trace : List GroupedBalancedGameQueryTrace67.Action,
          ∃ count : Nat,
            pair.2.2.1.1.value.value =
              some ((some outcome, trace), count) ∧ outcome.won = true |
      do
        let secretKey ← sampleSecretKey
        let result ←
          GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
            (organizerInteraction sizes GroupedBalancedWire67.wire
              GroupedBalancedWire67.decode GroupedBalancedWire67.decode
              adversary publicCache rounds) budget
        pure (secretKey, result)] ≤
      (budget : ENNReal) / (2 : ENNReal)^127 := by
  let interaction := organizerInteraction sizes GroupedBalancedWire67.wire
    GroupedBalancedWire67.decode GroupedBalancedWire67.decode
    adversary publicCache rounds
  let paired :=
    GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
      interaction budget
  let all := do
    let secretKey ← sampleSecretKey
    let result ← paired
    pure (secretKey, result)
  have eventLe :
      Pr[fun pair : SecretKey × Paired =>
        ∃ outcome : Result,
          ∃ trace : List GroupedBalancedGameQueryTrace67.Action,
            ∃ count : Nat,
              pair.2.2.1.1.value.value =
                some ((some outcome, trace), count) ∧ outcome.won = true |
        all] ≤ Pr[FourRisk | all] := by
    apply probEvent_mono
    intro pair pairMember winner
    have pairedMember : pair.2 ∈ support paired := by
      dsimp only [all] at pairMember
      simp only [mem_support_bind_iff] at pairMember
      obtain ⟨secretKey, _, child⟩ := pairMember
      obtain ⟨result, resultMember, same⟩ := child
      simp only [support_pure, Set.mem_singleton_iff] at same
      cases same
      exact resultMember
    exact completed_winner_four_risk adversary publicCache rounds budget
      pair (by simpa only [paired, interaction] using pairedMember) winner
  have bound :=
    GroupedBalancedNonceFullRisk67.organizer_all_four_risks_le_budget
      sizes GroupedBalancedWire67.wire GroupedBalancedWire67.decode
      GroupedBalancedWire67.decode adversary publicCache rounds budget
  exact eventLe.trans (by
    unfold FourRisk
    exact bound)

#print axioms completed_winner_probability_le_budget

abbrev Annotated :=
  GroupedBalancedGraphIndexJoint67.JointOutcome
    ((Option Result × List GroupedBalancedGameQueryTrace67.Action) × Nat) ×
    List SecurityIndexTrace.Entry

def project (pair : SecretKey × Paired) : SecretKey × Annotated :=
  (pair.1, (pair.2.2.1.1, pair.2.2.1.2.map Prod.snd))

theorem paired_secret_projection
    (adversary : SigGolf.Adversary sizes)
    (publicCache : Cache) (rounds budget : Nat) :
    let interaction := organizerInteraction sizes GroupedBalancedWire67.wire
      GroupedBalancedWire67.decode GroupedBalancedWire67.decode
      adversary publicCache rounds
    project <$> (do
      let secretKey ← sampleSecretKey
      let result ←
        GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
          interaction budget
      pure (secretKey, result)) =
      GroupedBalancedPlantedRealJointUnion67.annotatedSecretGlobal
        interaction budget := by
  dsimp only
  unfold GroupedBalancedPlantedRealJointUnion67.annotatedSecretGlobal
  rw [map_bind]
  apply bind_congr
  intro secretKey
  simp only [map_bind, map_pure, project]
  have projected :=
    GroupedBalancedNonceCommonProjection67.paired_annotated_projection
      (organizerInteraction sizes GroupedBalancedWire67.wire
        GroupedBalancedWire67.decode GroupedBalancedWire67.decode
        adversary publicCache rounds) budget
  simpa only [Functor.map_map, Function.comp_def,
    map_eq_pure_bind, bind_assoc, pure_bind] using
    congrArg (fun d => Prod.mk secretKey <$> d) projected

#print axioms paired_secret_projection

theorem option_winner_completed (result : Annotated)
    (won : optionEvent
      (fun value : Option Result × List GroupedBalancedGameQueryTrace67.Action =>
        ∃ outcome, value.1 = some outcome ∧ outcome.won = true)
      (eraseRun result).1.value.value) :
    ∃ outcome : Result,
      ∃ trace : List GroupedBalancedGameQueryTrace67.Action,
        ∃ count : Nat,
          result.1.value.value = some ((some outcome, trace), count) ∧
            outcome.won = true := by
  cases h : result.1.value.value with
  | none =>
      simp [optionEvent, eraseRun, eraseOutcome, h] at won
  | some value =>
      rcases value with ⟨⟨candidate, trace⟩, count⟩
      cases candidate with
      | none =>
          simp [optionEvent, eraseRun, eraseOutcome, h] at won
      | some outcome =>
          refine ⟨outcome, trace, count, rfl, ?_⟩
          simpa [optionEvent, eraseRun, eraseOutcome, h] using won

#print axioms option_winner_completed

def AnnotatedRisk (pair : SecretKey × Annotated) : Prop :=
  let plain := eraseRun pair.2
  plain.1.bad = true ∨
    optionEvent
      (fun value : Option Result × List GroupedBalancedGameQueryTrace67.Action =>
        ∃ outcome, value.1 = some outcome ∧ outcome.won = true)
      plain.1.value.value ∨
    SecretKeyHitTrace (stoppedInputs plain) pair.1

theorem projected_annotated_risk_four_risk
    (adversary : SigGolf.Adversary sizes)
    (publicCache : Cache) (rounds budget : Nat)
    (pair : SecretKey × Paired)
    (member : pair.2 ∈ support
      (GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
        (organizerInteraction sizes GroupedBalancedWire67.wire
          GroupedBalancedWire67.decode GroupedBalancedWire67.decode
          adversary publicCache rounds) budget))
    (risk : AnnotatedRisk (project pair)) : FourRisk pair := by
  rcases risk with bad | won | hit
  · exact Or.inl (Or.inl (Or.inl bad))
  · obtain ⟨outcome, trace, count, completed, winner⟩ :=
      option_winner_completed (project pair).2 won
    apply completed_winner_four_risk adversary publicCache rounds budget
      pair member
    exact ⟨outcome, trace, count, completed, winner⟩
  · exact Or.inr hit

#print axioms projected_annotated_risk_four_risk

theorem annotated_risk_probability_le_budget
    (adversary : SigGolf.Adversary sizes)
    (publicCache : Cache) (rounds budget : Nat) :
    let interaction := organizerInteraction sizes GroupedBalancedWire67.wire
      GroupedBalancedWire67.decode GroupedBalancedWire67.decode
      adversary publicCache rounds
    Pr[AnnotatedRisk |
      GroupedBalancedPlantedRealJointUnion67.annotatedSecretGlobal
        interaction budget] ≤
      (budget : ENNReal) / (2 : ENNReal)^127 := by
  dsimp only
  let interaction := organizerInteraction sizes GroupedBalancedWire67.wire
    GroupedBalancedWire67.decode GroupedBalancedWire67.decode
    adversary publicCache rounds
  let paired :=
    GroupedBalancedIndexLabeledPairedGlobal67.pairedAuditedGlobal
      interaction budget
  let all := do
    let secretKey ← sampleSecretKey
    let result ← paired
    pure (secretKey, result)
  have projection : project <$> all =
      GroupedBalancedPlantedRealJointUnion67.annotatedSecretGlobal
        interaction budget := by
    simpa only [all, paired, interaction] using
      paired_secret_projection adversary publicCache rounds budget
  have eventLe :
      Pr[fun pair => AnnotatedRisk (project pair) | all] ≤
        Pr[FourRisk | all] := by
    apply probEvent_mono
    intro pair pairMember risk
    have pairedMember : pair.2 ∈ support paired := by
      dsimp only [all] at pairMember
      simp only [mem_support_bind_iff] at pairMember
      obtain ⟨secretKey, _, child⟩ := pairMember
      obtain ⟨result, resultMember, same⟩ := child
      simp only [support_pure, Set.mem_singleton_iff] at same
      cases same
      exact resultMember
    exact projected_annotated_risk_four_risk adversary publicCache
      rounds budget pair (by simpa only [paired, interaction] using
        pairedMember) risk
  have fullBound :=
    GroupedBalancedNonceFullRisk67.organizer_all_four_risks_le_budget
      sizes GroupedBalancedWire67.wire GroupedBalancedWire67.decode
      GroupedBalancedWire67.decode adversary publicCache rounds budget
  calc
    _ = Pr[fun pair => AnnotatedRisk (project pair) | all] := by
      rw [← projection, probEvent_map]
      rfl
    _ ≤ Pr[FourRisk | all] := eventLe
    _ ≤ _ := by
      unfold FourRisk
      exact fullBound

#print axioms annotated_risk_probability_le_budget

def Won (output : Option Result) : Prop :=
  ∃ outcome, output = some outcome ∧ outcome.won = true

theorem planted_real_winning_le_budget
    (adversary : SigGolf.Adversary sizes)
    (publicCache : Cache) (rounds budget : Nat) :
    let interaction := organizerInteraction sizes GroupedBalancedWire67.wire
      GroupedBalancedWire67.decode GroupedBalancedWire67.decode
      adversary publicCache rounds
    Pr[Won |
      GroupedBalancedPlantedRealUnion67.realPlantedGlobal
        interaction budget] ≤
      (budget : ENNReal) / (2 : ENNReal)^127 := by
  dsimp only
  let interaction := organizerInteraction sizes GroupedBalancedWire67.wire
    GroupedBalancedWire67.decode GroupedBalancedWire67.decode
    adversary publicCache rounds
  have first :=
    GroupedBalancedPlantedRealJointUnion67.real_le_annotated_union
      interaction budget Won
  change Pr[Won |
      GroupedBalancedPlantedRealUnion67.realPlantedGlobal
        interaction budget] ≤
      Pr[AnnotatedRisk |
        GroupedBalancedPlantedRealJointUnion67.annotatedSecretGlobal
          interaction budget] at first
  exact first.trans
    (annotated_risk_probability_le_budget adversary publicCache
      rounds budget)

#print axioms planted_real_winning_le_budget

/-- The organizer's counted total-call experiment is the same winning event
as its cutoff experiment, with the same graph table and sampled secret key. -/
theorem planted_counted_winning_le_budget
    (adversary : SigGolf.Adversary sizes)
    (publicCache : Cache) (rounds budget : Nat) :
    Pr[fun result => result.1.won = true ∧ result.2 ≤ budget |
      do
        let table ← $ᵗ PointTable
        let secretKey ← sampleSecretKey
        (simulateQ (realGameOracle secretKey)
          (SecurityBudget.counted
            (GroupedBalancedGameWorldBudget67.organizerProgram
              sizes GroupedBalancedWire67.wire
              GroupedBalancedWire67.decode GroupedBalancedWire67.decode
              adversary publicCache rounds table))).run'
          (GroupedBalancedPlantedCache67.planted table)] ≤
      (budget : ENNReal) / (2 : ENNReal)^127 := by
  let interaction := organizerInteraction sizes GroupedBalancedWire67.wire
    GroupedBalancedWire67.decode GroupedBalancedWire67.decode
    adversary publicCache rounds
  have cutoffEq :
      Pr[Won |
        GroupedBalancedPlantedRealUnion67.realPlantedGlobal
          interaction budget] =
      Pr[fun result => result.1.won = true ∧ result.2 ≤ budget |
        do
          let table ← $ᵗ PointTable
          let secretKey ← sampleSecretKey
          (simulateQ (realGameOracle secretKey)
            (SecurityBudget.counted
              (GroupedBalancedGameWorldBudget67.organizerProgram
                sizes GroupedBalancedWire67.wire
                GroupedBalancedWire67.decode GroupedBalancedWire67.decode
                adversary publicCache rounds table))).run'
            (GroupedBalancedPlantedCache67.planted table)] := by
    unfold GroupedBalancedPlantedRealUnion67.realPlantedGlobal
    simp only [probEvent_bind_eq_tsum]
    apply tsum_congr
    intro table
    congr 1
    apply tsum_congr
    intro secretKey
    congr 1
    exact SecurityBudget.prob_cutoff_eq_counted
      (realGameOracle secretKey)
      (GroupedBalancedGameWorldBudget67.organizerProgram
        sizes GroupedBalancedWire67.wire GroupedBalancedWire67.decode
        GroupedBalancedWire67.decode adversary publicCache rounds table)
      (GroupedBalancedPlantedCache67.planted table) budget
      (fun result => result.won = true)
  rw [← cutoffEq]
  exact planted_real_winning_le_budget adversary publicCache rounds budget

#print axioms planted_counted_winning_le_budget

end SigGolfCandidate.Hypertree.GroupedBalancedOrganizerFinalRisk67
