import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexProgram67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexCost67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexMarks67. -/
section
/-! A structural credit for selective H5 traces. Only tag-5 draws spend credit;
ordinary uniform choices carried by coins spend none. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexCost67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphIndexLift67
open GroupedBalancedGraphIndexProgram67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 50000
open scoped Classical

def Credit {α : Type} (cost : α → Nat) (spent : Nat) :
    SecurityIndexProgram.Program α → Prop
  | .pure value => spent ≤ cost value
  | .draw _ next => ∀ answer, Credit cost (spent + 1) (next answer)
  | .coin _ next => ∀ answer, Credit cost spent (next answer)


theorem credit_execute {α : Type} (cost : α → Nat)
    (spent : Nat) (program : SecurityIndexProgram.Program α)
    (credit : Credit cost spent program) :
    ∀ result ∈ support (SecurityIndexProgram.execute program),
      spent + result.2.length ≤ cost result.1 := by
  induction program generalizing spent with
  | pure value =>
      change spent ≤ cost value at credit
      intro result member
      simp only [SecurityIndexProgram.execute, support_pure,
        Set.mem_singleton_iff] at member
      subst result
      simpa only [List.length_nil, Nat.add_zero] using credit
  | coin n next ih =>
      intro result member
      simp only [SecurityIndexProgram.execute, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      exact ih answer spent (credit answer) result member
  | draw mark next ih =>
      intro result member
      simp only [SecurityIndexProgram.execute, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      simp only [support_map, Set.mem_image] at member
      obtain ⟨tail, tailMember, same⟩ := member
      subst result
      have bound := ih answer (spent + 1) (credit answer) tail tailMember
      simp only [List.length_cons]
      omega

theorem unmarked_credit {α β : Type} (program : ProbComp α)
    (next : α → SecurityIndexProgram.Program β)
    (cost : β → Nat) (spent : Nat)
    (credit : ∀ value, Credit cost spent (next value)) :
    Credit cost spent (unmarked program next) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact credit value
  | query_bind n resume ih =>
      rw [unmarked_query]
      exact fun answer => ih answer

theorem readIndex_credit {β : Type} (state : State) (input : Query)
    (mark : Bool)
    (next : BitVec 256 → QueryCache HashSpec →
      SecurityIndexProgram.Program β)
    (cost : β → Nat) (spent : Nat)
    (cached : ∀ answer, state.residual input = some answer →
      Credit cost spent (next answer state.residual))
    (fresh : state.residual input = none → ∀ answer,
      Credit cost (spent + 1)
        (next answer (state.residual.cacheQuery input answer))) :
    Credit cost spent (readIndex state input mark next) := by
  cases present : state.residual input with
  | some answer =>
      simp only [readIndex, present, Credit]
      exact cached answer present
  | none =>
      simp only [readIndex, present, Credit]
      exact fresh present

theorem hashStepOn_credit {β : Type}
    (parsed : Option (Message × Bytes 32))
    (table : PointTable) (state : State) (input : Query)
    (next : BitVec 256 → State → SecurityIndexProgram.Program β)
    (cost : β → Nat) (spent : Nat)
    (outside : ∀ result : BitVec 256 × QueryCache HashSpec,
      Credit cost spent
        (next result.1 { state with residual := result.2 }))
    (cached : ∀ answer, state.residual input = some answer →
      Credit cost spent
        (next answer (state.recordIndex state.residual)))
    (fresh : state.residual input = none → ∀ answer,
      Credit cost (spent + 1)
        (next answer
          (state.recordIndex (state.residual.cacheQuery input answer)))) :
    Credit cost spent (hashStepOn parsed table state input next) := by
  cases parsed with
  | none =>
      simp only [hashStepOn]
      exact unmarked_credit _ _ cost spent outside
  | some pair =>
      simp only [hashStepOn]
      exact readIndex_credit state input false _ cost spent cached fresh

theorem signStep_outer_credit {β : Type}
    (table : PointTable) (secretKey : SecretKey)
    (setup : QueryCache GroupedBalancedGraphPassive67.PointSpec)
    (state : State) (message : Message)
    (next : GroupedBalancedScheme67.Signature → State →
      SecurityIndexProgram.Program β)
    (cost : β → Nat) (spent : Nat)
    (continuation : ∀ randomizerResult :
      BitVec 256 × QueryCache HashSpec,
      Credit cost spent
        (readIndex { state with residual := randomizerResult.2 }
          (SecurityRandomOracle.indexInput message randomizerResult.1)
          (decide (message ∉ state.signedMessages))
          (fun indexAnswer residual =>
            next
              (GroupedBalancedGraphHonestSignView67.signatureFromAnswers
                setup randomizerResult.1 (indexAnswer.extractLsb' 0 160)
                (table (.inr (.inl (indexAnswer.extractLsb' 0 160)))))
              (state.recordSign message residual)))) :
    Credit cost spent
      (signStep table secretKey setup state message next) := by
  unfold signStep
  apply unmarked_credit
  exact continuation

#print axioms credit_execute
#print axioms unmarked_credit
#print axioms readIndex_credit
#print axioms hashStepOn_credit
#print axioms signStep_outer_credit

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexCost67

end

/-! A marked-draw credit for the direct67 H5 trace. Public H5 lookups
produce unmarked draws; only a first honest signing lookup can mark. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexMarks67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphIndexLift67
open GroupedBalancedGraphIndexProgram67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 50000
open scoped Classical

def MarkedCredit {α : Type} (cost : α → Nat) (spent : Nat) :
    SecurityIndexProgram.Program α → Prop
  | .pure value => spent ≤ cost value
  | .draw mark next =>
      ∀ answer, MarkedCredit cost (spent + if mark then 1 else 0)
        (next answer)
  | .coin _ next => ∀ answer, MarkedCredit cost spent (next answer)

theorem marked_execute {α : Type} (cost : α → Nat)
    (spent : Nat) (program : SecurityIndexProgram.Program α)
    (credit : MarkedCredit cost spent program) :
    ∀ result ∈ support (SecurityIndexProgram.execute program),
      spent + SecurityIndexTrace.marks result.2 ≤ cost result.1 := by
  induction program generalizing spent with
  | pure value =>
      change spent ≤ cost value at credit
      intro result member
      simp only [SecurityIndexProgram.execute, support_pure,
        Set.mem_singleton_iff] at member
      subst result
      simpa only [SecurityIndexTrace.marks, Nat.add_zero] using credit
  | coin n next ih =>
      intro result member
      simp only [SecurityIndexProgram.execute, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      exact ih answer spent (credit answer) result member
  | draw mark next ih =>
      intro result member
      simp only [SecurityIndexProgram.execute, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      simp only [support_map, Set.mem_image] at member
      obtain ⟨tail, tailMember, same⟩ := member
      subst result
      have bound :=
        ih answer (spent + if mark then 1 else 0)
          (credit answer) tail tailMember
      simp only [SecurityIndexTrace.marks]
      omega

theorem unmarked_credit {α β : Type} (program : ProbComp α)
    (next : α → SecurityIndexProgram.Program β)
    (cost : β → Nat) (spent : Nat)
    (credit : ∀ value, MarkedCredit cost spent (next value)) :
    MarkedCredit cost spent (unmarked program next) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact credit value
  | query_bind n resume ih =>
      rw [unmarked_query]
      exact fun answer => ih answer

theorem readIndex_credit {β : Type} (state : State) (input : Query)
    (mark : Bool)
    (next : BitVec 256 → QueryCache HashSpec →
      SecurityIndexProgram.Program β)
    (cost : β → Nat) (spent : Nat)
    (cached : ∀ answer, state.residual input = some answer →
      MarkedCredit cost spent (next answer state.residual))
    (fresh : state.residual input = none → ∀ answer,
      MarkedCredit cost (spent + if mark then 1 else 0)
        (next answer (state.residual.cacheQuery input answer))) :
    MarkedCredit cost spent (readIndex state input mark next) := by
  cases present : state.residual input with
  | some answer =>
      simp only [readIndex, present, MarkedCredit]
      exact cached answer present
  | none =>
      simp only [readIndex, present, MarkedCredit]
      exact fresh present

theorem hashStepOn_credit {β : Type}
    (parsed : Option (Message × Bytes 32))
    (table : PointTable) (state : State) (input : Query)
    (next : BitVec 256 → State → SecurityIndexProgram.Program β)
    (cost : β → Nat) (spent : Nat)
    (outside : ∀ result : BitVec 256 × QueryCache HashSpec,
      MarkedCredit cost spent
        (next result.1 { state with residual := result.2 }))
    (cached : ∀ answer, state.residual input = some answer →
      MarkedCredit cost spent
        (next answer (state.recordIndex state.residual)))
    (fresh : state.residual input = none → ∀ answer,
      MarkedCredit cost spent
        (next answer
          (state.recordIndex (state.residual.cacheQuery input answer)))) :
    MarkedCredit cost spent (hashStepOn parsed table state input next) := by
  cases parsed with
  | none =>
      simp only [hashStepOn]
      exact unmarked_credit _ _ cost spent outside
  | some pair =>
      simp only [hashStepOn]
      exact readIndex_credit state input false _ cost spent cached
        (by simpa only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using fresh)

theorem signStep_outer_credit {β : Type}
    (table : PointTable) (secretKey : SecretKey)
    (setup : QueryCache GroupedBalancedGraphPassive67.PointSpec)
    (state : State) (message : Message)
    (next : GroupedBalancedScheme67.Signature → State →
      SecurityIndexProgram.Program β)
    (cost : β → Nat) (spent : Nat)
    (continuation : ∀ randomizerResult :
      BitVec 256 × QueryCache HashSpec,
      MarkedCredit cost spent
        (readIndex { state with residual := randomizerResult.2 }
          (SecurityRandomOracle.indexInput message randomizerResult.1)
          (decide (message ∉ state.signedMessages))
          (fun indexAnswer residual =>
            next
              (GroupedBalancedGraphHonestSignView67.signatureFromAnswers
                setup randomizerResult.1 (indexAnswer.extractLsb' 0 160)
                (table (.inr (.inl (indexAnswer.extractLsb' 0 160)))))
              (state.recordSign message residual)))) :
    MarkedCredit cost spent
      (signStep table secretKey setup state message next) := by
  unfold signStep
  apply unmarked_credit
  exact continuation

#print axioms marked_execute
#print axioms hashStepOn_credit
#print axioms signStep_outer_credit

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexMarks67
