import SigGolfCandidate.Hypertree.GroupedBalancedNonceProgram67


/-! A passive nonce interpreter for the hybrid direct67 H5 program. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceInterpreter67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedNonceProgram67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

abbrev NP := SecurityNonceProgram.Program

noncomputable def interpret {α β : Type} :
    GroupedBalancedNonceProgram67.Program α → Audit →
      (((α × List Draw) × Audit) → NP β) → NP β
  | .pure value, audit, next => next ((value, []), audit)
  | .draw input mark resume, audit, next =>
      .bits (fun answer =>
        let entry : Draw :=
          (input, (mark, answer.extractLsb' 0 160))
        let updated : Audit :=
          { audit with
            h5cache := audit.h5cache.cacheQuery input answer
            draws := audit.draws ++ [entry] }
        interpret (resume answer) updated (fun result =>
          next ((result.1.1, entry :: result.1.2), result.2)))
  | .recordPublic pair resume, audit, next =>
      let continued :=
        interpret resume (publicStep audit pair) next
      if pair.1 ∈ audit.signedMessages then continued
      else .guess pair.1 pair.2 continued
  | .recordSign pair resume, audit, next =>
      .reveal pair.1 (fun _ =>
        interpret resume (signStep audit pair) next)
  | .coin n resume, audit, next =>
      .coin n (fun answer => interpret (resume answer) audit next)
  | .nonce message resume, audit, next =>
      .reveal message (fun answer => interpret (resume answer) audit next)

noncomputable def execute {α : Type}
    (program : GroupedBalancedNonceProgram67.Program α) :
    NP ((α × List Draw) × Audit) :=
  interpret program {} .pure

#print axioms interpret
#print axioms execute

end SigGolfCandidate.Hypertree.GroupedBalancedNonceInterpreter67


/-! The passive interpreter's ordinary output is precisely the old labelled
H5 audit after fixing its nonce table. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceInterpreterObserve67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedNonceProgram67
open GroupedBalancedNonceInterpreter67
open SecurityMonitorNonceLift
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem observe_interpret {α β : Type}
    (nonces : SecurityGraphFactor.NonceTable)
    (cache : SecurityNonceMonitor.NonceCache)
    (program : GroupedBalancedNonceProgram67.Program α)
    (audit : Audit)
    (next : ((α × List Draw) × Audit) → SecurityNonceProgram.Program β) :
    observe nonces cache (interpret program audit next) =
      run (GroupedBalancedNonceProgram67.erase nonces program) audit >>= fun result =>
        observe nonces cache (next result) := by
  induction program generalizing cache audit next with
  | pure value => rfl
  | coin n resume ih =>
      simp only [interpret, GroupedBalancedNonceProgram67.erase, observe,
        SecurityNonceProgram.run,
        GroupedBalancedIndexLabeledAudit67.run,
        map_bind, bind_assoc]
      exact bind_congr fun answer => ih answer cache audit next
  | recordPublic pair resume ih =>
      by_cases signed : pair.1 ∈ audit.signedMessages
      · simp only [interpret, GroupedBalancedNonceProgram67.erase, if_pos signed,
          GroupedBalancedIndexLabeledAudit67.run]
        exact ih cache (publicStep audit pair) next
      · simp only [interpret, GroupedBalancedNonceProgram67.erase, if_neg signed,
          GroupedBalancedIndexLabeledAudit67.run,
          observe, SecurityNonceProgram.run,
          Functor.map_map, SecurityNonceProgram.addGuess]
        exact ih cache (publicStep audit pair) next
  | recordSign pair resume ih =>
      simp only [interpret, GroupedBalancedNonceProgram67.erase,
        GroupedBalancedIndexLabeledAudit67.run,
        observe, SecurityNonceProgram.run]
      rw [← observe, ih (cache.cacheQuery pair.1 (nonces pair.1))
        (signStep audit pair) next]
      apply bind_congr
      intro result
      exact GroupedBalancedNonceObserve67.observe_cache nonces
        (cache.cacheQuery pair.1 (nonces pair.1)) cache (next result)
  | nonce message resume ih =>
      simp only [interpret, GroupedBalancedNonceProgram67.erase, observe,
        SecurityNonceProgram.run]
      rw [← observe,
        ih (nonces message) (cache.cacheQuery message (nonces message)) audit next]
      apply bind_congr
      intro result
      exact GroupedBalancedNonceObserve67.observe_cache nonces
        (cache.cacheQuery message (nonces message)) cache (next result)
  | draw input mark resume ih =>
      simp only [interpret, GroupedBalancedNonceProgram67.erase, observe,
        SecurityNonceProgram.run,
        GroupedBalancedIndexLabeledAudit67.run,
        map_bind, bind_assoc]
      apply bind_congr
      intro answer
      rw [← observe]
      let entry : Draw :=
        (input, (mark, answer.extractLsb' 0 160))
      let updated : Audit :=
        { audit with
          h5cache := audit.h5cache.cacheQuery input answer
          draws := audit.draws ++ [entry] }
      have step := ih answer cache updated
        (fun result => next ((result.1.1, entry :: result.1.2), result.2))
      simpa only [entry, updated, observe, bind_map_left] using step

theorem observe_execute {α : Type}
    (nonces : SecurityGraphFactor.NonceTable)
    (cache : SecurityNonceMonitor.NonceCache)
    (program : GroupedBalancedNonceProgram67.Program α) :
    observe nonces cache (GroupedBalancedNonceInterpreter67.execute program) =
      run (GroupedBalancedNonceProgram67.erase nonces program) {} := by
  simpa only [GroupedBalancedNonceInterpreter67.execute, observe,
    SecurityNonceProgram.run, map_pure, bind_pure] using
    (observe_interpret nonces cache program {} (.pure))

#print axioms observe_interpret
#print axioms observe_execute

end SigGolfCandidate.Hypertree.GroupedBalancedNonceInterpreterObserve67
