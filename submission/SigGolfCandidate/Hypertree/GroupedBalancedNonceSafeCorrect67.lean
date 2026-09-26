import SigGolfCandidate.Hypertree.GroupedBalancedNonceSafeProgram67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedNonceInterpretMap67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedNonceSafeCorrect67. -/
section
/-! Pure output maps on passive nonce programs preserve their monitor flag
and charged guess count. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceProgramMap67
open SigGolf OracleComp OracleSpec Reference
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

def map {α β : Type} (f : α → β) :
    SecurityNonceProgram.Program α → SecurityNonceProgram.Program β
  | .pure value => .pure (f value)
  | .reveal message next => .reveal message (fun answer => map f (next answer))
  | .guess message nonce next => .guess message nonce (map f next)
  | .coin n next => .coin n (fun answer => map f (next answer))
  | .bits next => .bits (fun answer => map f (next answer))

def mapValue {α β : Type} (f : α → β)
    (result : SecurityNonceProgram.Outcome α) :
    SecurityNonceProgram.Outcome β :=
  ⟨f result.value, result.bad, result.guesses⟩

theorem run_map {α β : Type} (f : α → β)
    (nonces : SecurityGraphFactor.NonceTable)
    (cache : SecurityNonceMonitor.NonceCache)
    (program : SecurityNonceProgram.Program α) :
    SecurityNonceProgram.run nonces cache (map f program) =
    mapValue f <$> SecurityNonceProgram.run nonces cache program := by
  induction program generalizing cache with
  | pure value => rfl
  | reveal message next ih =>
      exact ih (nonces message) (cache.cacheQuery message (nonces message))
  | coin n next ih | bits next ih =>
      simp only [map, SecurityNonceProgram.run, map_bind]
      exact bind_congr (fun answer => ih answer cache)
  | guess message nonce next ih =>
      simp only [map, SecurityNonceProgram.run, ih, Functor.map_map]
      congr 1

#print axioms run_map

end SigGolfCandidate.Hypertree.GroupedBalancedNonceProgramMap67


/-! Naturality of the passive interpreter in its final value. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceInterpretMap67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedNonceProgram67
open GroupedBalancedNonceInterpreter67
open GroupedBalancedNonceProgramMap67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem interpret_natural {α β γ : Type}
    (f : β → γ) (program : Program α) (audit : Audit)
    (next : ((α × List GroupedBalancedIndexLabeledProgram67.Draw) × Audit) →
      SecurityNonceProgram.Program β) :
    interpret program audit (fun result => map f (next result)) =
      map f (interpret program audit next) := by
  induction program generalizing audit next with
  | pure value => rfl
  | draw input mark resume ih =>
      simp only [interpret, map]
      exact congrArg _ (funext fun answer =>
        ih answer _ (fun result =>
          next ((result.1.1,
            (input, (mark, answer.extractLsb' 0 160)) :: result.1.2),
            result.2)))
  | recordPublic pair resume ih =>
      simp only [interpret]
      split <;> simp only [map, ih]
  | recordSign pair resume ih =>
      simp only [interpret, map]
      exact congrArg _ (funext fun answer => ih _ _)
  | coin n resume ih =>
      simp only [interpret, map]
      exact congrArg _ (funext fun answer => ih answer _ _)
  | nonce message resume ih =>
      simp only [interpret, map]
      exact congrArg _ (funext fun answer => ih answer _ _)

theorem interpret_pure_map {α β : Type}
    (f : ((α × List GroupedBalancedIndexLabeledProgram67.Draw) × Audit) → β)
    (program : Program α) (audit : Audit) :
    interpret program audit (fun result => .pure (f result)) =
      map f (interpret program audit .pure) := by
  simpa only [map] using interpret_natural f program audit
    (fun result => SecurityNonceProgram.Program.pure result)

#print axioms interpret_natural
#print axioms interpret_pure_map

end SigGolfCandidate.Hypertree.GroupedBalancedNonceInterpretMap67
end

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceSafeCorrect67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedNonceProgram67
open GroupedBalancedNonceInterpreter67
open GroupedBalancedNonceSafeProgram67
open GroupedBalancedNonceTrack67
open GroupedBalancedNonceProgramMap67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

mutual
 theorem correctSafe {α : Type} {program : Program α} (safe : Safe program)
   (nonces : SecurityGraphFactor.NonceTable)
   (cache : SecurityNonceMonitor.NonceCache) (audit : Audit)
   (tracked : Tracks cache audit) :
   accumulate nonces audit <$> SecurityNonceProgram.run nonces cache
     (interpret program audit (.pure)) =
   annotate nonces <$> GroupedBalancedIndexLabeledAudit67.run
     (erase nonces program) audit := by
  cases safe with
  | pure value =>
      simp [GroupedBalancedNonceInterpreter67.interpret,
        SecurityNonceProgram.run, GroupedBalancedIndexLabeledAudit67.run,
        GroupedBalancedNonceProgram67.erase, accumulate, annotate, hits]
  | draw input mark next children =>
      simp only [GroupedBalancedNonceInterpreter67.interpret,
        SecurityNonceProgram.run, GroupedBalancedNonceProgram67.erase,
        GroupedBalancedIndexLabeledAudit67.run, map_bind]
      apply bind_congr
      intro answer
      let entry : GroupedBalancedIndexLabeledProgram67.Draw :=
        (input, (mark, answer.extractLsb' 0 160))
      let updated : Audit :=
        { audit with
          h5cache := audit.h5cache.cacheQuery input answer
          draws := audit.draws ++ [entry] }
      let wrap : ((α × List GroupedBalancedIndexLabeledProgram67.Draw) × Audit) →
        ((α × List GroupedBalancedIndexLabeledProgram67.Draw) × Audit) :=
        fun result => ((result.1.1, entry :: result.1.2), result.2)
      change accumulate nonces audit <$>
        SecurityNonceProgram.run nonces cache
          (interpret (next answer) updated
            (fun result => SecurityNonceProgram.Program.pure (wrap result))) =
        annotate nonces <$>
          (wrap <$> GroupedBalancedIndexLabeledAudit67.run
            (erase nonces (next answer)) updated)
      rw [GroupedBalancedNonceInterpretMap67.interpret_pure_map,
        GroupedBalancedNonceProgramMap67.run_map]
      simp only [Functor.map_map]
      have child := correctSafe (children answer) nonces cache updated
        (tracked.draw input mark answer)
      have mapped := congrArg
        (fun distribution => mapValue wrap <$> distribution) child
      simpa only [Functor.map_map, Function.comp_def,
        mapValue, accumulate, annotate, hits, updated, wrap]
        using mapped
  | recordPublic pair next child =>
      simp only [GroupedBalancedNonceInterpreter67.interpret,
        GroupedBalancedNonceProgram67.erase,
        GroupedBalancedIndexLabeledAudit67.run]
      rw [accumulate_public nonces cache audit tracked pair]
      exact correctSafe child nonces cache (publicStep audit pair)
        (tracked.public pair)
  | recordSign pair next child =>
      simp only [GroupedBalancedNonceInterpreter67.interpret,
        SecurityNonceProgram.run,
        GroupedBalancedNonceProgram67.erase,
        GroupedBalancedIndexLabeledAudit67.run]
      simpa only [accumulate_sign_fun] using
        (correctSafe child nonces
          (cache.cacheQuery pair.1 (nonces pair.1))
          (signStep audit pair)
          (tracked.sign pair.1 (nonces pair.1) pair rfl))
  | coin n next children =>
      simp only [GroupedBalancedNonceInterpreter67.interpret,
        SecurityNonceProgram.run, GroupedBalancedNonceProgram67.erase,
        GroupedBalancedIndexLabeledAudit67.run, map_bind]
      exact bind_congr (fun answer =>
        correctSafe (children answer) nonces cache audit tracked)
  | nonce message next children =>
      simp only [GroupedBalancedNonceInterpreter67.interpret,
        SecurityNonceProgram.run,
        GroupedBalancedNonceProgram67.erase]
      exact correctPending (children (nonces message)) nonces cache audit tracked
 theorem correctPending {α : Type} {program : Program α} {message : Message}
   (pending : Pending message program)
   (nonces : SecurityGraphFactor.NonceTable)
   (cache : SecurityNonceMonitor.NonceCache) (audit : Audit)
   (tracked : Tracks cache audit) :
   accumulate nonces audit <$> SecurityNonceProgram.run nonces
     (cache.cacheQuery message (nonces message))
     (interpret program audit (.pure)) =
   annotate nonces <$> GroupedBalancedIndexLabeledAudit67.run
     (erase nonces program) audit := by
  cases pending with
  | recordSign message pair same next child =>
      simp only [GroupedBalancedNonceInterpreter67.interpret,
        SecurityNonceProgram.run,
        GroupedBalancedNonceProgram67.erase,
        GroupedBalancedIndexLabeledAudit67.run]
      simpa only [accumulate_sign_fun] using
        (correctSafe child nonces
          ((cache.cacheQuery message (nonces message)).cacheQuery
            pair.1 (nonces pair.1))
          (signStep audit pair)
          (by
            rw [same]
            exact tracked.doubleSign message (nonces message) pair same))
  | draw message input mark next children =>
      simp only [GroupedBalancedNonceInterpreter67.interpret,
        SecurityNonceProgram.run, GroupedBalancedNonceProgram67.erase,
        GroupedBalancedIndexLabeledAudit67.run, map_bind]
      apply bind_congr
      intro answer
      let entry : GroupedBalancedIndexLabeledProgram67.Draw :=
        (input, (mark, answer.extractLsb' 0 160))
      let updated : Audit :=
        { audit with
          h5cache := audit.h5cache.cacheQuery input answer
          draws := audit.draws ++ [entry] }
      let wrap : ((α × List GroupedBalancedIndexLabeledProgram67.Draw) × Audit) →
        ((α × List GroupedBalancedIndexLabeledProgram67.Draw) × Audit) :=
        fun result => ((result.1.1, entry :: result.1.2), result.2)
      change accumulate nonces audit <$>
        SecurityNonceProgram.run nonces
          (cache.cacheQuery message (nonces message))
          (interpret (next answer) updated
            (fun result => SecurityNonceProgram.Program.pure (wrap result))) =
        annotate nonces <$>
          (wrap <$> GroupedBalancedIndexLabeledAudit67.run
            (erase nonces (next answer)) updated)
      rw [GroupedBalancedNonceInterpretMap67.interpret_pure_map,
        GroupedBalancedNonceProgramMap67.run_map]
      simp only [Functor.map_map]
      have child := correctPending (children answer) nonces cache updated
        (tracked.draw input mark answer)
      have mapped := congrArg
        (fun distribution => mapValue wrap <$> distribution) child
      simpa only [Functor.map_map, Function.comp_def,
        mapValue, accumulate, annotate, hits, updated, wrap]
        using mapped
end

#print axioms correctSafe
#print axioms correctPending

end SigGolfCandidate.Hypertree.GroupedBalancedNonceSafeCorrect67
