import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAudit67
import SigGolfCandidate.Hypertree.SecurityMonitorNonceLift
import SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerCutoff67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedNonceView67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedNonceProgram67. -/
section
/-! A signing view that requests a nonce only when the signer reaches its
randomizer read. Instantiating every request with a fixed private table gives
the existing eager direct67 signing view exactly. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceView67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphHonestSignView67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedGameViewLoggedBridge67
open SecurityGraphIdeal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

inductive NView (α : Type) where
  | done (value : α)
  | hash (query : Query) (next : BitVec 256 → NView α)
  | privateHash (query : Query)
      (outside : GroupedBalancedGraphQuery67.locate query = none)
      (next : BitVec 256 → NView α)
  | sign (index : BitVec 160) (next : BitVec 256 → NView α)
  | coin (n : Nat) (next : Fin (n + 1) → NView α)
  | nonce (message : Message) (next : BitVec 256 → NView α)

noncomputable def instantiate {α : Type} (nonces : Message → BitVec 256) :
    NView α → View α
  | .done value => .done value
  | .hash input next => .hash input (fun answer =>
      instantiate nonces (next answer))
  | .privateHash input outside next => .privateHash input outside
      (fun answer => instantiate nonces (next answer))
  | .sign index next => .sign index (fun answer =>
      instantiate nonces (next answer))
  | .coin n next => .coin n (fun answer =>
      instantiate nonces (next answer))
  | .nonce message next => instantiate nonces (next (nonces message))

noncomputable def map {α β : Type} (f : α → β) : NView α → NView β
  | .done value => .done (f value)
  | .hash input next => .hash input (fun answer => map f (next answer))
  | .privateHash input outside next => .privateHash input outside
      (fun answer => map f (next answer))
  | .sign index next => .sign index (fun answer => map f (next answer))
  | .coin n next => .coin n (fun answer => map f (next answer))
  | .nonce message next => .nonce message (fun answer => map f (next answer))

theorem instantiate_map {α β : Type} (nonces : Message → BitVec 256)
    (f : α → β) (view : NView α) :
    instantiate nonces (map f view) =
      GroupedBalancedGameViewLoggedBridge67.mapView f
        (instantiate nonces view) := by
  induction view with
  | done value => rfl
  | hash input next ih =>
      simp only [map, instantiate,
        GroupedBalancedGameViewLoggedBridge67.mapView]
      exact congrArg _ (funext fun answer => ih answer)
  | privateHash input outside next ih =>
      simp only [map, instantiate,
        GroupedBalancedGameViewLoggedBridge67.mapView]
      exact congrArg _ (funext fun answer => ih answer)
  | sign index next ih =>
      simp only [map, instantiate,
        GroupedBalancedGameViewLoggedBridge67.mapView]
      exact congrArg _ (funext fun answer => ih answer)
  | coin n next ih =>
      simp only [map, instantiate,
        GroupedBalancedGameViewLoggedBridge67.mapView]
      exact congrArg _ (funext fun answer => ih answer)
  | nonce message next ih =>
      exact ih (nonces message)

noncomputable def prependAction {α : Type} (action : Action) :
    NView (α × List Action) → NView (α × List Action) :=
  map (fun result => (result.1, action :: result.2))

theorem instantiate_prependAction {α : Type}
    (nonces : Message → BitVec 256)
    (action : Action) (view : NView (α × List Action)) :
    instantiate nonces (prependAction action view) =
      GroupedBalancedGameViewLoggedBridge67.prependAction action
        (instantiate nonces view) :=
  instantiate_map nonces _ view

noncomputable def cutoff {α : Type} (cache : QueryCache PointSpec) :
    Interaction α → Nat → NView (Option α × List Action)
  | .done value, _ => .done (some value, [])
  | .coin n next, budget => .coin n (fun answer =>
      cutoff cache (next answer) budget)
  | .hash _ _, 0 => .done (none, [])
  | .hash input next, budget + 1 =>
      .hash input (fun answer =>
        prependAction (.publicHash input)
          (cutoff cache (next answer) budget))
  | .sign _ _, 0 => .done (none, [])
  | .sign message next, budget + 1 =>
      prependAction .privateHash
        (match budget with
        | 0 => .done (none, [])
        | budget + 1 =>
            .nonce message (fun randomizer =>
              let input := SecurityRandomOracle.indexInput message randomizer
              .privateHash input (locate_index_none message randomizer)
                (fun indexAnswer =>
                  let index : BitVec 160 := indexAnswer.extractLsb' 0 160
                  .sign index (fun bottomAnswer =>
                    prependAction (.publicHash input)
                      (cutoff cache
                        (next (signatureFromAnswers cache randomizer index
                          bottomAnswer)) budget)))))

theorem instantiate_cutoff {α : Type}
    (answers : PrivateTable) (cache : QueryCache PointSpec)
    (interaction : Interaction α) (budget : Nat) :
    instantiate (fun message => answers (.randomizer message))
      (cutoff cache interaction budget) =
    GroupedBalancedIdealEagerCutoff67.eagerCutoffView answers cache
      interaction budget := by
  induction interaction generalizing budget with
  | done value => rfl
  | coin n next ih =>
      simp only [cutoff, instantiate,
        GroupedBalancedIdealEagerCutoff67.eagerCutoffView]
      exact congrArg _ (funext fun answer => ih answer budget)
  | hash input next ih =>
      cases budget with
      | zero => rfl
      | succ budget =>
          simp only [cutoff, instantiate,
            GroupedBalancedIdealEagerCutoff67.eagerCutoffView]
          congr 1
          funext answer
          rw [instantiate_prependAction, ih answer]
  | sign message next ih =>
      cases budget with
      | zero => rfl
      | succ budget =>
          cases budget with
          | zero =>
              simp only [cutoff,
                GroupedBalancedIdealEagerCutoff67.eagerCutoffView,
                instantiate_prependAction]
              rfl
          | succ budget =>
              simp only [cutoff,
                GroupedBalancedIdealEagerCutoff67.eagerCutoffView,
                instantiate_prependAction, instantiate]
              simp only [ih]

#print axioms instantiate_cutoff

end SigGolfCandidate.Hypertree.GroupedBalancedNonceView67
end

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedNonceLift67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedNonceProgram67. -/
section
/-! Forgetting passive nonce flags and counters leaves the same program
outputs, regardless of which nonces have already been disclosed. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceObserve67
open SigGolf OracleComp OracleSpec Reference
open SecurityNonceProgram SecurityMonitorNonceLift
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem observe_cache {α : Type} (table : SecurityGraphFactor.NonceTable)
    (first second : SecurityNonceMonitor.NonceCache)
    (program : SecurityNonceProgram.Program α) :
    observe table first program = observe table second program := by
  induction program generalizing first second with
  | pure value => rfl
  | reveal message next ih =>
      exact ih (table message) _ _
  | guess message nonce next ih =>
      simpa only [observe, SecurityNonceProgram.run,
        Functor.map_map, Function.comp_def,
        SecurityNonceProgram.addGuess] using ih first second
  | coin n next ih | bits next ih =>
      simp only [observe, SecurityNonceProgram.run, map_bind]
      exact bind_congr fun answer => ih answer first second

#print axioms observe_cache

end SigGolfCandidate.Hypertree.GroupedBalancedNonceObserve67


/-! Translate a nonce-independent labelled H5 segment into the passive
nonce syntax. Public H5 pairs become guesses and signer pairs disclose their
message coordinate. The ordinary output retains the full stopped audit. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceLift67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open SecurityMonitorNonceLift
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

abbrev NP := SecurityNonceProgram.Program

noncomputable def lift {α β : Type} :
    GroupedBalancedIndexLabeledProgram67.Program α → Audit →
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
        lift (resume answer) updated (fun result =>
          next ((result.1.1, entry :: result.1.2), result.2)))
  | .recordPublic pair resume, audit, next =>
      let continued :=
        lift resume (publicStep audit pair) next
      if pair.1 ∈ audit.signedMessages then continued
      else .guess pair.1 pair.2 continued
  | .recordSign pair resume, audit, next =>
      .reveal pair.1 (fun _ =>
        lift resume (signStep audit pair) next)
  | .coin n resume, audit, next =>
      .coin n (fun answer => lift (resume answer) audit next)

#print axioms lift

end SigGolfCandidate.Hypertree.GroupedBalancedNonceLift67
end

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedNonceLiftObserve67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedNonceProgram67. -/
section
/-! The passive nonce interpreter has exactly the ordinary labelled H5
execution as its output marginal for any fixed nonce table. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceLiftObserve67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedNonceLift67
open SecurityMonitorNonceLift
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

theorem observe_lift {α β : Type}
    (nonces : SecurityGraphFactor.NonceTable)
    (cache : SecurityNonceMonitor.NonceCache)
    (program : GroupedBalancedIndexLabeledProgram67.Program α)
    (audit : Audit)
    (next : ((α × List Draw) × Audit) → SecurityNonceProgram.Program β) :
    observe nonces cache (lift program audit next) =
      run program audit >>= fun result =>
        observe nonces cache (next result) := by
  induction program generalizing cache audit next with
  | pure value => rfl
  | coin n resume ih =>
      simp only [lift, observe, SecurityNonceProgram.run,
        GroupedBalancedIndexLabeledAudit67.run,
        map_bind, bind_assoc]
      exact bind_congr fun answer => ih answer cache audit next
  | recordPublic pair resume ih =>
      by_cases signed : pair.1 ∈ audit.signedMessages
      · simp only [lift, if_pos signed,
          GroupedBalancedIndexLabeledAudit67.run]
        exact ih cache (publicStep audit pair) next
      · simp only [lift, if_neg signed,
          GroupedBalancedIndexLabeledAudit67.run,
          observe, SecurityNonceProgram.run,
          Functor.map_map, Function.comp_def,
          SecurityNonceProgram.addGuess]
        exact ih cache (publicStep audit pair) next
  | recordSign pair resume ih =>
      simp only [lift, GroupedBalancedIndexLabeledAudit67.run,
        observe, SecurityNonceProgram.run]
      rw [← observe, ih (cache.cacheQuery pair.1 (nonces pair.1))
        (signStep audit pair) next]
      apply bind_congr
      intro result
      exact GroupedBalancedNonceObserve67.observe_cache nonces
        (cache.cacheQuery pair.1 (nonces pair.1)) cache (next result)
  | draw input mark resume ih =>
      simp only [lift, observe, SecurityNonceProgram.run,
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

#print axioms observe_lift

end SigGolfCandidate.Hypertree.GroupedBalancedNonceLiftObserve67

end

/-! A free program carrying labelled H5 draws and an explicit private nonce
read. Erasing nonce reads with a fixed table gives the existing labelled
direct67 program. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceProgram67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedIndexLabeledProgram67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

inductive Program (α : Type) where
  | pure (value : α)
  | draw (input : Query) (mark : Bool)
      (next : BitVec 256 → Program α)
  | recordPublic (pair : Message × Bytes 32) (next : Program α)
  | recordSign (pair : Message × Bytes 32) (next : Program α)
  | coin (n : Nat) (next : Fin (n + 1) → Program α)
  | nonce (message : Message) (next : BitVec 256 → Program α)

def bind {α β : Type} : Program α → (α → Program β) → Program β
  | .pure value, next => next value
  | .draw input mark resume, next => .draw input mark (fun answer =>
      bind (resume answer) next)
  | .recordPublic pair resume, next => .recordPublic pair
      (bind resume next)
  | .recordSign pair resume, next => .recordSign pair
      (bind resume next)
  | .coin n resume, next => .coin n (fun answer => bind (resume answer) next)
  | .nonce message resume, next => .nonce message (fun answer =>
      bind (resume answer) next)

def erase {α : Type} (nonces : Message → BitVec 256) :
    Program α → GroupedBalancedIndexLabeledProgram67.Program α
  | .pure value => .pure value
  | .draw input mark next => .draw input mark (fun answer =>
      erase nonces (next answer))
  | .recordPublic pair next => .recordPublic pair (erase nonces next)
  | .recordSign pair next => .recordSign pair (erase nonces next)
  | .coin n next => .coin n (fun answer => erase nonces (next answer))
  | .nonce message next => erase nonces (next (nonces message))

def fromLabeled {α : Type} :
    GroupedBalancedIndexLabeledProgram67.Program α → Program α
  | .pure value => .pure value
  | .draw input mark next => .draw input mark (fun answer =>
      fromLabeled (next answer))
  | .recordPublic pair next => .recordPublic pair (fromLabeled next)
  | .recordSign pair next => .recordSign pair (fromLabeled next)
  | .coin n next => .coin n (fun answer => fromLabeled (next answer))

def bindLabeled {α β : Type} :
    GroupedBalancedIndexLabeledProgram67.Program α →
      (α → GroupedBalancedIndexLabeledProgram67.Program β) →
      GroupedBalancedIndexLabeledProgram67.Program β
  | .pure value, next => next value
  | .draw input mark resume, next => .draw input mark (fun answer =>
      bindLabeled (resume answer) next)
  | .recordPublic pair resume, next => .recordPublic pair
      (bindLabeled resume next)
  | .recordSign pair resume, next => .recordSign pair
      (bindLabeled resume next)
  | .coin n resume, next => .coin n (fun answer =>
      bindLabeled (resume answer) next)

theorem erase_fromLabeled {α : Type}
    (nonces : Message → BitVec 256)
    (program : GroupedBalancedIndexLabeledProgram67.Program α) :
    erase nonces (fromLabeled program) = program := by
  induction program with
  | pure value => rfl
  | draw input mark next ih =>
      simp only [fromLabeled, erase]
      exact congrArg _ (funext fun answer => ih answer)
  | coin n next ih =>
      simp only [fromLabeled, erase]
      exact congrArg _ (funext fun answer => ih answer)
  | recordPublic pair next ih =>
      simp only [fromLabeled, erase, ih]
  | recordSign pair next ih =>
      simp only [fromLabeled, erase, ih]

theorem erase_bind {α β : Type}
    (nonces : Message → BitVec 256)
    (program : Program α) (next : α → Program β) :
    erase nonces (bind program next) =
      bindLabeled (erase nonces program)
        (fun value => erase nonces (next value)) := by
  induction program with
  | pure value => rfl
  | draw input mark resume ih =>
      simp only [bind, erase, bindLabeled]
      exact congrArg _ (funext fun answer => ih answer)
  | coin n resume ih =>
      simp only [bind, erase, bindLabeled]
      exact congrArg _ (funext fun answer => ih answer)
  | recordPublic pair resume ih =>
      simp only [bind, erase, bindLabeled, ih]
  | recordSign pair resume ih =>
      simp only [bind, erase, bindLabeled, ih]
  | nonce message resume ih =>
      exact ih (nonces message)

#print axioms erase_fromLabeled
#print axioms erase_bind

end SigGolfCandidate.Hypertree.GroupedBalancedNonceProgram67
