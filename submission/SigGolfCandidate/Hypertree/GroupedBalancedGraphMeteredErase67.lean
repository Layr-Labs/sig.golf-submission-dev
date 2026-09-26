import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSetup67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMetered67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphProgramMap67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphMeteredErase67. -/
section
/-! A pure result map for the passive graph-monitor syntax. It preserves
every reveal, random draw, and contact test. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphProgramMap67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorOracle67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

def mapProgram {α β : Type} (f : α → β) : Program α → Program β
  | .done value => .done (f value)
  | .reveal point next => .reveal point (fun answer => mapProgram f (next answer))
  | .guess point value next => .guess point value (mapProgram f next)
  | .coin n next => .coin n (fun answer => mapProgram f (next answer))
  | .bits next => .bits (fun answer => mapProgram f (next answer))
  | .collision target next => .collision target (fun answer => mapProgram f (next answer))

theorem map_disclose {α β : Type} (f : α → β)
    (points : List Point) (exposed : QueryCache PointSpec)
    (next : QueryCache PointSpec → Program α) :
    mapProgram f (disclose points exposed next) =
      disclose points exposed (fun opened => mapProgram f (next opened)) := by
  induction points generalizing exposed with
  | nil => rfl
  | cons point rest ih =>
      simp only [disclose, mapProgram]
      congr 1
      funext answer
      exact ih _

theorem map_residualStep {α β : Type} (f : α → β)
    (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec)
    (query : Query) (target : Point)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    mapProgram f (residualStep exposed residual query target next) =
      residualStep exposed residual query target
        (fun answer opened cache => mapProgram f (next answer opened cache)) := by
  unfold residualStep
  cases residual query with
  | some answer => rfl
  | none =>
      cases exposed target with
      | some known => rfl
      | none => rfl

theorem map_chainStep {α β : Type} (f : α → β)
    (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec)
    (position : GroupedBalancedSecurityGraph67.Position) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    mapProgram f (chainStep exposed residual position query next) =
      chainStep exposed residual position query
        (fun answer opened cache => mapProgram f (next answer opened cache)) := by
  unfold chainStep
  cases predEq : GroupedBalancedGraphMonitorPredecessor67.predecessor position.val with
  | none =>
      simp only [predEq]
      by_cases equal : query = position.input []
      · simp only [if_pos equal, mapProgram]
      · simp only [if_neg equal]
        exact map_residualStep f exposed residual query (.inl position) next
  | some previous =>
      simp only [predEq]
      cases parsed : parsedChainPayload position query with
      | none =>
          simp only [parsed]
          exact map_residualStep f exposed residual query (.inl position) next
      | some point =>
          simp only [parsed]
          cases knownEq : exposed previous with
          | none =>
              simp only [knownEq, mapProgram]
              exact congrArg (Program.guess previous point)
                (map_residualStep f exposed residual query (.inl position) next)
          | some known =>
              simp only [knownEq]
              by_cases equal : point = truncate known
              · simp only [if_pos equal, mapProgram]
              · simp only [if_neg equal]
                exact map_residualStep f exposed residual query (.inl position) next

theorem map_publicStep {α β : Type} (f : α → β)
    (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec)
    (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    mapProgram f (publicStep exposed residual query next) =
      publicStep exposed residual query
        (fun answer opened cache => mapProgram f (next answer opened cache)) := by
  unfold publicStep
  cases located : GroupedBalancedGraphQuery67.locate query with
  | none =>
      simp only [located]
      cases residual query <;> rfl
  | some position =>
      simp only [located]
      by_cases tag : position.val.tag.val = 2
      · simp only [if_pos tag]
        exact map_chainStep f exposed residual position query next
      · simp only [if_neg tag]
        rw [map_disclose]
        congr 1
        funext opened
        split
        · rfl
        · exact map_residualStep f opened residual query (.inl position) next

theorem map_setup {α β : Type} (f : α → β)
    (next : QueryCache PointSpec → Program α) :
    mapProgram f (GroupedBalancedGraphMonitorSetup67.setup next) =
      GroupedBalancedGraphMonitorSetup67.setup
        (fun exposed => mapProgram f (next exposed)) := by
  unfold GroupedBalancedGraphMonitorSetup67.setup
  rw [map_disclose]
  congr 1
  funext known
  exact map_disclose f _ _ next

def mapOutcome {α β : Type} (f : α → β) (result : Outcome α) : Outcome β :=
  ⟨f result.value, result.bad, result.tests⟩

theorem run_map {α β : Type} (f : α → β) (table : PointTable)
    (cache : QueryCache PointSpec) (program : Program α) :
    run table cache (mapProgram f program) =
      mapOutcome f <$> run table cache program := by
  induction program generalizing cache with
  | done value => rfl
  | reveal point next ih => exact ih (table point) _
  | guess point value next ih =>
      simp only [mapProgram, run, ih, Functor.map_map]
      rfl
  | coin n next ih | bits next ih =>
      simp only [mapProgram, run, map_bind]
      apply bind_congr
      intro answer
      exact ih answer cache
  | collision target next ih =>
      simp only [mapProgram, run, map_bind]
      apply bind_congr
      intro answer
      rw [ih answer cache, Functor.map_map]
      simp only [Functor.map_map]
      rfl

#print axioms map_publicStep
#print axioms run_map

end SigGolfCandidate.Hypertree.GroupedBalancedGraphProgramMap67

end

/-! Forgetting the class-specific meter gives the original graph monitor
program exactly, including its adaptive reveal and contact-test order. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMeteredErase67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphProgramMap67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

def drop {α : Type} (result : GroupedBalancedGraphMetered67.Result α) :
    Option α × Nat × State :=
  (result.value, result.remaining, result.state)

theorem map_limited {α : Type} (view : View α)
    (remaining : Nat) (state : State) (graphCalls : Nat) :
    mapProgram drop
      (GroupedBalancedGraphMetered67.limited view remaining state graphCalls) =
      GroupedBalancedGraphMonitorSignCompiler67.limited view remaining state := by
  induction view generalizing remaining state graphCalls with
  | done value => rfl
  | coin n next ih =>
      simp only [GroupedBalancedGraphMetered67.limited,
        GroupedBalancedGraphMonitorSignCompiler67.limited, mapProgram]
      congr 1
      funext answer
      exact ih answer remaining state graphCalls
  | sign index next ih =>
      simp only [GroupedBalancedGraphMetered67.limited,
        GroupedBalancedGraphMonitorSignCompiler67.limited, mapProgram]
      congr 1
      funext answer
      exact ih answer remaining (signed state index answer) graphCalls
  | privateHash input outside next ih =>
      cases cached : state.residual input with
      | some answer =>
          simp only [GroupedBalancedGraphMetered67.limited,
            GroupedBalancedGraphMonitorSignCompiler67.limited, cached]
          exact ih answer remaining state graphCalls
      | none =>
          simp only [GroupedBalancedGraphMetered67.limited,
            GroupedBalancedGraphMonitorSignCompiler67.limited, cached,
            mapProgram]
          congr 1
          funext answer
          exact ih answer remaining
            (privateOpened state input answer) graphCalls
  | hash input next ih =>
      cases remaining with
      | zero => rfl
      | succ remaining =>
          cases located : GroupedBalancedGraphQuery67.locate input with
          | none =>
              simp only [GroupedBalancedGraphMetered67.limited,
                GroupedBalancedGraphMonitorSignCompiler67.limited, located,
                map_publicStep]
              congr 1
              funext answer exposed residual
              exact ih answer remaining (opened state exposed residual)
                graphCalls
          | some position =>
              simp only [GroupedBalancedGraphMetered67.limited,
                GroupedBalancedGraphMonitorSignCompiler67.limited, located,
                map_publicStep]
              congr 1
              funext answer exposed residual
              exact ih answer remaining (opened state exposed residual)
                (graphCalls + 1)

#print axioms map_limited

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMeteredErase67
