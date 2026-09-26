import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexLift67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphInteraction67
import SigGolfCandidate.Hypertree.SecurityIndexQuery

/-! An input-labelled H5 trace compiler for the direct67 adversary interaction.
Only fresh H5 oracle answers become index-monitor draws. Other public graph
answers, secret randomizers, and private coins remain fully adaptive ordinary
randomness. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexProgram67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphIndexLift67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

structure State where
  residual : QueryCache HashSpec := ∅
  signedMessages : Finset Message := ∅
  indexCalls : Nat := 0

def State.recordIndex (state : State) (residual : QueryCache HashSpec) : State :=
  { state with
    residual := residual
    indexCalls := state.indexCalls + 1 }

def State.recordSign (state : State) (message : Message)
    (residual : QueryCache HashSpec) : State :=
  { state with
    residual := residual
    signedMessages := insert message state.signedMessages
    indexCalls := state.indexCalls + 1 }

noncomputable def readIndex {α : Type} (state : State)
    (input : Query) (mark : Bool)
    (next : BitVec 256 → QueryCache HashSpec →
      SecurityIndexProgram.Program α) : SecurityIndexProgram.Program α :=
  match state.residual input with
  | some answer => next answer state.residual
  | none => .draw mark (fun answer =>
      next answer (state.residual.cacheQuery input answer))

noncomputable def hashStepOn {α : Type}
    (parsed : Option (Message × Bytes 32)) (table : PointTable)
    (state : State) (input : Query)
    (next : BitVec 256 → State → SecurityIndexProgram.Program α) :
    SecurityIndexProgram.Program α :=
  match parsed with
  | some _ => readIndex state input false (fun answer residual =>
      next answer (state.recordIndex residual))
  | none =>
      unmarked
        ((GroupedBalancedGraphOracle67.publicOracle
          (GroupedBalancedGraphMonitorTable67.privateOf table)
          (GroupedBalancedGraphMonitorTable67.labelsOf table)
          input).run state.residual)
        (fun result => next result.1 { state with residual := result.2 })

noncomputable def hashStep {α : Type} (table : PointTable)
    (state : State) (input : Query)
    (next : BitVec 256 → State → SecurityIndexProgram.Program α) :
    SecurityIndexProgram.Program α :=
  hashStepOn (SecurityIndexQuery.parse input) table state input next

noncomputable def signStep {α : Type} (table : PointTable)
    (secretKey : SecretKey) (setup : QueryCache PointSpec)
    (state : State) (message : Message)
    (next : GroupedBalancedScheme67.Signature → State →
      SecurityIndexProgram.Program α) : SecurityIndexProgram.Program α :=
  unmarked
    ((randomOracle (spec := HashSpec)
      (SecurityRandomOracle.randomizerInput secretKey message)).run
        state.residual)
    (fun randomizerResult =>
      let randomizer := randomizerResult.1
      let afterRandomizer := { state with residual := randomizerResult.2 }
      let input := SecurityRandomOracle.indexInput message randomizer
      readIndex afterRandomizer input
        (decide (message ∉ state.signedMessages))
        (fun indexAnswer residual =>
          let index : BitVec 160 := indexAnswer.extractLsb' 0 160
          let bottomAnswer := table (.inr (.inl index))
          let signature :=
            GroupedBalancedGraphHonestSignView67.signatureFromAnswers
              setup randomizer index bottomAnswer
          next signature (state.recordSign message residual)))

/-- Every parsed public H5 input is either a cache hit or one unmarked draw.
An honest first signing request marks its fresh H5 draw. -/
noncomputable def compile {α : Type} (table : PointTable)
    (secretKey : SecretKey) (setup : QueryCache PointSpec) :
    Interaction α → State → SecurityIndexProgram.Program (α × State)
  | .done value, state => .pure (value, state)
  | .coin n next, state =>
      .coin n (fun answer => compile table secretKey setup (next answer) state)
  | .hash input next, state =>
      hashStep table state input (fun answer updated =>
        compile table secretKey setup (next answer) updated)
  | .sign message next, state =>
      signStep table secretKey setup state message
        (fun signature updated =>
          compile table secretKey setup (next signature) updated)

noncomputable def start {α : Type} (table : PointTable)
    (secretKey : SecretKey) (interaction : Interaction α) :
    SecurityIndexProgram.Program (α × State) :=
  compile table secretKey (GroupedBalancedGraphMonitorSetup67.cache table)
    interaction {}

/-- The existing H5 monitor bounds the collision event in the exact joint
output law, while retaining the adversary's result and final residual cache. -/
theorem conflict_le {α : Type} (table : PointTable)
    (secretKey : SecretKey) (interaction : Interaction α) :
    Pr[fun result => SecurityIndexTrace.Conflict result.2 ∧
        SecurityIndexTrace.marks result.2 ≤ LIFETIME |
      SecurityIndexProgram.execute (start table secretKey interaction)] ≤
      OracleComp.EvalDist.expectedValue
        (SecurityIndexProgram.execute (start table secretKey interaction))
        (fun result => (result.2.length : ENNReal)) / 2 ^ 128 :=
  SecurityIndexProgram.prob_lifetime_conflict_le _

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexProgram67
