import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorTable67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorProgram67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphQuery67


/-! Parse a public chain address to the unique private or public 128-bit
predecessor consumed by its canonical payload. Ghost chain addresses have no
predecessor and carry the empty payload. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorPredecessor67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPayload67 GroupedBalancedGraphPassive67

def predecessor (address : SecurityGraph.Address) : Option Point :=
  if hbottom : address.level.val = 0 ∧ address.leaf.val = 0 ∧
      address.chain.val = 0 ∧ address.step.val = 0 then
    some (.inr (.inl (BitVec.ofNat 160 address.tree.toNat)))
  else if hlevel : 10 ≤ address.level.val ∧ address.level.val < 160 then
    if hleaf : address.leaf.val = 0 then
      if hchain : address.chain.val < 67 then
        if hstep : address.step.val < 10 then
          let base : Fin 150 := ⟨address.level.val - 10, by omega⟩
          let leaf : BitVec 160 := BitVec.ofNat 160 address.tree.toNat
          let chain : Fin 67 := ⟨address.chain.val, hchain⟩
          if zero : address.step.val = 0 then
            some (.inr (.inr ((base, leaf), chain)))
          else
            some (.inl (upperChain base leaf chain
              ⟨address.step.val - 1, by omega⟩))
        else none
      else none
    else none
  else none

theorem chain_payload_eq (table : PointTable)
    (address : SecurityGraph.Address) :
    chainPayload (GroupedBalancedGraphMonitorTable67.privateOf table)
      (GroupedBalancedGraphMonitorTable67.labelsOf table) address =
      match predecessor address with
      | none => []
      | some point => bytes (truncate (table point)) := by
  unfold chainPayload predecessor
  split_ifs with bottom level leaf chainBound stepBound zero
  · rfl
  · simpa only using congrArg bytes
      (GroupedBalancedGraphMonitorTable67.upper_source table
        ⟨address.level.val - 10, by omega⟩
        (BitVec.ofNat 160 address.tree.toNat)
        ⟨address.chain.val, chainBound⟩)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorPredecessor67


/-! Output-retaining passive monitor for one grouped public oracle call. A
chain query tests at most one hidden 128-bit predecessor and one independent
output collision. Leaf and node queries open only terminal or metadata
children, then test at most one output collision. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorOracle67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorPredecessor67
open scoped Classical

def knownTable (exposed : QueryCache PointSpec) : PointTable :=
  fun point => (exposed point).getD 0

def required (position : Position) : List Point :=
  if position.val.tag.val = 3 then
    if hlevel : 10 ≤ position.val.level.val ∧ position.val.level.val < 160 then
      let base : Fin 150 := ⟨position.val.level.val - 10, by omega⟩
      let leaf : BitVec 160 := BitVec.ofNat 160 position.val.tree.toNat
      List.ofFn (fun chain : Fin 67 =>
        .inl (upperChain base leaf chain (endpointStep chain)))
    else []
  else if position.val.tag.val = 4 ∧ position.val.level.val < 160 then
    [.inl (GroupedBalancedGraphPayload67.nodeChildren position.val).1,
      .inl (GroupedBalancedGraphPayload67.nodeChildren position.val).2]
  else []

def revealCache (table : PointTable) : List Point →
    QueryCache PointSpec → QueryCache PointSpec
  | [], exposed => exposed
  | point :: rest, exposed =>
      revealCache table rest (exposed.cacheQuery point (table point))

noncomputable def disclose {α : Type} : List Point → QueryCache PointSpec →
    (QueryCache PointSpec → Program α) → Program α
  | [], exposed, next => next exposed
  | point :: rest, exposed, next => .reveal point (fun answer =>
      disclose rest (exposed.cacheQuery point answer) next)

noncomputable def residualStep {α : Type}
    (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec)
    (query : Query) (target : Point)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    Program α :=
  match residual query with
  | some answer => next answer exposed residual
  | none => match exposed target with
    | some known => .collision (truncate known) (fun answer =>
        next answer exposed (residual.cacheQuery query answer))
    | none => .bits (fun answer => .guess target (truncate answer)
        (next answer exposed (residual.cacheQuery query answer)))

noncomputable def parsedChainPayload (position : Position) (query : Query) :
    Option Digest :=
  if found : ∃ point, query = position.input (bytes point)
  then some found.choose else none

noncomputable def chainStep {α : Type}
    (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec)
    (position : Position) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    Program α :=
  match predecessor position.val with
  | none =>
      if query = position.input [] then
        .reveal (.inl position) (fun answer =>
          next answer (exposed.cacheQuery (.inl position) answer) residual)
      else residualStep exposed residual query (.inl position) next
  | some previous =>
      match parsedChainPayload position query with
      | none => residualStep exposed residual query (.inl position) next
      | some point => match exposed previous with
        | none => .guess previous point
            (residualStep exposed residual query (.inl position) next)
        | some known =>
            if point = truncate known then
              .reveal (.inl position) (fun answer =>
                next answer (exposed.cacheQuery (.inl position) answer) residual)
            else residualStep exposed residual query (.inl position) next

noncomputable def publicStep {α : Type}
    (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec)
    (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    Program α :=
  match GroupedBalancedGraphQuery67.locate query with
  | none => match residual query with
      | some answer => next answer exposed residual
      | none => .bits (fun answer =>
          next answer exposed (residual.cacheQuery query answer))
  | some position =>
      if position.val.tag.val = 2 then
        chainStep exposed residual position query next
      else
        disclose (required position) exposed (fun opened =>
          let payload := GroupedBalancedGraphPayload67.payload
            (GroupedBalancedGraphMonitorTable67.privateOf (knownTable opened))
            (GroupedBalancedGraphMonitorTable67.labelsOf (knownTable opened)) position
          if query = position.input payload then
            .reveal (.inl position) (fun answer =>
              next answer (opened.cacheQuery (.inl position) answer) residual)
          else residualStep opened residual query (.inl position) next)

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorOracle67
