import SigGolfCandidate.Hypertree.GroupedBalancedGraphHonestSignView67

/-! A complete adaptive adversary-facing syntax with public hash, honest
signing, and private coin actions. Its signing branch compiles to two private
oracle reads and one bottom disclosure. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphInteraction67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphHonestSignView67
set_option maxRecDepth 8192
open scoped Classical

inductive Interaction (α : Type) where
  | done (value : α)
  | hash (input : Query) (next : BitVec 256 → Interaction α)
  | sign (message : Message)
      (next : GroupedBalancedScheme67.Signature → Interaction α)
  | coin (n : Nat) (next : Fin (n + 1) → Interaction α)

noncomputable def toView {α : Type} (secretKey : SecretKey)
    (cache : QueryCache PointSpec) : Interaction α → View α
  | .done value => .done value
  | .hash input next => .hash input (fun answer =>
      toView secretKey cache (next answer))
  | .sign message next => honestSign secretKey message cache (fun signature =>
      toView secretKey cache (next signature))
  | .coin n next => .coin n (fun answer =>
      toView secretKey cache (next answer))

theorem interaction_contact_le {α : Type} (secretKey : SecretKey)
    (interaction : QueryCache PointSpec → Interaction α)
    (remaining : Nat) :
    Pr[= none | do
      let table ← $ᵗ PointTable
      GroupedBalancedGraphMonitorSignCoupling67.execute table
        (toView secretKey (GroupedBalancedGraphMonitorSetup67.cache table)
          (interaction (GroupedBalancedGraphMonitorSetup67.cache table)))
        remaining
        (GroupedBalancedGraphMonitorSignBound67.initial
          (GroupedBalancedGraphMonitorSetup67.cache table))] ≤
      (2 * remaining : Nat) / (2 : ENNReal) ^ 128 :=
  GroupedBalancedGraphMonitorSignBound67.planted_from_cache_contact_le
    (fun cache => toView secretKey cache (interaction cache)) remaining

end SigGolfCandidate.Hypertree.GroupedBalancedGraphInteraction67
