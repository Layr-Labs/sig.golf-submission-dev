import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootTree67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsLeavesFold67
import SigGolfCandidate.Hypertree.GroupedBalancedScheme67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalLeavesFold67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootPriorLeavesFrame67


/-! Once the sixteen leaf words are established, the actual H4 trace yields keygen. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootFunctionalHandoff67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem root_after_leaves (hash : Hash) (secretKey : SecretKey)
    (s leaves : MachineState)
    (pc : s.pc = 0x1000)
    (prefixTrace : Trace hash image s 189680 219632 3968 4240 leaves)
    (leafTable : ∀ j : Nat, j < 16 → ∀ i : Fin 2,
      leaves.getMem (Signing.wordAddress (0x82000+16*j) i.val) =
        (GroupedBalancedUpperTree67.root hash secretKey 156 0 j).extractLsb'
          (64*i.val) 64) :
    ∃ final, Trace hash image s 191039 221096 3983 4255 final ∧
      final.pc = 0x1648 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x82000 i.val) =
          (GroupedBalancedScheme67.keygen hash secretKey).extractLsb'
            (64*i.val) 64) ∧
      final.getMem 0x81078#64 = 0x82000#64 := by
  obtain ⟨known,knownTrace,knownPC,_,knownLevel⟩ :=
    GroupedBalancedKeygenLeavesFold67.entry_sixteen_leaves hash s pc
  have same : leaves = known := Trace.deterministic prefixTrace knownTrace
  have leafPC : leaves.pc = 0x1428 := by rw [same]; exact knownPC
  have leafLevel : leaves.getMem 0x81000 = 156 := by
    rw [same]
    exact knownLevel
  obtain ⟨idx1,idx2⟩ :=
    GroupedBalancedKeygenRootControlsLeavesFold67.entry_sixteen_controls
      hash s leaves pc prefixTrace
  obtain ⟨final,treeTrace,finalPC,sourceBase,_,rootWords⟩ :=
    GroupedBalancedKeygenRootTree67.tree_values hash secretKey leaves
      leafPC leafLevel idx1 idx2 leafTable
  refine ⟨final,?_,finalPC,?_,sourceBase⟩
  · simpa only [Nat.reduceAdd] using prefixTrace.trans treeTrace
  · intro i
    simpa only [GroupedBalancedScheme67.keygen] using rootWords i

#print axioms root_after_leaves
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootFunctionalHandoff67



/-! Connect the concrete H1–H3 leaf fold to the concrete H4 top root. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalHandoff67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenLeafFunctionalLeavesFold67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem keygen_root_under_safety (hash : Hash) (secretKey : SecretKey)
    (safety : LeafSafety hash secretKey)
    (s : MachineState) (pc : s.pc = 0x1000)
    (source : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    ∃ final, Trace hash image s 191039 221096 3983 4255 final ∧
      final.pc = 0x1648 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x82000 i.val) =
          (GroupedBalancedScheme67.keygen hash secretKey).extractLsb'
            (64*i.val) 64) ∧
      final.getMem 0x81078#64 = 0x82000#64 := by
  obtain ⟨leaves,first,roots⟩ :=
    entry_sixteen_leaves hash secretKey safety s pc source
  apply GroupedBalancedKeygenRootFunctionalHandoff67.root_after_leaves
    hash secretKey s leaves pc first
  intro j bound i
  have address : Signing.wordAddress (0x82000+16*j) i.val =
      Signing.wordAddress 0x82000 (2*j+i.val) := by
    change BitVec.ofNat 64 (0x82000+16*j+8*i.val) =
      BitVec.ofNat 64 (0x82000+8*(2*j+i.val))
    congr 1
    omega
  rw [address]
  simpa only [GroupedBalancedUpperTree67.root] using
    roots ⟨j,bound⟩ i

#print axioms keygen_root_under_safety

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalHandoff67


/-! The concrete keygen image computes the reference public root. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalSafety67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenLeafFunctionalFold67
open GroupedBalancedKeygenLeafFunctionalLeavesFold67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem safe_of_far (n : Nat) (bound : n < 16)
    (s t : MachineState)
    (far : GroupedBalancedKeygenRootPriorLeavesFrame67.SafeFrame n s t) :
    GroupedBalancedKeygenLeafFunctionalLeavesFold67.SafeFrame n s t := by
  constructor
  · intro a low
    exact far a (Or.inl (by omega))
  · intro j old i
    apply far
    right
    have range : 0x82000 ≤
        (Signing.wordAddress 0x82000 (2*j.val+i.val)).toNat ∧
        (Signing.wordAddress 0x82000 (2*j.val+i.val)).toNat <
          0x82000+16*n := by
      simp only [Signing.wordAddress,BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by have := j.isLt; have := i.isLt; omega)]
      have := i.isLt
      omega
    exact range

theorem leaf_safety (hash : Hash) (secretKey : SecretKey) :
    LeafSafety hash secretKey := by
  constructor
  · intro n bound s even final trace
    have leaf := leaf_counter_word s n (by omega) even.address
    have far :=
      GroupedBalancedKeygenRootPriorLeavesFrame67.regular_leaf_safe
        hash s final n even.pc bound
        (by simpa using even.counter) leaf even.level trace
    exact safe_of_far n (by omega) s final far
  · intro s even final trace
    have leaf := leaf_counter_word s 15 (by decide) even.address
    have far :=
      GroupedBalancedKeygenRootPriorLeavesFrame67.last_leaf_safe
        hash s final even.pc (by simpa using even.counter)
        (by simpa using leaf) even.level trace
    exact safe_of_far 15 (by decide) s final far

theorem keygen_root (hash : Hash) (secretKey : SecretKey)
    (s : MachineState) (pc : s.pc = 0x1000)
    (source : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    ∃ final, Trace hash image s 191039 221096 3983 4255 final ∧
      final.pc = 0x1648 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x82000 i.val) =
          (GroupedBalancedScheme67.keygen hash secretKey).extractLsb'
            (64*i.val) 64) ∧
      final.getMem 0x81078#64 = 0x82000#64 :=
  GroupedBalancedKeygenLeafFunctionalHandoff67.keygen_root_under_safety
    hash secretKey (leaf_safety hash secretKey) s pc source

#print axioms safe_of_far
#print axioms leaf_safety
#print axioms keygen_root

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalSafety67
