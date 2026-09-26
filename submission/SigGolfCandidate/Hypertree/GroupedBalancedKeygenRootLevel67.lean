import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootFold67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenOneLevel67

/-! A direct67 H4 level computes all reference parents and swaps buffers. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootLevel67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenRootNodes67
set_option maxRecDepth 16384
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedKeygenImage67.image
private abbrev root := GroupedBalancedUpperTree67.root
private abbrev levelState := GroupedBalancedKeygenLevel67.levelState

theorem level_frame (s : MachineState) (a : Word)
    (ne78 : a ≠ 0x81078#64) (ne80 : a ≠ 0x81080#64)
    (ne70 : a ≠ 0x81070#64) (ne00 : a ≠ 0x81000#64)
    (ne50 : a ≠ 0x81050#64) :
    (levelState s).getMem a = s.getMem a := by
  simp [levelState,GroupedBalancedKeygenLevel67.levelState,
    execInstrBr,signExtend12,ne78,ne80,ne70,ne00,ne50,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem level_high (s : MachineState) (a : Word)
    (high : 0x82000 ≤ a.toNat) :
    (levelState s).getMem a = s.getMem a := by
  have ne (b : Nat) (small : b < 0x82000) : a ≠ BitVec.ofNat 64 b := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : b < 2^64)] at hn
    omega
  exact level_frame s a (ne 0x81078 (by decide)) (ne 0x81080 (by decide))
    (ne 0x81070 (by decide)) (ne 0x81000 (by decide))
    (ne 0x81050 (by decide))

theorem level_values (hash : Hash) (secretKey : SecretKey)
    (s : MachineState) (base ell k src dst : Nat)
    (pc : s.pc = 0x1480) (positive : 0 < k) (bound : k ≤ 8)
    (srcCase : src = 0x82000 ∨ src = 0x82100)
    (dstCase : dst = 0x82000 ∨ dst = 0x82100)
    (different : src ≠ dst)
    (index : s.getMem 0x81040#64 = 0#64)
    (count : s.getMem 0x81070#64 = BitVec.ofNat 64 k)
    (source : s.getMem 0x81078#64 = BitVec.ofNat 64 src)
    (destination : s.getMem 0x81080#64 = BitVec.ofNat 64 dst)
    (treeLevel : s.getMem 0x81050#64 = BitVec.ofNat 64 ell)
    (levelWord : s.getMem 0x81000 = BitVec.ofNat 64 (base+ell))
    (index1 : s.getMem 0x81010 = 0#64)
    (index2 : s.getMem 0x81018 = 0#64)
    (table : ∀ j : Nat, j < 2*k → ∀ i : Fin 2,
      s.getMem (Signing.wordAddress (src+16*j) i.val) =
        (root hash secretKey base ell j).extractLsb' (64*i.val) 64) :
    ∃ final,
      Trace hash image s (79*k+35) (86*k+35) k k final ∧
      final.pc = (if BitVec.ofNat 64 ell + 1 = 4 then 0x1648 else 0x1470) ∧
      final.getMem 0x81070#64 = BitVec.ofNat 64 k >>> 1 ∧
      final.getMem 0x81078#64 = BitVec.ofNat 64 dst ∧
      final.getMem 0x81080#64 = BitVec.ofNat 64 src ∧
      final.getMem 0x81050#64 = BitVec.ofNat 64 ell + 1 ∧
      final.getMem 0x81000 = BitVec.ofNat 64 (base+ell+1) ∧
      final.getMem 0x81010 = 0#64 ∧
      final.getMem 0x81018 = 0#64 ∧
      (∀ j : Nat, j < k → ∀ i : Fin 2,
        final.getMem (Signing.wordAddress (dst+16*j) i.val) =
          (root hash secretKey base (ell+1) j).extractLsb' (64*i.val) 64) := by
  obtain ⟨nodes,first,nodesPC,nodesIndex,nodesLow,nodesOutput,_⟩ :=
    GroupedBalancedKeygenRootFold67.nodes_values hash secretKey s
      base ell 0 k src dst pc positive (by simpa using bound)
      srcCase dstCase different (by simpa using index)
      (by simpa using count) source destination levelWord index1 index2
      (by simpa using table)
  have nodesControl (a : Word) (high : 0x81000 ≤ a.toNat)
      (low : a.toNat < 0x82000) (ne08 : a ≠ 0x81008#64)
      (ne40 : a ≠ 0x81040#64) : nodes.getMem a = s.getMem a :=
    nodesLow a high low ne08 ne40
  let final := levelState nodes
  have second : Trace hash image nodes 35 35 0 0 final :=
    (GroupedBalancedKeygenLevel67.level_steps nodes nodesPC).trace
  obtain ⟨srcNext,dstNext,countNext,levelNext,treeNext,_⟩ :=
    GroupedBalancedKeygenLevel67.level_controls nodes
  have nodeTree : nodes.getMem 0x81050#64 = BitVec.ofNat 64 ell := by
    rw [nodesControl 0x81050#64 (by decide) (by decide) (by decide) (by decide)]
    exact treeLevel
  refine ⟨final,by simpa only [Nat.add_assoc,Nat.add_zero] using first.trans second,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [GroupedBalancedKeygenLevel67.level_pc nodes nodesPC,nodeTree]
  · rw [countNext,nodesControl 0x81070#64 (by decide) (by decide)
      (by decide) (by decide),count]
  · rw [srcNext,nodesControl 0x81080#64 (by decide) (by decide)
      (by decide) (by decide),destination]
  · rw [dstNext,nodesControl 0x81078#64 (by decide) (by decide)
      (by decide) (by decide),source]
  · rw [treeNext,nodeTree]
  · have lit : (0x81000#64 : Word) = (0x81000 : Word) := by decide
    rw [←lit,levelNext,nodesControl 0x81000#64 (by decide) (by decide)
      (by decide) (by decide)]
    rw [lit,levelWord]
    simp [BitVec.ofNat_add]
  · rw [level_frame nodes 0x81010 (by decide) (by decide) (by decide)
      (by decide) (by decide),nodesControl 0x81010 (by decide) (by decide)
      (by decide) (by decide)]
    exact index1
  · rw [level_frame nodes 0x81018 (by decide) (by decide) (by decide)
      (by decide) (by decide),nodesControl 0x81018 (by decide) (by decide)
      (by decide) (by decide)]
    exact index2
  · intro j jBound i
    rw [level_high nodes (Signing.wordAddress (dst+16*j) i.val)
      (table_word_high dst j i dstCase (by omega))]
    exact nodesOutput j (by omega) (by simpa using jBound) i

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootLevel67
