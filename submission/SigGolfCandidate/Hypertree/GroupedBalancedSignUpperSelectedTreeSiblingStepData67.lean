import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingStepFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeStepData67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedSiblingIndex67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingStepData67. -/
section
/-! The selected sibling slot fits the source table at each parent level. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedSiblingIndex67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def siblingIndex (s : MachineState) : Nat :=
  ((s.getMem 0x810e8 >>> ((s.getMem 0x81050).toNat%64)) ^^^
    (1:Word)).toNat

theorem index_eq (s : MachineState) (height selected : Nat)
    (heightSmall : height<64)
    (selectedSmall : selected<2^64)
    (selectedWord : s.getMem 0x810e8=BitVec.ofNat 64 selected)
    (levelWord : s.getMem 0x81050=BitVec.ofNat 64 height) :
    siblingIndex s=Nat.xor (selected/2^height) 1 := by
  unfold siblingIndex
  rw [BitVec.toNat_xor,levelWord,selectedWord,
    BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : height<2^64),
    Nat.mod_eq_of_lt heightSmall,Nat.mod_eq_of_lt selectedSmall]
  rw [show ((1:Word).toNat)=1 by decide]
  rfl

theorem index_bound (s : MachineState) (heightMax height selected : Nat)
    (maxSmall : heightMax≤4)
    (heightSmall : height<heightMax)
    (selectedWord : s.getMem 0x810e8=BitVec.ofNat 64 selected)
    (levelWord : s.getMem 0x81050=BitVec.ofNat 64 height)
    (selectedBound : selected<2^heightMax) :
    siblingIndex s < 2^(heightMax-height) := by
  have height64 : height<64 := by omega
  have selected64 : selected<2^64 := by
    have maxPower : 2^heightMax≤2^64 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have shift : (s.getMem 0x810e8 >>> ((s.getMem 0x81050).toNat%64)).toNat=
      selected/2^height := by
    rw [levelWord,selectedWord,BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat]
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : height<2^64),
      Nat.mod_eq_of_lt height64,Nat.mod_eq_of_lt selected64]
  have exp : 2^heightMax=2^height*2^(heightMax-height) := by
    rw [←pow_add]
    congr 1
    omega
  have divided : selected/2^height<2^(heightMax-height) := by
    apply (Nat.div_lt_iff_lt_mul (pow_pos (by decide) height)).2
    calc
      selected < 2^heightMax := selectedBound
      _ = 2^(heightMax-height)*2^height := by rw [exp]; ac_rfl
  have shiftedSmall :
      (s.getMem 0x810e8 >>> ((s.getMem 0x81050).toNat%64)).toNat <
        2^(heightMax-height) := by rw [shift]; exact divided
  unfold siblingIndex
  rw [BitVec.toNat_xor]
  have oneBound : ((1:Word).toNat)<2^(heightMax-height) := by
    have power : 2^1≤2^(heightMax-height) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have oneNat : ((1:Word).toNat)=1 := by decide
    rw [oneNat]
    exact lt_of_lt_of_le (by decide : 1<2) (by simpa using power)
  exact Nat.xor_lt_two_pow shiftedSmall oneBound

#print axioms index_bound
#print axioms index_eq
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedSiblingIndex67

end

/-! Current authentication sibling survives the parent level's transition. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingStepData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeLevelTrace67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev step := GroupedBalancedSignBottomTreeLevelControl67.transitionState
private abbrev siblingIndex :=
  GroupedBalancedSignUpperSelectedSiblingIndex67.siblingIndex

private theorem ne_high (a : Word) (low : a.toNat<0x80000)
    (b : Nat) (high : 0x80000≤b) (small : b<2^64) :
    a≠BitVec.ofNat 64 b := by
  intro eq
  have hn := congrArg BitVec.toNat eq
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at hn
  omega

theorem height_step_sibling (hash : Hash) (s next : MachineState)
    (heightMax treeBase witnessBase height limit source target : Nat)
    (sibling : Reference.Digest)
    (ready : Ready heightMax treeBase witnessBase height limit source target s)
    (heightBound : height+1<heightMax)
    (maxBound : heightMax=3 ∨ heightMax=4)
    (witnessBound : witnessBase+16*heightMax+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (positive : 0<limit) (small : limit≤8)
    (bases : (source=0x83000 ∧ target=0x88000) ∨
      (source=0x88000 ∧ target=0x83000))
    (sourceWords : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (source+16*siblingIndex s+8*i.val))=
        sibling.extractLsb' (64*i.val) 64)
    (trace : Trace hash image s
      (113+84*(limit-1)+85) (120+91*(limit-1)+85)
      limit limit next) :
    ∀ i : Fin 2,
      next.getMem (BitVec.ofNat 64 (witnessBase+16*height+8*i.val))=
        sibling.extractLsb' (64*i.val) 64 := by
  have hb : height<10 := by rcases maxBound with rfl|rfl <;> omega
  have hwb : witnessBase+16*height+16≤0x80000 := by omega
  obtain ⟨done,parentTrace,doneInv,parentFrame,_,_⟩ :=
    GroupedBalancedSignUpperTreeParentTrace67.first_level hash s height
      witnessBase limit source target ready.pc ready.levelWord ready.witness
      hb hwb witnessAligned ready.selectedBound ready.count ready.sourcePtr
      ready.targetPtr bases positive small
  have inputWords : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (source+16*
        (((s.getMem 0x810e8 >>> ((s.getMem 0x81050).toNat%64)) ^^^
          (1:Word)).toNat)+8*i.val))=
        sibling.extractLsb' (64*i.val) 64 := by
    simpa only [siblingIndex,
      GroupedBalancedSignUpperSelectedSiblingIndex67.siblingIndex] using
        sourceWords
  have doneSibling :=
    GroupedBalancedSignUpperSelectedTreeSiblingLevel67.first_level_sibling
      hash s done height witnessBase limit source target sibling ready.pc
      ready.levelWord ready.witness hb hwb witnessAligned
      ready.selectedBound ready.count ready.sourcePtr ready.targetPtr bases
      positive small inputWords parentTrace
  have doneLevel : done.getMem 0x81050=BitVec.ofNat 64 height := by
    rw [parentFrame 0x81050 ⟨by decide,by decide,by decide,by decide⟩]
    exact ready.levelWord
  have doneMax : done.getMem 0x81060=BitVec.ofNat 64 heightMax := by
    rw [parentFrame 0x81060 ⟨by decide,by decide,by decide,by decide⟩]
    exact ready.maxLevel
  let shifted := step done
  have transTrace : Trace hash image done 37 37 0 0 shifted :=
    (GroupedBalancedSignBottomTreeLevelControl67.transition_steps done
      doneInv.pc).trace
  have shiftedPc : shifted.pc=0x1e04 := by
    have h := GroupedBalancedSignUpperTreeLevelTrace67.transition_pc done
      heightMax height doneInv.pc doneLevel doneMax (by omega) maxBound
    rw [h]
    simp [Nat.ne_of_lt heightBound]
  obtain ⟨built,prelude,_,preludeFrame⟩ :=
    GroupedBalancedSignUpperTreePreludeTrace67.prelude shifted shiftedPc
  have builtTrace : Trace hash image s
      (113+84*(limit-1)+85) (120+91*(limit-1)+85)
      limit limit built := by
    have combined := (parentTrace.trans transTrace).trans
      (OrdinarySteps.trace (hash := hash) prelude)
    convert combined using 1 <;> omega
  have same := Trace.deterministic trace builtTrace
  intro i
  let a : Word := BitVec.ofNat 64 (witnessBase+16*height+8*i.val)
  have low : a.toNat<0x80000 := by
    simp only [a,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : witnessBase+16*height+8*i.val<2^64)]
    omega
  have ne (b : Nat) (high : 0x80000≤b) (small : b<2^64) :
      a≠BitVec.ofNat 64 b := ne_high a low b high small
  rw [same,
    preludeFrame a
      (ne 0x81008 (by decide) (by decide))
      (ne 0x81010 (by decide) (by decide))
      (ne 0x81018 (by decide) (by decide))
      (ne 0x810a8 (by decide) (by decide))
      (ne 0x810b0 (by decide) (by decide))
      (ne 0x810b8 (by decide) (by decide)),
    GroupedBalancedSignBottomTreeLevelData67.frame done a
      (ne 0x810c0 (by decide) (by decide))
      (ne 0x810c8 (by decide) (by decide))
      (ne 0x810d0 (by decide) (by decide))
      (ne 0x81000 (by decide) (by decide))
      (ne 0x81050 (by decide) (by decide))]
  exact doneSibling i

theorem terminal_sibling (hash : Hash) (s final : MachineState)
    (heightMax treeBase witnessBase height source target : Nat)
    (sibling : Reference.Digest)
    (ready : Ready heightMax treeBase witnessBase height 1 source target s)
    (terminalHeight : height+1=heightMax)
    (maxBound : heightMax=3 ∨ heightMax=4)
    (witnessBound : witnessBase+16*heightMax+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (bases : (source=0x83000 ∧ target=0x88000) ∨
      (source=0x88000 ∧ target=0x83000))
    (sourceWords : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (source+16*siblingIndex s+8*i.val))=
        sibling.extractLsb' (64*i.val) 64)
    (trace : Trace hash image s 150 157 1 1 final) :
    ∀ i : Fin 2,
      final.getMem (BitVec.ofNat 64 (witnessBase+16*height+8*i.val))=
        sibling.extractLsb' (64*i.val) 64 := by
  have hb : height<10 := by rcases maxBound with rfl|rfl <;> omega
  have hwb : witnessBase+16*height+16≤0x80000 := by omega
  obtain ⟨done,parentTrace,doneInv,_,_,_⟩ :=
    GroupedBalancedSignUpperTreeParentTrace67.first_level hash s height
      witnessBase 1 source target ready.pc ready.levelWord ready.witness
      hb hwb witnessAligned ready.selectedBound ready.count ready.sourcePtr
      ready.targetPtr bases (by decide) (by decide)
  have inputWords : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (source+16*
        (((s.getMem 0x810e8 >>> ((s.getMem 0x81050).toNat%64)) ^^^
          (1:Word)).toNat)+8*i.val))=
        sibling.extractLsb' (64*i.val) 64 := by
    simpa only [siblingIndex,
      GroupedBalancedSignUpperSelectedSiblingIndex67.siblingIndex] using
        sourceWords
  have doneSibling :=
    GroupedBalancedSignUpperSelectedTreeSiblingLevel67.first_level_sibling
      hash s done height witnessBase 1 source target sibling ready.pc
      ready.levelWord ready.witness hb hwb witnessAligned
      ready.selectedBound ready.count ready.sourcePtr ready.targetPtr bases
      (by decide) (by decide) inputWords parentTrace
  let shifted := step done
  have transTrace : Trace hash image done 37 37 0 0 shifted :=
    (GroupedBalancedSignBottomTreeLevelControl67.transition_steps done
      doneInv.pc).trace
  have builtTrace : Trace hash image s 150 157 1 1 shifted := by
    have combined := parentTrace.trans transTrace
    simpa only [Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub] using combined
  have same := Trace.deterministic trace builtTrace
  intro i
  let a : Word := BitVec.ofNat 64 (witnessBase+16*height+8*i.val)
  have low : a.toNat<0x80000 := by
    simp only [a,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : witnessBase+16*height+8*i.val<2^64)]
    omega
  have ne (b : Nat) (high : 0x80000≤b) (small : b<2^64) :
      a≠BitVec.ofNat 64 b := ne_high a low b high small
  rw [same,
    GroupedBalancedSignBottomTreeLevelData67.frame done a
      (ne 0x810c0 (by decide) (by decide))
      (ne 0x810c8 (by decide) (by decide))
      (ne 0x810d0 (by decide) (by decide))
      (ne 0x81000 (by decide) (by decide))
      (ne 0x81050 (by decide) (by decide))]
  exact doneSibling i

#print axioms height_step_sibling
#print axioms terminal_sibling
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingStepData67
