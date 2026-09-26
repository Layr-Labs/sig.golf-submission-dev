import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstLevelData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelPrelude67
import SigGolfCandidate.TraceDeterminism

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeNextData67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeStepData67. -/
section
/-! Table and 192-bit address transfer to the next upper parent row. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeNextData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeParentData67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev step := GroupedBalancedSignBottomTreeLevelControl67.transitionState
private abbrev node := GroupedBalancedSignUpperTreeModel67.nodeAt

theorem next_data (hash : Hash) (treeBase leafBase : Nat)
    (leaves : Nat → Reference.Digest)
    (height limit source target addressBase : Nat) (s : MachineState)
    (params : Params leafBase height limit source target addressBase)
    (done : Done hash treeBase leafBase leaves height limit source target
      addressBase s)
    (midPc : (step s).pc=0x1e04)
    (even : 2*(limit/2)=limit) :
    ∃ t : MachineState,
      Trace hash image s 85 85 0 0 t ∧
      (∀ i : Fin 3,
        t.getMem (Signing.wordAddress 0x81008 i.val)=
          (BitVec.ofNat 192 (addressBase/2)).extractLsb'
            (64*i.val) 64) ∧
      (∀ i : Fin 3,
        t.getMem (Signing.wordAddress 0x810a8 i.val)=
          (BitVec.ofNat 192 (addressBase/2)).extractLsb'
            (64*i.val) 64) ∧
      (∀ j, j<2*(limit/2) → ∀ i : Fin 2,
        t.getMem (BitVec.ofNat 64 (target+16*j+8*i.val))=
          (node hash treeBase leafBase leaves (height+1) j).extractLsb'
            (64*i.val) 64) := by
  have transTrace : Trace hash image s 37 37 0 0 (step s) :=
    (GroupedBalancedSignBottomTreeLevelControl67.transition_steps s
      done.pc).trace
  have beforeScratch : ∀ i : Fin 3,
      (step s).getMem (Signing.wordAddress 0x810a8 i.val)=
        (BitVec.ofNat 192 addressBase).extractLsb' (64*i.val) 64 := by
    intro i
    rw [GroupedBalancedSignBottomTreeLevelData67.frame s _
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)]
    exact done.scratch i
  obtain ⟨t,prelude,_,addressWords,scratchWords,preludeFrame⟩ :=
    GroupedBalancedSignBottomTreeLevelPrelude67.level_prelude
      (step s) (BitVec.ofNat 192 addressBase) midPc beforeScratch
  have shifted : (BitVec.ofNat 192 addressBase >>> 1)=
      BitVec.ofNat 192 (addressBase/2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    norm_num
    have := params.addressBound
    omega
  have sourceWords : ∀ j, j<2*(limit/2) → ∀ i : Fin 2,
      t.getMem (BitVec.ofNat 64 (target+16*j+8*i.val))=
        (node hash treeBase leafBase leaves (height+1) j).extractLsb'
          (64*i.val) 64 := by
    intro j hj i
    have jBound : j<limit := by omega
    have targetRange : 0x83000≤target ∧ target≤0x88000 := by
      rcases params.bases with ⟨_,rfl⟩|⟨_,rfl⟩ <;> omega
    let a : Word := BitVec.ofNat 64 (target+16*j+8*i.val)
    have nat : a.toNat=target+16*j+8*i.val := by
      simp only [a,BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by have := params.small.2; omega)
    have ne (b : Word) (low : b.toNat<0x83000) : a≠b := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      rw [nat] at hn
      omega
    have transFrame : (step s).getMem a=s.getMem a :=
      GroupedBalancedSignBottomTreeLevelData67.frame s a
        (ne 0x810c0 (by decide)) (ne 0x810c8 (by decide))
        (ne 0x810d0 (by decide)) (ne 0x81000 (by decide))
        (ne 0x81050 (by decide))
    rw [preludeFrame a (ne 0x81008 (by decide))
      (ne 0x81010 (by decide)) (ne 0x81018 (by decide))
      (ne 0x810a8 (by decide)) (ne 0x810b0 (by decide))
      (ne 0x810b8 (by decide)),transFrame]
    exact done.targetWords j jBound i
  refine ⟨t,?_,?_,?_,sourceWords⟩
  · have both := transTrace.trans (OrdinarySteps.trace (hash := hash) prelude)
    convert both using 1 <;> decide
  · intro i
    rw [addressWords i,shifted]
  · intro i
    rw [scratchWords i,shifted]

#print axioms next_data
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeNextData67

end

/-! One upper parent row, table swap, and the next functional row invariant. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeStepData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeParentData67
open GroupedBalancedSignUpperTreeFirstLevelData67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev node := GroupedBalancedSignUpperTreeModel67.nodeAt

theorem params_next (leafBase height limit source target addressBase : Nat)
    (params : Params leafBase height limit source target addressBase)
    (halfPositive : 0<limit/2)
    (halfCase : limit/2=1 ∨ limit/2=2 ∨ limit/2=4 ∨ limit/2=8)
    (even : 2*(limit/2)=limit) :
    Params leafBase (height+1) (limit/2) target source (addressBase/2) := by
  have addressNext : addressBase/2=leafBase/2^((height+1)+1) := by
    rw [params.addressDef,Nat.div_div_eq_div_mul]
    simp only [pow_succ]
  have alignedNext : (addressBase/2)%(limit/2)=0 := by
    obtain ⟨k,hk⟩ := Nat.dvd_of_mod_eq_zero params.addressAligned
    rw [hk,←even]
    have div : (2*(limit/2)*k)/2=(limit/2)*k := by
      rw [mul_assoc]
      simp [Nat.mul_comm]
    rw [div]
    simp
  have boundNext : addressBase/2+limit/2<2^160 := by
    have := params.addressBound
    have aLe := Nat.div_le_self addressBase 2
    have lLe := Nat.div_le_self limit 2
    omega
  refine ⟨⟨halfPositive,by have := params.small.2; omega⟩,
    halfCase,alignedNext,addressNext,boundNext,?_⟩
  rcases params.bases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact Or.inr ⟨rfl,rfl⟩
  · exact Or.inl ⟨rfl,rfl⟩

theorem height_step_data (hash : Hash) (treeBase leafBase : Nat)
    (leaves : Nat → Reference.Digest)
    (heightMax witnessBase height limit source target addressBase : Nat)
    (s : MachineState)
    (params : Params leafBase height limit source target addressBase)
    (start : Start hash treeBase leafBase leaves heightMax witnessBase height
      limit source target addressBase s)
    (heightBound : height+1<heightMax)
    (maxBound : heightMax=3 ∨ heightMax=4)
    (treeBound : treeBase+heightMax<2^64)
    (witnessBound : witnessBase+16*heightMax+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (even : 2*(limit/2)=limit)
    (halfPositive : 0<limit/2)
    (halfCase : limit/2=1 ∨ limit/2=2 ∨ limit/2=4 ∨ limit/2=8) :
    ∃ next : MachineState,
      Trace hash image s (113+84*(limit-1)+85)
        (120+91*(limit-1)+85) limit limit next ∧
      Params leafBase (height+1) (limit/2) target source (addressBase/2) ∧
      Start hash treeBase leafBase leaves heightMax witnessBase (height+1)
        (limit/2) target source (addressBase/2) next := by
  have levelBound : height<10 := by
    rcases maxBound with rfl|rfl <;> omega
  have shortWitness : witnessBase+16*height+16≤0x80000 := by omega
  obtain ⟨done,levelTrace,doneInv⟩ := one_level hash treeBase leafBase leaves
    heightMax witnessBase height limit source target addressBase s params start
    levelBound shortWitness witnessAligned
  obtain ⟨other,otherTrace,_,parentFrame,_,_⟩ :=
    GroupedBalancedSignUpperTreeParentTrace67.first_level hash s height
      witnessBase limit source target start.ready.pc start.ready.levelWord
      start.ready.witness levelBound shortWitness witnessAligned
      start.ready.selectedBound start.ready.count start.ready.sourcePtr
      start.ready.targetPtr params.bases params.small.1 params.small.2
  have same := Trace.deterministic levelTrace otherTrace
  have doneLevel : done.getMem 0x81050=BitVec.ofNat 64 height := by
    rw [same,parentFrame 0x81050 ⟨by decide,by decide,by decide,by decide⟩]
    exact start.ready.levelWord
  have doneMax : done.getMem 0x81060=BitVec.ofNat 64 heightMax := by
    rw [same,parentFrame 0x81060 ⟨by decide,by decide,by decide,by decide⟩]
    exact start.ready.maxLevel
  have midPc := GroupedBalancedSignUpperTreeLevelTrace67.transition_pc
    done heightMax height doneInv.pc doneLevel doneMax (by omega) maxBound
  have midPc' : (GroupedBalancedSignBottomTreeLevelControl67.transitionState
      done).pc=0x1e04 := by
    rw [midPc]
    simp [Nat.ne_of_lt heightBound]
  obtain ⟨built,midTrace,builtAddress,builtScratch,builtSource⟩ :=
    GroupedBalancedSignUpperTreeNextData67.next_data hash treeBase leafBase
      leaves height limit source target addressBase done params doneInv midPc'
      even
  obtain ⟨next,wholeTrace,nextReady,_,_⟩ :=
    GroupedBalancedSignUpperTreeLevelTrace67.height_step hash s heightMax
      treeBase witnessBase height limit source target start.ready heightBound
      maxBound treeBound witnessBound witnessAligned params.small.1
      params.small.2 params.bases
  have sameNext : next=built := by
    have combined : Trace hash image s (113+84*(limit-1)+85)
        (120+91*(limit-1)+85) limit limit built := by
      convert levelTrace.trans midTrace using 1 <;> omega
    exact Trace.deterministic wholeTrace combined
  have pnext := params_next leafBase height limit source target addressBase
    params halfPositive halfCase even
  refine ⟨next,wholeTrace,pnext,⟨nextReady,?_,?_,?_⟩⟩
  · rw [sameNext]
    exact builtAddress
  · rw [sameNext]
    exact builtSource
  · rw [sameNext]
    exact builtScratch

#print axioms params_next
#print axioms height_step_data
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeStepData67
