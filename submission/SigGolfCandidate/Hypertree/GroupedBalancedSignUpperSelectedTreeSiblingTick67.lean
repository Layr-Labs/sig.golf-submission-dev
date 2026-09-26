import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeTickFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstLevelData67

/-! The first tick of an upper Merkle level copies the selected authentication
sibling from the source table into the signature witness region. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingTick67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev select := GroupedBalancedSignBottomTreeSelectPtr67.selectState
private abbrev copy (s : MachineState) :=
  GroupedBalancedSignBottomTreeSelectCopy67.copyState (select s)
private abbrev pair (s : MachineState) :=
  GroupedBalancedSignBottomTreePairPtr67.pairState (copy s)
private abbrev children (s : MachineState) :=
  GroupedBalancedSignBottomTreeChildData67.childrenState (pair s)
private abbrev ready (s : MachineState) :=
  GroupedBalancedSignBottomTreeH4Prelude67.preludeState (children s)
private abbrev hashed := GroupedBalancedSignBottomTreeFirstTickData67.hashed
private abbrev stored := GroupedBalancedSignBottomTreeFirstTickData67.stored
private abbrev tick := GroupedBalancedSignBottomTreeFirstTickData67.tickState

private theorem ne_high (a : Word) (low : a.toNat<0x80000)
    (b : Nat) (high : 0x80000≤b) (small : b<2^64) :
    a≠BitVec.ofNat 64 b := by
  intro eq
  have hn := congrArg BitVec.toNat eq
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at hn
  omega

theorem tick_from_copy (hash : Hash) (s : MachineState)
    (level witnessBase target : Nat) (a : Word)
    (levelWord : s.getMem 0x81050=BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (levelBound : level<10)
    (witnessBound : witnessBase+16*level+16≤0x80000)
    (destination : s.getMem 0x810c8=BitVec.ofNat 64 target)
    (targetCase : target=0x83000 ∨ target=0x88000)
    (low : a.toNat<0x80000) :
    (tick hash s).getMem a=(copy s).getMem a := by
  have pairFrame : (pair s).getMem a=(copy s).getMem a :=
    GroupedBalancedSignBottomTreePairStartData67.initial_frame _ a
      (ne_high a low 0x810d8 (by decide) (by decide))
  have childFrame : (children s).getMem a=(pair s).getMem a :=
    GroupedBalancedSignBottomTreeChildData67.frame _ a
      (ne_high a low 0x80020 (by decide) (by decide))
      (ne_high a low 0x80028 (by decide) (by decide))
      (ne_high a low 0x80030 (by decide) (by decide))
      (ne_high a low 0x80038 (by decide) (by decide))
  have readyFrame : (ready s).getMem a=(children s).getMem a :=
    GroupedBalancedSignBottomTreeH4Prelude67.prelude_frame _ a
      (ne_high a low 0x80000 (by decide) (by decide))
      (ne_high a low 0x80008 (by decide) (by decide))
      (ne_high a low 0x80010 (by decide) (by decide))
      (ne_high a low 0x80018 (by decide) (by decide))
  have answerFrame : (hashed hash s).getMem a=(ready s).getMem a := by
    have args := GroupedBalancedSignBottomTreeH4Prelude67.prelude_hash_args
      (children s)
    apply Signing.hash_answer_frame (ready s) (hash (hashInput (ready s)))
      args.2.2.1 a
    intro i eq
    exact ne_high a low (0x80300+8*i.val) (by omega) (by omega) eq
  have ptr := GroupedBalancedSignUpperTreeFirstTick67.output_pointer
    hash s level witnessBase target levelWord witness levelBound
      witnessBound destination
  have noOutput0 : a≠
      (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
        (hashed hash s)).getReg .x7 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [ptr,BitVec.toNat_ofNat] at hn
    rcases targetCase with rfl | rfl <;> omega
  have noOutput8 : a≠
      (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
        (hashed hash s)).getReg .x7+8 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [BitVec.toNat_add,ptr,BitVec.toNat_ofNat] at hn
    have eight : (8:Word).toNat=8 := by decide
    rw [eight] at hn
    rcases targetCase with rfl | rfl <;>
      norm_num at hn <;> omega
  have storedFrame : (stored hash s).getMem a=(hashed hash s).getMem a :=
    GroupedBalancedSignBottomTreeStoreData67.stored_frame
      (hashed hash s) a noOutput0 noOutput8
  have advFrame :
      (GroupedBalancedSignBottomTreeFirstTickData67.advanced hash s).getMem a=
        (stored hash s).getMem a :=
    GroupedBalancedSignBottomTreeParentControl67.advance_frame _ a
      (ne_high a low 0x81008 (by decide) (by decide))
      (ne_high a low 0x810d8 (by decide) (by decide))
  change (GroupedBalancedSignBottomTreeParentControl67.branchState
    (GroupedBalancedSignBottomTreeFirstTickData67.advanced hash s)).getMem a = _
  rw [GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    advFrame,storedFrame]
  exact answerFrame.trans (readyFrame.trans (childFrame.trans pairFrame))

theorem tick_sibling (hash : Hash) (s : MachineState)
    (level witnessBase sourceBase target : Nat)
    (sibling : Reference.Digest)
    (levelWord : s.getMem 0x81050=BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (levelBound : level<10)
    (witnessBound : witnessBase+16*level+16≤0x80000)
    (selectedBound : (s.getMem 0x810e8).toNat<1024)
    (source : s.getMem 0x810c0=BitVec.ofNat 64 sourceBase)
    (sourceCase : sourceBase=0x83000 ∨ sourceBase=0x88000)
    (destination : s.getMem 0x810c8=BitVec.ofNat 64 target)
    (targetCase : target=0x83000 ∨ target=0x88000)
    (sourceWords : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (sourceBase+16*
        (((s.getMem 0x810e8 >>> ((s.getMem 0x81050).toNat%64)) ^^^
          (1:Word)).toNat)+8*i.val)) = sibling.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (tick hash s).getMem (BitVec.ofNat 64 (witnessBase+16*level+8*i.val))=
        sibling.extractLsb' (64*i.val) 64 := by
  intro i
  let dst : Word := BitVec.ofNat 64 (witnessBase+16*level+8*i.val)
  have dstLow : dst.toNat<0x80000 := by
    simp only [dst,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : witnessBase+16*level+8*i.val<2^64)]
    omega
  rw [tick_from_copy hash s level witnessBase target dst levelWord witness
    levelBound witnessBound destination targetCase dstLow]
  have destNat := GroupedBalancedSignUpperTreeSelect67.destination_nat s
    level witnessBase levelWord witness levelBound witnessBound
  have srcNat := GroupedBalancedSignBottomTreeSelectData67.selected_source_nat
    s sourceBase source sourceCase selectedBound
  have dstEq : dst = (select s).getReg .x7 + BitVec.ofNat 64 (8*i.val) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add,destNat,BitVec.toNat_ofNat]
    simp only [dst,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : witnessBase+16*level+8*i.val<2^64)]
    rw [Nat.mod_eq_of_lt (by omega : 8*i.val<2^64),
      Nat.mod_eq_of_lt (by omega : witnessBase+16*level+8*i.val<2^64)]
  have srcEq : (select s).getReg .x6+BitVec.ofNat 64 (8*i.val) =
      BitVec.ofNat 64 (sourceBase+16*
        (((s.getMem 0x810e8 >>> ((s.getMem 0x81050).toNat%64)) ^^^
          (1:Word)).toNat)+8*i.val) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add,srcNat,BitVec.toNat_ofNat]
    simp only [BitVec.toNat_ofNat]
    have idxBound := GroupedBalancedSignBottomTreeSelectData67.selected_index_bound
      s selectedBound
    rw [Nat.mod_eq_of_lt (by omega : 8*i.val<2^64),
      Nat.mod_eq_of_lt (by
        rcases sourceCase with rfl | rfl <;> omega :
        sourceBase+16*
          (((s.getMem 0x810e8 >>> ((s.getMem 0x81050).toNat%64)) ^^^
            (1:Word)).toNat)+8*i.val<2^64)]
    change (sourceBase+16*
      (((s.getMem 0x810e8 >>> ((s.getMem 0x81050).toNat%64)) ^^^
        (1:Word)).toNat)+8*i.val)%2^64 = _
    rw [Nat.mod_eq_of_lt (by
      rcases sourceCase with rfl | rfl <;> omega)]
  fin_cases i
  · rw [dstEq]
    have notSame : (select s).getReg .x7≠(select s).getReg .x7+8 := by
        intro eq
        have hn := congrArg BitVec.toNat eq
        rw [destNat,BitVec.toNat_add,destNat] at hn
        have eight : (8:Word).toNat=8 := by decide
        rw [eight,Nat.mod_eq_of_lt (by omega : witnessBase+16*level+8<2^64)] at hn
        omega
    have copied := GroupedBalancedSignBottomTreeSelectData67.copied_low
      s notSame
    have src0 : (select s).getReg .x6 =
        BitVec.ofNat 64 (sourceBase+16*
          (((s.getMem 0x810e8 >>> ((s.getMem 0x81050).toNat%64)) ^^^
            (1:Word)).toNat)) := by simpa using srcEq
    rw [src0] at copied
    simpa using copied.trans (sourceWords (0 : Fin 2))
  · rw [dstEq]
    have copied := GroupedBalancedSignBottomTreeSelectData67.copied_high s
    have src1 : (select s).getReg .x6+8 =
        BitVec.ofNat 64 (sourceBase+16*
          (((s.getMem 0x810e8 >>> ((s.getMem 0x81050).toNat%64)) ^^^
            (1:Word)).toNat)+8) := by simpa using srcEq
    rw [src1] at copied
    simpa using copied.trans (sourceWords (1 : Fin 2))

theorem tick_prior (hash : Hash) (s : MachineState)
    (level witnessBase target : Nat) (a : Word)
    (levelWord : s.getMem 0x81050=BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (levelBound : level<10)
    (witnessBound : witnessBase+16*level+16≤0x80000)
    (destination : s.getMem 0x810c8=BitVec.ofNat 64 target)
    (targetCase : target=0x83000 ∨ target=0x88000)
    (before : a.toNat<witnessBase+16*level) :
    (tick hash s).getMem a=s.getMem a := by
  have low : a.toNat<0x80000 := by omega
  rw [tick_from_copy hash s level witnessBase target a levelWord witness
    levelBound witnessBound destination targetCase low]
  have dstNat := GroupedBalancedSignUpperTreeSelect67.destination_nat s
    level witnessBase levelWord witness levelBound witnessBound
  apply GroupedBalancedSignBottomTreeSelectData67.copied_frame
  · intro eq
    have hn := congrArg BitVec.toNat eq
    rw [dstNat] at hn
    omega
  · intro eq
    have hn := congrArg BitVec.toNat eq
    rw [BitVec.toNat_add,dstNat] at hn
    have eight : (8:Word).toNat=8 := by decide
    rw [eight,Nat.mod_eq_of_lt (by omega :
      witnessBase+16*level+8<2^64)] at hn
    omega

#print axioms tick_from_copy
#print axioms tick_sibling
#print axioms tick_prior
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingTick67
