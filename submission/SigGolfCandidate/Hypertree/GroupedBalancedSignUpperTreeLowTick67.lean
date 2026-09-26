import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstTick67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeInnerTickFrame67

/-! The reused parent-tree hash leaves signer key and public-key words untouched. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeLowTick67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private def selected (s : MachineState) :=
  GroupedBalancedSignBottomTreeSelectPtr67.selectState s
private def copied (s : MachineState) :=
  GroupedBalancedSignBottomTreeSelectCopy67.copyState (selected s)
private def paired (s : MachineState) :=
  GroupedBalancedSignBottomTreePairPtr67.pairState (copied s)
private def children (s : MachineState) :=
  GroupedBalancedSignBottomTreeChildData67.childrenState (paired s)
private def ready (s : MachineState) :=
  GroupedBalancedSignBottomTreeH4Prelude67.preludeState (children s)

private theorem ne_static (a : Word) (low : a.toNat<0x100) (b : Nat)
    (hb : 0x100≤b) (small : b<2^64) : a≠BitVec.ofNat 64 b := by
  intro eq
  have hn := congrArg BitVec.toNat eq
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at hn
  omega

theorem first_hashed_low (hash : Hash) (s : MachineState)
    (level witnessBase : Nat) (a : Word)
    (levelWord : s.getMem 0x81050=BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (levelBound : level<10)
    (witnessLower : 0x20060≤witnessBase)
    (witnessBound : witnessBase+16*level+16≤0x80000)
    (low : a.toNat<0x100) :
    (GroupedBalancedSignBottomTreeFirstTickData67.hashed hash s).getMem a =
      s.getMem a := by
  have ptr := GroupedBalancedSignUpperTreeSelect67.destination_nat s
    level witnessBase levelWord witness levelBound witnessBound
  have ptr' : ((selected s).getReg .x7).toNat =
      witnessBase+16*level := ptr
  have ptr8 : ((selected s).getReg .x7+8).toNat =
      witnessBase+16*level+8 := by
    rw [BitVec.toNat_add,ptr']
    change (witnessBase+16*level+8)%2^64 = _
    rw [Nat.mod_eq_of_lt (by omega)]
  have copyFrame : (copied s).getMem a=s.getMem a := by
    apply GroupedBalancedSignBottomTreeSelectData67.copied_frame
    · intro eq
      have hn := congrArg BitVec.toNat eq
      have hn' : a.toNat=((selected s).getReg .x7).toNat := hn
      rw [ptr'] at hn'
      omega
    · intro eq
      have hn := congrArg BitVec.toNat eq
      have hn' : a.toNat=((selected s).getReg .x7+8).toNat := hn
      rw [ptr8] at hn'
      omega
  have pairFrame : (paired s).getMem a=(copied s).getMem a :=
    GroupedBalancedSignBottomTreePairStartData67.initial_frame _ a
      (ne_static a low 0x810d8 (by decide) (by decide))
  have childFrame : (children s).getMem a=(paired s).getMem a :=
    GroupedBalancedSignBottomTreeChildData67.frame _ a
      (ne_static a low 0x80020 (by decide) (by decide))
      (ne_static a low 0x80028 (by decide) (by decide))
      (ne_static a low 0x80030 (by decide) (by decide))
      (ne_static a low 0x80038 (by decide) (by decide))
  have readyFrame : (ready s).getMem a=(children s).getMem a :=
    GroupedBalancedSignBottomTreeH4Prelude67.prelude_frame _ a
      (ne_static a low 0x80000 (by decide) (by decide))
      (ne_static a low 0x80008 (by decide) (by decide))
      (ne_static a low 0x80010 (by decide) (by decide))
      (ne_static a low 0x80018 (by decide) (by decide))
  have answerFrame :
      (GroupedBalancedSignBottomTreeFirstTickData67.hashed hash s).getMem a =
        (ready s).getMem a := by
    have args := GroupedBalancedSignBottomTreeH4Prelude67.prelude_hash_args
      (children s)
    apply Signing.hash_answer_frame (ready s) (hash (hashInput (ready s)))
      args.2.2.1 a
    intro i eq
    have hn := congrArg BitVec.toNat eq
    simp only [Signing.wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80300+8*i.val < 2^64)] at hn
    omega
  exact answerFrame.trans (readyFrame.trans (childFrame.trans
    (pairFrame.trans copyFrame)))

#print axioms first_hashed_low

theorem first_tick_low (hash : Hash) (s : MachineState)
    (level witnessBase target : Nat) (a : Word)
    (levelWord : s.getMem 0x81050=BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (levelBound : level<10)
    (witnessLower : 0x20060≤witnessBase)
    (witnessBound : witnessBase+16*level+16≤0x80000)
    (destination : s.getMem 0x810c8=BitVec.ofNat 64 target)
    (targetCase : target=0x83000 ∨ target=0x88000)
    (low : a.toNat<0x100) :
    (GroupedBalancedSignBottomTreeFirstTickData67.tickState hash s).getMem a =
      s.getMem a := by
  let hashed := GroupedBalancedSignBottomTreeFirstTickData67.hashed hash s
  let stored := GroupedBalancedSignBottomTreeFirstTickData67.stored hash s
  let ptr := GroupedBalancedSignBottomTreeHashStorePtr67.storeState hashed
  have targetPtr := GroupedBalancedSignUpperTreeFirstTick67.output_pointer
    hash s level witnessBase target levelWord witness levelBound
    witnessBound destination
  have targetLow : 0x100 ≤ target := by
    rcases targetCase with rfl | rfl <;> decide
  have targetSmall : target+8<2^64 := by
    rcases targetCase with rfl | rfl <;> decide
  have ne0 : a≠ptr.getReg .x7 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [targetPtr,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : target<2^64)] at hn
    omega
  have ne8 : a≠ptr.getReg .x7+8 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [BitVec.toNat_add,targetPtr,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : target<2^64)] at hn
    change a.toNat=(target+8)%2^64 at hn
    rw [Nat.mod_eq_of_lt targetSmall] at hn
    omega
  have storedFrame : stored.getMem a=hashed.getMem a :=
    GroupedBalancedSignBottomTreeStoreData67.stored_frame hashed a ne0 ne8
  have advFrame :
      (GroupedBalancedSignBottomTreeFirstTickData67.advanced hash s).getMem a =
        stored.getMem a := by
    apply GroupedBalancedSignBottomTreeParentControl67.advance_frame
    · exact ne_static a low 0x81008 (by decide) (by decide)
    · exact ne_static a low 0x810d8 (by decide) (by decide)
  rw [GroupedBalancedSignBottomTreeFirstTickData67.tickState,
    GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    advFrame,storedFrame]
  exact first_hashed_low hash s level witnessBase a levelWord witness
    levelBound witnessLower witnessBound low

#print axioms first_tick_low

private def loopPair (s : MachineState) :=
  GroupedBalancedSignBottomTreePairPtrLoop67.pairState s
private def loopChildren (s : MachineState) :=
  GroupedBalancedSignBottomTreeChildData67.childrenState (loopPair s)
private def loopReady (s : MachineState) :=
  GroupedBalancedSignBottomTreeH4Prelude67.preludeState (loopChildren s)

theorem inner_hashed_low (hash : Hash) (s : MachineState) (a : Word)
    (low : a.toNat<0x100) :
    (GroupedBalancedSignBottomTreeInnerTickFrame67.hashed hash s).getMem a =
      s.getMem a := by
  have pairFrame : (loopPair s).getMem a=s.getMem a :=
    GroupedBalancedSignBottomTreePointerData67.pair_frame s a
  have childFrame : (loopChildren s).getMem a=(loopPair s).getMem a :=
    GroupedBalancedSignBottomTreeChildData67.frame _ a
      (ne_static a low 0x80020 (by decide) (by decide))
      (ne_static a low 0x80028 (by decide) (by decide))
      (ne_static a low 0x80030 (by decide) (by decide))
      (ne_static a low 0x80038 (by decide) (by decide))
  have readyFrame : (loopReady s).getMem a=(loopChildren s).getMem a :=
    GroupedBalancedSignBottomTreeH4Prelude67.prelude_frame _ a
      (ne_static a low 0x80000 (by decide) (by decide))
      (ne_static a low 0x80008 (by decide) (by decide))
      (ne_static a low 0x80010 (by decide) (by decide))
      (ne_static a low 0x80018 (by decide) (by decide))
  have answerFrame :
      (GroupedBalancedSignBottomTreeInnerTickFrame67.hashed hash s).getMem a =
        (loopReady s).getMem a := by
    have args := GroupedBalancedSignBottomTreeH4Prelude67.prelude_hash_args
      (loopChildren s)
    apply Signing.hash_answer_frame (loopReady s)
      (hash (hashInput (loopReady s))) args.2.2.1 a
    intro i eq
    have hn := congrArg BitVec.toNat eq
    simp only [Signing.wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80300+8*i.val < 2^64)] at hn
    omega
  exact answerFrame.trans (readyFrame.trans (childFrame.trans pairFrame))

theorem inner_tick_low (hash : Hash) (s : MachineState)
    (count target : Nat) (a : Word)
    (counter : s.getMem 0x810d8=BitVec.ofNat 64 count)
    (destination : s.getMem 0x810c8=BitVec.ofNat 64 target)
    (countBound : count<512)
    (targetCase : target=0x83000 ∨ target=0x88000)
    (low : a.toNat<0x100) :
    (GroupedBalancedSignBottomTreeInnerTickFrame67.tickState hash s).getMem a =
      s.getMem a := by
  let hashed := GroupedBalancedSignBottomTreeInnerTickFrame67.hashed hash s
  let stored := GroupedBalancedSignBottomTreeInnerTickFrame67.stored hash s
  let ptr := GroupedBalancedSignBottomTreeHashStorePtr67.storeState hashed
  have targetPtr := GroupedBalancedSignBottomTreeInnerTickFrame67.output_pointer_nat
    hash s count target counter destination countBound targetCase
  have ne0 : a≠ptr.getReg .x7 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [targetPtr] at hn
    rcases targetCase with rfl | rfl <;> omega
  have ne8 : a≠ptr.getReg .x7+8 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [BitVec.toNat_add,targetPtr] at hn
    have eight : (8:Word).toNat=8 := by decide
    rw [eight,Nat.mod_eq_of_lt (by
      rcases targetCase with rfl | rfl <;> omega)] at hn
    rcases targetCase with rfl | rfl <;> omega
  have storedFrame : stored.getMem a=hashed.getMem a :=
    GroupedBalancedSignBottomTreeStoreData67.stored_frame hashed a ne0 ne8
  have advFrame :
      (GroupedBalancedSignBottomTreeInnerTickFrame67.advanced hash s).getMem a =
        stored.getMem a := by
    apply GroupedBalancedSignBottomTreeParentControl67.advance_frame
    · exact ne_static a low 0x81008 (by decide) (by decide)
    · exact ne_static a low 0x810d8 (by decide) (by decide)
  rw [GroupedBalancedSignBottomTreeInnerTickFrame67.tickState,
    GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    advFrame,storedFrame]
  exact inner_hashed_low hash s a low

#print axioms inner_hashed_low
#print axioms inner_tick_low
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeLowTick67
