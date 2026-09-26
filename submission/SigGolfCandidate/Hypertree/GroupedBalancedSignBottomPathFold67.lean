import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentLevel67
import SigGolfCandidate.Hypertree.GroupedBalancedBottomBuildSibling67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedTick67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomPathFold67. -/
section
/-! The first tick of a bottom-tree level copies the selected sibling into the wire. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedTick67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomTreeParentFold67
open GroupedBalancedSignBottomTreeParentLevel67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev selected (s : MachineState) :=
  GroupedBalancedSignBottomTreeSelectPtr67.selectState s
private abbrev copied (s : MachineState) :=
  GroupedBalancedSignBottomTreeSelectCopy67.copyState (selected s)
private abbrev paired (s : MachineState) :=
  GroupedBalancedSignBottomTreePairPtr67.pairState (copied s)
private abbrev children (s : MachineState) :=
  GroupedBalancedSignBottomTreeChildData67.childrenState (paired s)
private abbrev ready (s : MachineState) :=
  GroupedBalancedSignBottomTreeH4Prelude67.preludeState (children s)
private abbrev first := GroupedBalancedSignBottomTreeFirstTickData67.tickState
private abbrev node := GroupedBalancedSignBottomTreeModel67.levelNode

theorem first_below_hash (hash : Hash) (s : MachineState) (a : Word)
    (low : a.toNat < 0x80000) :
    (GroupedBalancedSignBottomTreeFirstTickData67.hashed hash s).getMem a =
      (copied s).getMem a := by
  have ne (b : Nat) (hb : 0x80000 ≤ b) (hbound : b < 2^64) :
      a ≠ BitVec.ofNat 64 b := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound] at hn
    omega
  have pairFrame := GroupedBalancedSignBottomTreePairStartData67.initial_frame
    (copied s) a (ne 0x810d8 (by decide) (by decide))
  have childFrame := GroupedBalancedSignBottomTreeChildData67.frame (paired s) a
    (ne 0x80020 (by decide) (by decide))
    (ne 0x80028 (by decide) (by decide))
    (ne 0x80030 (by decide) (by decide))
    (ne 0x80038 (by decide) (by decide))
  have readyFrame := GroupedBalancedSignBottomTreeH4Prelude67.prelude_frame
    (children s) a (ne 0x80000 (by decide) (by decide))
    (ne 0x80008 (by decide) (by decide))
    (ne 0x80010 (by decide) (by decide))
    (ne 0x80018 (by decide) (by decide))
  have answerFrame :
      (GroupedBalancedSignBottomTreeFirstTickData67.hashed hash s).getMem a =
        (ready s).getMem a := by
    have args := GroupedBalancedSignBottomTreeH4Prelude67.prelude_hash_args
      (children s)
    apply Signing.hash_answer_frame (ready s) (hash (hashInput (ready s)))
      args.2.2.1 a
    intro i same
    exact ne (0x80300+8*i.val) (by omega) (by omega) same
  exact answerFrame.trans (readyFrame.trans (childFrame.trans pairFrame))

theorem first_below_copy (hash : Hash) (s : MachineState)
    (height target : Nat) (a : Word)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 height)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (heightBound : height < 10)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
    (low : a.toNat < 0x80000) :
    (first hash s).getMem a = (copied s).getMem a := by
  have addrNe : a ≠ 0x81008 := by
    intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega
  have counterNe : a ≠ 0x810d8 := by
    intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega
  rw [first,GroupedBalancedSignBottomTreeFirstTickData67.tickState,
    GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    GroupedBalancedSignBottomTreeFirstTickData67.advanced,
    GroupedBalancedSignBottomTreeParentControl67.advance_frame _ a addrNe counterNe,
    GroupedBalancedSignBottomTreeFirstTickData67.stored_from_hashed
      hash s height target a levelWord witnessBase heightBound
      destination targetCase (by omega),
    first_below_hash hash s a low]

theorem first_prior_frame (hash : Hash) (s : MachineState)
    (height target : Nat) (a : Word)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 height)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (heightBound : height < 10)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
    (prior : a.toNat < 0x20090+16*height) :
    (first hash s).getMem a = s.getMem a := by
  rw [first_below_copy hash s height target a levelWord witnessBase
    heightBound destination targetCase (by omega)]
  have dst := GroupedBalancedSignBottomTreeSelectData67.selected_destination_nat
    s height levelWord witnessBase heightBound
  have ne0 : a ≠ (selected s).getReg .x7 := by
    intro eq; have hn := congrArg BitVec.toNat eq; rw [dst] at hn; omega
  have ne1 : a ≠ (selected s).getReg .x7 + 8 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [BitVec.toNat_add,dst] at hn
    have eight : (8 : Word).toNat = 8 := by decide
    rw [eight,Nat.mod_eq_of_lt (by omega : 0x20090+16*height+8 < 2^64)] at hn
    omega
  exact GroupedBalancedSignBottomTreeSelectData67.copied_frame s a ne0 ne1

private def siblingIndex (s : MachineState) : Word :=
  (s.getMem 0x810e8 >>> ((s.getMem 0x81050).toNat % 64)) ^^^ 1

theorem sibling_index_nat (s : MachineState) (height selectedIndex : Nat)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 height)
    (heightBound : height < 10)
    (selectedWord : (s.getMem 0x810e8).toNat = selectedIndex) :
    (siblingIndex s).toNat = Nat.xor (selectedIndex / 2^height) 1 := by
  rw [siblingIndex,BitVec.toNat_xor]
  have heightSmall : height < 2^64 := by omega
  simp only [levelWord,BitVec.toNat_ofNat,Nat.mod_eq_of_lt heightSmall,
    Nat.mod_eq_of_lt (by omega : height < 64),BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow,selectedWord]
  rfl

theorem sibling_index_bound (selectedIndex height limit : Nat)
    (selectedBound : selectedIndex < 1024)
    (heightBound : height < 10)
    (limitDef : limit = 512/2^height) :
    Nat.xor (selectedIndex/2^height) 1 < 2*limit := by
  have small : selectedIndex/2^height < 2^(10-height) := by
    interval_cases height <;> norm_num at * <;> omega
  have xorSmall : Nat.xor (selectedIndex/2^height) 1 < 2^(10-height) :=
    Nat.xor_lt_two_pow small (by
      have positive : 0 < 10-height := by omega
      exact Nat.one_lt_two_pow (by omega))
  rw [limitDef]
  interval_cases height <;> norm_num at * <;> omega

theorem first_sibling_words (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase selectedIndex : Nat)
    (s : MachineState)
    (params : Params base height limit source target addressBase)
    (start : Start hash secretKey base height limit source target addressBase s)
    (selectedWord : (s.getMem 0x810e8).toNat = selectedIndex) :
    ∀ i : Fin 2,
      (first hash s).getMem
        (BitVec.ofNat 64 (0x20090+16*height+8*i.val)) =
      (node hash secretKey base height
        (Nat.xor (selectedIndex/2^height) 1)).extractLsb'
          (64*i.val) 64 := by
  let j := Nat.xor (selectedIndex/2^height) 1
  have selectedBound : selectedIndex < 1024 := by
    rw [←selectedWord]
    exact start.selectedBound
  have jBound : j < 2*limit :=
    sibling_index_bound selectedIndex height limit selectedBound
      params.heightBound params.limitDef
  have jEq : (siblingIndex s).toNat = j :=
    sibling_index_nat s height selectedIndex start.levelWord
      params.heightBound selectedWord
  have sourceCase : source = 0x83000 ∨ source = 0x88000 := by
    rcases params.bases with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  have targetCase : target = 0x83000 ∨ target = 0x88000 := by
    rcases params.bases with ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  have sourceNat := GroupedBalancedSignBottomTreeSelectData67.selected_source_nat
    s source start.sourcePtr sourceCase start.selectedBound
  change ((selected s).getReg .x6).toNat =
    source + 16*(siblingIndex s).toNat at sourceNat
  have srcEq : (selected s).getReg .x6 =
      BitVec.ofNat 64 (source+16*j) := by
    apply BitVec.eq_of_toNat_eq
    rw [sourceNat,jEq,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by rcases sourceCase with rfl | rfl <;> omega)]
  have destNat := GroupedBalancedSignBottomTreeSelectData67.selected_destination_nat
    s height start.levelWord start.witnessBase params.heightBound
  have destEq : (selected s).getReg .x7 =
      BitVec.ofNat 64 (0x20090+16*height) := by
    apply BitVec.eq_of_toNat_eq
    rw [destNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  intro i
  fin_cases i
  · have aLow : (BitVec.ofNat 64 (0x20090+16*height)).toNat < 0x80000 := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      have hb := params.heightBound
      omega
    change (first hash s).getMem (BitVec.ofNat 64 (0x20090+16*height)) =
      (node hash secretKey base height j).extractLsb' 0 64
    rw [first_below_copy hash s height target _ start.levelWord start.witnessBase
      params.heightBound start.targetPtr targetCase aLow]
    rw [←destEq]
    have distinct : (selected s).getReg .x7 ≠
        (selected s).getReg .x7 + 8 := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      rw [BitVec.toNat_add,destNat] at hn
      have eight : (8 : Word).toNat = 8 := by decide
      have hb := params.heightBound
      rw [eight,Nat.mod_eq_of_lt (by omega : 0x20090+16*height+8 < 2^64)] at hn
      omega
    rw [GroupedBalancedSignBottomTreeSelectData67.copied_low s distinct,srcEq]
    simpa [j] using start.sourceWords j jBound (0 : Fin 2)
  · have aHigh : (BitVec.ofNat 64 (0x20090+16*height+8)).toNat < 0x80000 := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      have hb := params.heightBound
      omega
    change (first hash s).getMem (BitVec.ofNat 64 (0x20090+16*height+8)) =
      (node hash secretKey base height j).extractLsb' 64 64
    rw [first_below_copy hash s height target _ start.levelWord start.witnessBase
      params.heightBound start.targetPtr targetCase aHigh]
    have dstPlus : BitVec.ofNat 64 (0x20090+16*height+8) =
        (selected s).getReg .x7 + 8 := by
      rw [destEq]
      simp [BitVec.ofNat_add]
    rw [dstPlus,GroupedBalancedSignBottomTreeSelectData67.copied_high s,srcEq]
    simpa [j,BitVec.ofNat_add] using start.sourceWords j jBound (1 : Fin 2)

#print axioms first_below_copy
#print axioms first_prior_frame
#print axioms first_sibling_words
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedTick67

end

/-! Frames for the remaining parent ticks after a bottom sibling is copied. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomPathFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomTreeParentFold67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev F := GroupedBalancedSignBottomTreeInnerTickFrame67.tickState
private abbrev pair (s : MachineState) :=
  GroupedBalancedSignBottomTreePairPtrLoop67.pairState s
private abbrev children (s : MachineState) :=
  GroupedBalancedSignBottomTreeChildData67.childrenState (pair s)
private abbrev ready (s : MachineState) :=
  GroupedBalancedSignBottomTreeH4Prelude67.preludeState (children s)

theorem inner_below_hash (hash : Hash) (s : MachineState) (a : Word)
    (low : a.toNat < 0x80000) :
    (GroupedBalancedSignBottomTreeInnerTickFrame67.hashed hash s).getMem a =
      s.getMem a := by
  have ne (b : Nat) (hb : 0x80000 ≤ b) (hbound : b < 2^64) :
      a ≠ BitVec.ofNat 64 b := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hbound] at hn
    omega
  have pairFrame := GroupedBalancedSignBottomTreePointerData67.pair_frame s a
  have childFrame := GroupedBalancedSignBottomTreeChildData67.frame (pair s) a
    (ne 0x80020 (by decide) (by decide))
    (ne 0x80028 (by decide) (by decide))
    (ne 0x80030 (by decide) (by decide))
    (ne 0x80038 (by decide) (by decide))
  have readyFrame := GroupedBalancedSignBottomTreeH4Prelude67.prelude_frame
    (children s) a (ne 0x80000 (by decide) (by decide))
    (ne 0x80008 (by decide) (by decide))
    (ne 0x80010 (by decide) (by decide))
    (ne 0x80018 (by decide) (by decide))
  have answerFrame :
      (GroupedBalancedSignBottomTreeInnerTickFrame67.hashed hash s).getMem a =
        (ready s).getMem a := by
    have args := GroupedBalancedSignBottomTreeH4Prelude67.prelude_hash_args
      (children s)
    apply Signing.hash_answer_frame (ready s) (hash (hashInput (ready s)))
      args.2.2.1 a
    intro i same
    exact ne (0x80300+8*i.val) (by omega) (by omega) same
  exact answerFrame.trans (readyFrame.trans (childFrame.trans pairFrame))

theorem inner_below_frame (hash : Hash) (s : MachineState)
    (count target : Nat) (a : Word)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (countBound : count < 512)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
    (low : a.toNat < 0x80000) :
    (F hash s).getMem a = s.getMem a := by
  have ptr := GroupedBalancedSignBottomTreeInnerTickFrame67.output_pointer_nat
    hash s count target counter destination countBound targetCase
  have addrNe : a ≠ 0x81008 := by
    intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega
  have counterNe : a ≠ 0x810d8 := by
    intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega
  have ne0 : a ≠ (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
      (GroupedBalancedSignBottomTreeInnerTickFrame67.hashed hash s)).getReg .x7 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [ptr] at hn
    rcases targetCase with rfl | rfl <;> omega
  have ne1 : a ≠ (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
      (GroupedBalancedSignBottomTreeInnerTickFrame67.hashed hash s)).getReg .x7 + 8 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [BitVec.toNat_add,ptr] at hn
    have eight : (8 : Word).toNat = 8 := by decide
    rw [eight,Nat.mod_eq_of_lt (by
      rcases targetCase with rfl | rfl <;> omega)] at hn
    rcases targetCase with rfl | rfl <;> omega
  rw [F,GroupedBalancedSignBottomTreeInnerTickFrame67.tickState,
    GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    GroupedBalancedSignBottomTreeInnerTickFrame67.advanced,
    GroupedBalancedSignBottomTreeParentControl67.advance_frame _ a addrNe counterNe,
    GroupedBalancedSignBottomTreeInnerTickFrame67.stored,
    GroupedBalancedSignBottomTreeStoreData67.stored_frame _ a ne0 ne1,
    inner_below_hash hash s a low]

def Safe (a : Word) : Prop := a.toNat < 0x80000 ∨ a = 0x810e8

theorem inner_safe (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase n : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (holds : At hash secretKey base height limit source target addressBase n s)
    (nBound : n < limit) (a : Word) (safe : Safe a) :
    (F hash s).getMem a = s.getMem a := by
  have countBound : n < 512 := by have h := params.limitBound; omega
  have targetCase : target = 0x83000 ∨ target = 0x88000 := by
    rcases params.bases with ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  rcases safe with low | rfl
  · exact inner_below_frame hash s n target a holds.counter holds.targetPtr
      countBound targetCase low
  · exact GroupedBalancedSignBottomTreeInnerTickFrame67.tick_control_frame
      hash s n target 0x810e8 holds.counter holds.targetPtr countBound
      targetCase (by decide) (by decide) (by decide) (by decide)

theorem fold_safe (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase n : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (holds : At hash secretKey base height limit source target addressBase n s)
    (nBound : n < limit) :
    ∃ final,
      Trace hash image s (84*(limit-n)) (91*(limit-n))
        (limit-n) (limit-n) final ∧
      Done hash secretKey base height limit source target addressBase final ∧
      (∀ a, Safe a → final.getMem a = s.getMem a) := by
  suffices H : ∀ remaining n (s : MachineState), remaining = limit-n →
      n < limit → At hash secretKey base height limit source target addressBase n s →
      ∃ final,
        Trace hash image s (84*remaining) (91*remaining)
          remaining remaining final ∧
        Done hash secretKey base height limit source target addressBase final ∧
        (∀ a, Safe a → final.getMem a = s.getMem a) by
    exact H (limit-n) n s rfl nBound holds
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
      intro n s remEq nBound holds
      obtain ⟨firstTrace,next,last⟩ :=
        one_tick hash secretKey base height limit source target addressBase n s
          params holds nBound
      by_cases more : n+1 < limit
      · obtain ⟨final,rest,finished,restFrame⟩ :=
          ih (limit-(n+1)) (by omega) (n+1) (F hash s)
            (by omega) more (next more)
        refine ⟨final,?_,finished,?_⟩
        · convert firstTrace.trans rest using 1 <;> omega
        · intro a ha
          exact (restFrame a ha).trans
            (inner_safe hash secretKey base height limit source target
              addressBase n s params holds nBound a ha)
      · have atEnd : n+1=limit := by omega
        refine ⟨F hash s,?_,last atEnd,?_⟩
        · have one : remaining=1 := by omega
          simpa only [one,Nat.mul_one] using firstTrace
        · intro a ha
          exact inner_safe hash secretKey base height limit source target
            addressBase n s params holds nBound a ha

theorem one_level_selected (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase selectedIndex : Nat)
    (s : MachineState)
    (params : Params base height limit source target addressBase)
    (start : GroupedBalancedSignBottomTreeParentLevel67.Start hash secretKey
      base height limit source target addressBase s)
    (positive : 0 < limit)
    (selectedWord : (s.getMem 0x810e8).toNat = selectedIndex) :
    ∃ final,
      Trace hash image s (113+84*(limit-1)) (120+91*(limit-1))
        limit limit final ∧
      Done hash secretKey base height limit source target addressBase final ∧
      (∀ a, a.toNat < 0x20090+16*height →
        final.getMem a = s.getMem a) ∧
      final.getMem 0x810e8 = s.getMem 0x810e8 ∧
      (∀ i : Fin 2,
        final.getMem (BitVec.ofNat 64 (0x20090+16*height+8*i.val)) =
          (GroupedBalancedSignBottomTreeModel67.levelNode hash secretKey base
            height (Nat.xor (selectedIndex/2^height) 1)).extractLsb'
              (64*i.val) 64) := by
  let first := GroupedBalancedSignBottomTreeFirstTickData67.tickState
  have targetCase : target = 0x83000 ∨ target = 0x88000 := by
    rcases params.bases with ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  obtain ⟨firstTrace,hcontinue,finish⟩ :=
    GroupedBalancedSignBottomTreeParentLevel67.first_result hash secretKey
      base height limit source target addressBase s params start positive
  have firstSelected :=
    GroupedBalancedSignBottomSelectedTick67.first_sibling_words hash secretKey
      base height limit source target addressBase selectedIndex s params start
      selectedWord
  have firstIndex : (first hash s).getMem 0x810e8 = s.getMem 0x810e8 :=
    GroupedBalancedSignBottomTreeFirstTickData67.tick_control_frame
      hash s height target 0x810e8 start.levelWord start.witnessBase
      params.heightBound start.targetPtr targetCase
      (by decide) (by decide) (by decide) (by decide)
  by_cases more : 1 < limit
  · obtain ⟨final,rest,done,restFrame⟩ :=
      fold_safe hash secretKey base height limit source target
        addressBase 1 (first hash s) params (hcontinue more) more
    refine ⟨final,?_,done,?_,?_,?_⟩
    · convert firstTrace.trans rest using 1 <;> omega
    · intro a prior
      have hb := params.heightBound
      exact (restFrame a (Or.inl (by omega))).trans
        (GroupedBalancedSignBottomSelectedTick67.first_prior_frame
          hash s height target a start.levelWord start.witnessBase
          params.heightBound start.targetPtr targetCase prior)
    · exact (restFrame 0x810e8 (Or.inr rfl)).trans firstIndex
    · intro i
      have slotSmall : (BitVec.ofNat 64 (0x20090+16*height+8*i.val)).toNat <
          0x80000 := by
        have hb := params.heightBound
        have hi := i.isLt
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
        omega
      exact (restFrame _ (Or.inl slotSmall)).trans (firstSelected i)
  · have one : limit=1 := by omega
    refine ⟨first hash s,?_,finish one,?_,firstIndex,firstSelected⟩
    · simpa [one] using firstTrace
    · intro a prior
      exact GroupedBalancedSignBottomSelectedTick67.first_prior_frame
        hash s height target a start.levelWord start.witnessBase
        params.heightBound start.targetPtr targetCase prior

#print axioms inner_below_frame
#print axioms one_level_selected
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomPathFold67
