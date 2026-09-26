import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeFirstTickData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeInnerTickFrame67

/-! Parent ticks preserve words above their two source and target node buffers. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeProtectedTick67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem first_high (hash : Hash) (s : MachineState)
    (height target : Nat) (a : Word)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 height)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (heightBound : height < 10)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
    (high : 0x90000 ≤ a.toNat) :
    (GroupedBalancedSignBottomTreeFirstTickData67.tickState hash s).getMem a =
      s.getMem a := by
  let hashed := GroupedBalancedSignBottomTreeFirstTickData67.hashed hash s
  let stored := GroupedBalancedSignBottomTreeFirstTickData67.stored hash s
  let ptr := GroupedBalancedSignBottomTreeHashStorePtr67.storeState hashed
  have targetPtr := GroupedBalancedSignBottomTreeFirstTickData67.output_pointer
    hash s height target levelWord witnessBase heightBound destination
  have ne0 : a ≠ ptr.getReg .x7 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [targetPtr,BitVec.toNat_ofNat] at hn
    rcases targetCase with rfl | rfl <;> omega
  have ne1 : a ≠ ptr.getReg .x7 + 8 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [targetPtr] at hn
    rcases targetCase with rfl | rfl
    · have v : ((BitVec.ofNat 64 0x83000) + 8).toNat = 0x83008 := by decide
      rw [v] at hn
      omega
    · have v : ((BitVec.ofNat 64 0x88000) + 8).toNat = 0x88008 := by decide
      rw [v] at hn
      omega
  have storeFrame : stored.getMem a = hashed.getMem a :=
    GroupedBalancedSignBottomTreeStoreData67.stored_frame hashed a ne0 ne1
  have hashFrame : hashed.getMem a = s.getMem a :=
    GroupedBalancedSignBottomTreeFirstTickData67.hashed_high_frame
      hash s height a levelWord witnessBase heightBound (by omega) (by
        intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega)
  have advFrame :
      (GroupedBalancedSignBottomTreeFirstTickData67.advanced hash s).getMem a =
        stored.getMem a := by
    apply GroupedBalancedSignBottomTreeParentControl67.advance_frame
    · intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega
    · intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega
  rw [GroupedBalancedSignBottomTreeFirstTickData67.tickState,
    GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    advFrame,storeFrame,hashFrame]

theorem inner_high (hash : Hash) (s : MachineState)
    (count target : Nat) (a : Word)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (countBound : count < 512)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
    (high : 0x90000 ≤ a.toNat) :
    (GroupedBalancedSignBottomTreeInnerTickFrame67.tickState hash s).getMem a =
      s.getMem a := by
  let hashed := GroupedBalancedSignBottomTreeInnerTickFrame67.hashed hash s
  let stored := GroupedBalancedSignBottomTreeInnerTickFrame67.stored hash s
  let ptr := GroupedBalancedSignBottomTreeHashStorePtr67.storeState hashed
  have ptrNat := GroupedBalancedSignBottomTreeInnerTickFrame67.output_pointer_nat
    hash s count target counter destination countBound targetCase
  have ne0 : a ≠ ptr.getReg .x7 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [ptrNat] at hn
    rcases targetCase with rfl | rfl <;> omega
  have ne1 : a ≠ ptr.getReg .x7 + 8 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [BitVec.toNat_add,ptrNat] at hn
    have eight : (8 : Word).toNat = 8 := by decide
    rw [eight,Nat.mod_eq_of_lt (by
      rcases targetCase with rfl | rfl <;> omega)] at hn
    rcases targetCase with rfl | rfl <;> omega
  have storeFrame : stored.getMem a = hashed.getMem a :=
    GroupedBalancedSignBottomTreeStoreData67.stored_frame hashed a ne0 ne1
  have hashFrame : hashed.getMem a = s.getMem a :=
    GroupedBalancedSignBottomTreeInnerTickFrame67.hashed_high_frame hash s a
      (by omega)
  have advFrame :
      (GroupedBalancedSignBottomTreeInnerTickFrame67.advanced hash s).getMem a =
        stored.getMem a := by
    apply GroupedBalancedSignBottomTreeParentControl67.advance_frame
    · intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega
    · intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega
  rw [GroupedBalancedSignBottomTreeInnerTickFrame67.tickState,
    GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    advFrame,storeFrame,hashFrame]

#print axioms first_high
#print axioms inner_high
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeProtectedTick67
