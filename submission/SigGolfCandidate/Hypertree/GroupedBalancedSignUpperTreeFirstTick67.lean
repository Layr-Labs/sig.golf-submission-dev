import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeSelect67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeFirstTickReady67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeFirstTickData67

/-! The shared first parent tick with the moving upper signature pointer. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstTick67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev tick := GroupedBalancedSignBottomTreeFirstTickData67.tickState
private abbrev paired (s : MachineState) :=
  GroupedBalancedSignBottomTreePairPtr67.pairState
    (GroupedBalancedSignBottomTreeSelectCopy67.copyState
      (GroupedBalancedSignBottomTreeSelectPtr67.selectState s))

theorem paired_pointer (s : MachineState) (level witnessBase : Nat)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000) :
    (paired s).getReg .x7 = s.getMem 0x810c0 := by
  rw [paired,GroupedBalancedSignBottomTreePairStartData67.initial_pointer]
  exact GroupedBalancedSignUpperTreeSelect67.copied_high_frame s level
    witnessBase 0x810c0 levelWord witness levelBound witnessBound (by decide)

theorem hashed_high_frame (hash : Hash) (s : MachineState)
    (level witnessBase : Nat) (a : Word)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000)
    (high : 0x81000 ≤ a.toNat) (counterNe : a ≠ 0x810d8) :
    (GroupedBalancedSignBottomTreeFirstTickData67.hashed hash s).getMem a =
      s.getMem a := by
  rw [GroupedBalancedSignBottomTreeFirstTickData67.hashed_from_paired
    hash s a high]
  change (paired s).getMem a = _
  rw [GroupedBalancedSignBottomTreePairStartData67.initial_frame _ a counterNe]
  exact GroupedBalancedSignUpperTreeSelect67.copied_high_frame s level
    witnessBase a levelWord witness levelBound witnessBound (by omega)

theorem output_pointer (hash : Hash) (s : MachineState)
    (level witnessBase target : Nat)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target) :
    (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
      (GroupedBalancedSignBottomTreeFirstTickData67.hashed hash s)).getReg .x7 =
      BitVec.ofNat 64 target := by
  have targetWord :
      (GroupedBalancedSignBottomTreeFirstTickData67.hashed hash s).getMem
        0x810c8 = BitVec.ofNat 64 target := by
    rw [hashed_high_frame hash s level witnessBase 0x810c8 levelWord
      witness levelBound witnessBound (by decide) (by decide),destination]
  have ptr := GroupedBalancedSignBottomTreePointerData67.store_reg_nat
    (GroupedBalancedSignBottomTreeFirstTickData67.hashed hash s) 0 target
    (GroupedBalancedSignBottomTreeFirstTickData67.hashed_counter hash s)
    targetWord
  simpa only [Nat.mul_zero,Nat.add_zero] using ptr

theorem executes (hash : Hash) (s : MachineState)
    (level witnessBase sourceBase target : Nat)
    (pc : s.pc = 0x1e94)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000)
    (witnessAligned : witnessBase % 8 = 0)
    (selectedBound : (s.getMem 0x810e8).toNat < 1024)
    (source : s.getMem 0x810c0 = BitVec.ofNat 64 sourceBase)
    (sourceCase : sourceBase = 0x83000 ∨ sourceBase = 0x88000)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (targetCase : target = 0x83000 ∨ target = 0x88000) :
    Trace hash image s 113 120 1 1 (tick hash s) := by
  let t1 := GroupedBalancedSignBottomTreeSelectPtr67.selectState s
  let t2 := GroupedBalancedSignBottomTreeSelectCopy67.copyState t1
  let t3 := GroupedBalancedSignBottomTreePairPtr67.pairState t2
  let t4 := GroupedBalancedSignBottomTreePairLoad67.loadState t3
  let t5 := GroupedBalancedSignBottomTreeNodeInput67.inputState t4
  let t6 := writeHash
    (GroupedBalancedSignBottomTreeH4Prelude67.preludeState t5)
    (hash (hashInput (GroupedBalancedSignBottomTreeH4Prelude67.preludeState t5)))
  let t7 := GroupedBalancedSignBottomTreeHashStorePtr67.storeState t6
  let t8 := GroupedBalancedSignBottomTreeHashStoreCopy67.copyState t7
  let t9 := GroupedBalancedSignBottomTreeParentAdvance67.advanceState t8
  let t10 := GroupedBalancedSignBottomTreeParentControl67.branchState t9
  have sourceValid (k : Nat) (hk : k ≤ 8) (ha : k % 8 = 0) :
      accessValid (t1.getReg .x6 + BitVec.ofNat 64 k) 8 = true :=
    GroupedBalancedSignBottomTreeSelectData67.source_access s sourceBase k
      source sourceCase selectedBound hk ha
  have destinationValid (k : Nat) (hk : k ≤ 8) (ha : k % 8 = 0) :
      accessValid (t1.getReg .x7 + BitVec.ofNat 64 k) 8 = true :=
    GroupedBalancedSignUpperTreeSelect67.destination_access s level witnessBase
      k levelWord witness levelBound witnessBound witnessAligned hk ha
  have childPtr : t3.getReg .x7 = BitVec.ofNat 64 sourceBase := by
    rw [paired_pointer s level witnessBase levelWord witness levelBound
      witnessBound,source]
  have childValid (k : Nat) (hk : k = 0 ∨ k = 8 ∨ k = 16 ∨ k = 24) :
      accessValid (t3.getReg .x7 + BitVec.ofNat 64 k) 8 = true := by
    rw [childPtr]
    rcases sourceCase with rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl <;> decide
  have outputPtr : t7.getReg .x7 = BitVec.ofNat 64 target :=
    output_pointer hash s level witnessBase target levelWord witness levelBound
      witnessBound destination
  have outputValid (k : Nat) (hk : k = 0 ∨ k = 8) :
      accessValid (t7.getReg .x7 + BitVec.ofNat 64 k) 8 = true := by
    rw [outputPtr]
    rcases targetCase with rfl | rfl <;>
      rcases hk with rfl | rfl <;> decide
  exact GroupedBalancedSignBottomTreeFirstTick67.first_tick
    hash s t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 pc
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by simpa using sourceValid 0 (by decide) (by decide))
    (sourceValid 8 (by decide) (by decide))
    (by simpa using destinationValid 0 (by decide) (by decide))
    (destinationValid 8 (by decide) (by decide))
    (by simpa using childValid 0 (Or.inl rfl))
    (childValid 8 (Or.inr (Or.inl rfl)))
    (childValid 16 (Or.inr (Or.inr (Or.inl rfl))))
    (childValid 24 (Or.inr (Or.inr (Or.inr rfl))))
    (by simpa using outputValid 0 (Or.inl rfl))
    (outputValid 8 (Or.inr rfl))

#print axioms executes
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstTick67
