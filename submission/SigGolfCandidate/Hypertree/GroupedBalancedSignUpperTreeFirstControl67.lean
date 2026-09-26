import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeFirstTickControl67

/-! First upper parent tick counter and frame facts for the level induction. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstControl67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev hashed := GroupedBalancedSignBottomTreeFirstTickData67.hashed
private abbrev stored := GroupedBalancedSignBottomTreeFirstTickData67.stored
private abbrev advanced := GroupedBalancedSignBottomTreeFirstTickData67.advanced
private abbrev tick := GroupedBalancedSignBottomTreeFirstTickData67.tickState

theorem stored_from_hashed (hash : Hash) (s : MachineState)
    (level witnessBase target : Nat) (a : Word)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
    (low : a.toNat < 0x83000) :
    (stored hash s).getMem a = (hashed hash s).getMem a := by
  have ptr := GroupedBalancedSignUpperTreeFirstTick67.output_pointer hash s
    level witnessBase target levelWord witness levelBound witnessBound
    destination
  have h0 : a ≠ (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
      (hashed hash s)).getReg .x7 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [ptr,BitVec.toNat_ofNat] at hn
    rcases targetCase with rfl | rfl <;> omega
  have h1 : a ≠ (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
      (hashed hash s)).getReg .x7 + 8 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [ptr] at hn
    rcases targetCase with rfl | rfl
    · have v : ((BitVec.ofNat 64 0x83000) + 8).toNat = 0x83008 := by decide
      rw [v] at hn; omega
    · have v : ((BitVec.ofNat 64 0x88000) + 8).toNat = 0x88008 := by decide
      rw [v] at hn; omega
  exact GroupedBalancedSignBottomTreeStoreData67.stored_frame
    (hashed hash s) a h0 h1

theorem stored_control_frame (hash : Hash) (s : MachineState)
    (level witnessBase target : Nat) (a : Word)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
    (high : 0x81000 ≤ a.toNat) (low : a.toNat < 0x83000)
    (counterNe : a ≠ 0x810d8) :
    (stored hash s).getMem a = s.getMem a := by
  rw [stored_from_hashed hash s level witnessBase target a levelWord witness
    levelBound witnessBound destination targetCase low]
  exact GroupedBalancedSignUpperTreeFirstTick67.hashed_high_frame hash s
    level witnessBase a levelWord witness levelBound witnessBound high counterNe

theorem tick_count (hash : Hash) (s : MachineState)
    (level witnessBase target : Nat)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (targetCase : target = 0x83000 ∨ target = 0x88000) :
    (tick hash s).getMem 0x810d8 = 1 := by
  change (GroupedBalancedSignBottomTreeParentControl67.branchState
    (GroupedBalancedSignBottomTreeFirstTickData67.advanced hash s)).getMem 0x810d8 = _
  rw [GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    GroupedBalancedSignBottomTreeFirstTickData67.advanced,
    GroupedBalancedSignBottomTreeParentControl67.advance_count,
    stored_from_hashed hash s level witnessBase target 0x810d8 levelWord witness
      levelBound witnessBound destination targetCase (by decide),
    GroupedBalancedSignBottomTreeFirstTickData67.hashed_counter]
  decide

theorem tick_address (hash : Hash) (s : MachineState)
    (level witnessBase target : Nat)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (targetCase : target = 0x83000 ∨ target = 0x88000) :
    (tick hash s).getMem 0x81008 = s.getMem 0x81008 + 1 := by
  change (GroupedBalancedSignBottomTreeParentControl67.branchState
    (GroupedBalancedSignBottomTreeFirstTickData67.advanced hash s)).getMem 0x81008 = _
  rw [GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    GroupedBalancedSignBottomTreeFirstTickData67.advanced,
    GroupedBalancedSignBottomTreeParentControl67.advance_address,
    stored_control_frame hash s level witnessBase target 0x81008 levelWord
      witness levelBound witnessBound destination targetCase
      (by decide) (by decide) (by decide)]

theorem tick_source_frame (hash : Hash) (s : MachineState)
    (level witnessBase sourceBase target : Nat) (a : Word)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (bases : (sourceBase = 0x83000 ∧ target = 0x88000) ∨
      (sourceBase = 0x88000 ∧ target = 0x83000))
    (sourceRange : sourceBase ≤ a.toNat ∧ a.toNat < sourceBase+0x4000) :
    (tick hash s).getMem a = s.getMem a := by
  have targetCase : target = 0x83000 ∨ target = 0x88000 := by
    rcases bases with ⟨_,h⟩ | ⟨_,h⟩
    · exact Or.inr h
    · exact Or.inl h
  have ptr := GroupedBalancedSignUpperTreeFirstTick67.output_pointer hash s
    level witnessBase target levelWord witness levelBound witnessBound
    destination
  have h0 : a ≠ (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
      (hashed hash s)).getReg .x7 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [ptr,BitVec.toNat_ofNat] at hn
    rcases bases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> omega
  have h1 : a ≠ (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
      (hashed hash s)).getReg .x7 + 8 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [ptr] at hn
    rcases bases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · have v : ((BitVec.ofNat 64 0x88000) + 8).toNat = 0x88008 := by decide
      rw [v] at hn; omega
    · have v : ((BitVec.ofNat 64 0x83000) + 8).toNat = 0x83008 := by decide
      rw [v] at hn; omega
  have storeFrame : (stored hash s).getMem a = (hashed hash s).getMem a :=
    GroupedBalancedSignBottomTreeStoreData67.stored_frame
      (hashed hash s) a h0 h1
  have high : 0x81000 ≤ a.toNat := by
    rcases bases with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> omega
  have counterNe : a ≠ 0x810d8 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    simp at hn
    omega
  have advFrame : (advanced hash s).getMem a = (stored hash s).getMem a := by
    apply GroupedBalancedSignBottomTreeParentControl67.advance_frame
    · intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega
    · intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega
  change (GroupedBalancedSignBottomTreeParentControl67.branchState
    (GroupedBalancedSignBottomTreeFirstTickData67.advanced hash s)).getMem a = _
  rw [GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    advFrame,storeFrame,
    GroupedBalancedSignUpperTreeFirstTick67.hashed_high_frame hash s level
      witnessBase a levelWord witness levelBound witnessBound high counterNe]

theorem tick_control_frame (hash : Hash) (s : MachineState)
    (level witnessBase target : Nat) (a : Word)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
    (high : 0x81000 ≤ a.toNat) (low : a.toNat < 0x83000)
    (counterNe : a ≠ 0x810d8) (addressNe : a ≠ 0x81008) :
    (tick hash s).getMem a = s.getMem a := by
  change (GroupedBalancedSignBottomTreeParentControl67.branchState
    (GroupedBalancedSignBottomTreeFirstTickData67.advanced hash s)).getMem a = _
  rw [GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    GroupedBalancedSignBottomTreeFirstTickData67.advanced,
    GroupedBalancedSignBottomTreeParentControl67.advance_frame
      (stored hash s) a addressNe counterNe]
  exact stored_control_frame hash s level witnessBase target a levelWord witness
    levelBound witnessBound destination targetCase high low counterNe

theorem tick_pc (hash : Hash) (s : MachineState)
    (level witnessBase target : Nat)
    (pc : s.pc = 0x1e94)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (targetCase : target = 0x83000 ∨ target = 0x88000) :
    (tick hash s).pc =
      if (1 : Word) ≠ s.getMem 0x810d0 then 0x1f08 else 0x2058 := by
  have regs := GroupedBalancedSignBottomTreeParentControl67.advance_regs
    (stored hash s)
  have r6 : (advanced hash s).getReg .x6 = 1 := by
    change (GroupedBalancedSignBottomTreeParentAdvance67.advanceState
      (stored hash s)).getReg .x6 = 1
    rw [regs.1,
      stored_from_hashed hash s level witnessBase target 0x810d8 levelWord
        witness levelBound witnessBound destination targetCase (by decide),
      GroupedBalancedSignBottomTreeFirstTickData67.hashed_counter]
    decide
  have r7 : (advanced hash s).getReg .x7 = s.getMem 0x810d0 := by
    change (GroupedBalancedSignBottomTreeParentAdvance67.advanceState
      (stored hash s)).getReg .x7 = s.getMem 0x810d0
    rw [regs.2,
      stored_control_frame hash s level witnessBase target 0x810d0 levelWord
        witness levelBound witnessBound destination targetCase
        (by decide) (by decide) (by decide)]
  exact (GroupedBalancedSignBottomTreeParentControl67.branch_pc
    (advanced hash s)
      (GroupedBalancedSignBottomTreeFirstTickControl67.advanced_pc hash s pc)).trans
        (by rw [r6,r7])

#print axioms tick_control_frame
#print axioms tick_pc
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstControl67
