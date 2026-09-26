import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstControl67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeProtectedTick67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeInnerTickData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeTickStack67


/-! Upper parent ticks preserve the caller stack and other high memory. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeHighFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem first_high (hash : Hash) (s : MachineState)
    (level witnessBase target : Nat) (a : Word)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase+16*level+16 ≤ 0x80000)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
    (high : 0x90000 ≤ a.toNat) :
    (GroupedBalancedSignBottomTreeFirstTickData67.tickState hash s).getMem a =
      s.getMem a := by
  let hashed := GroupedBalancedSignBottomTreeFirstTickData67.hashed hash s
  let stored := GroupedBalancedSignBottomTreeFirstTickData67.stored hash s
  let ptr := GroupedBalancedSignBottomTreeHashStorePtr67.storeState hashed
  have targetPtr := GroupedBalancedSignUpperTreeFirstTick67.output_pointer hash s
    level witnessBase target levelWord witness levelBound witnessBound destination
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
    · have v : ((BitVec.ofNat 64 0x83000)+8).toNat=0x83008 := by decide
      rw [v] at hn; omega
    · have v : ((BitVec.ofNat 64 0x88000)+8).toNat=0x88008 := by decide
      rw [v] at hn; omega
  have storeFrame : stored.getMem a = hashed.getMem a :=
    GroupedBalancedSignBottomTreeStoreData67.stored_frame hashed a ne0 ne1
  have hashFrame : hashed.getMem a = s.getMem a :=
    GroupedBalancedSignUpperTreeFirstTick67.hashed_high_frame hash s level
      witnessBase a levelWord witness levelBound witnessBound (by omega) (by
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

#print axioms first_high
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeHighFrame67


/-! Exact resource trace of a reused upper parent level, for 1–8 parents. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeParentTrace67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev first := GroupedBalancedSignBottomTreeFirstTickData67.tickState
private abbrev later := GroupedBalancedSignBottomTreeInnerTickFrame67.tickState

def Stable (a : Word) : Prop :=
  0x81000 ≤ a.toNat ∧ a.toNat < 0x83000 ∧
    a ≠ 0x81008 ∧ a ≠ 0x810d8

structure At (limit source target n : Nat) (s : MachineState) : Prop where
  pc : s.pc = 0x1f08
  counter : s.getMem 0x810d8 = BitVec.ofNat 64 n
  count : s.getMem 0x810d0 = BitVec.ofNat 64 limit
  sourcePtr : s.getMem 0x810c0 = BitVec.ofNat 64 source
  targetPtr : s.getMem 0x810c8 = BitVec.ofNat 64 target

structure Done (limit source target : Nat) (s : MachineState) : Prop where
  pc : s.pc = 0x2058
  counter : s.getMem 0x810d8 = BitVec.ofNat 64 limit
  count : s.getMem 0x810d0 = BitVec.ofNat 64 limit
  sourcePtr : s.getMem 0x810c0 = BitVec.ofNat 64 source
  targetPtr : s.getMem 0x810c8 = BitVec.ofNat 64 target

theorem one_tick (hash : Hash) (limit source target n : Nat)
    (s : MachineState)
    (holds : At limit source target n s)
    (small : limit ≤ 8) (nBound : n < limit)
    (sourceCase : source = 0x83000 ∨ source = 0x88000)
    (targetCase : target = 0x83000 ∨ target = 0x88000) :
    Trace hash image s 84 91 1 1 (later hash s) ∧
    (n+1 < limit → At limit source target (n+1) (later hash s)) ∧
    (n+1 = limit → Done limit source target (later hash s)) ∧
    (∀ a, Stable a → (later hash s).getMem a = s.getMem a) ∧
    (later hash s).getReg .x2 = s.getReg .x2 ∧
    (∀ a : Word, 0x90000 ≤ a.toNat →
      (later hash s).getMem a = s.getMem a) := by
  have countBound : n < 512 := by omega
  have trace := GroupedBalancedSignBottomTreeInnerTickData67.tick_trace
    hash s n source target holds.pc holds.counter holds.sourcePtr
    holds.targetPtr countBound sourceCase targetCase
  have pc := GroupedBalancedSignBottomTreeInnerTickData67.tick_pc
    hash s n target holds.pc holds.counter holds.targetPtr countBound targetCase
  have counter : (later hash s).getMem 0x810d8 = BitVec.ofNat 64 (n+1) := by
    rw [GroupedBalancedSignBottomTreeInnerTickFrame67.tick_count
      hash s n target holds.counter holds.targetPtr countBound targetCase,
      holds.counter]
    simp [BitVec.ofNat_add]
  have frame (a : Word) (hi : 0x81000 ≤ a.toNat) (lo : a.toNat < 0x83000)
      (ne08 : a ≠ 0x81008) (ned8 : a ≠ 0x810d8) :
      (later hash s).getMem a = s.getMem a :=
    GroupedBalancedSignBottomTreeInnerTickFrame67.tick_control_frame
      hash s n target a holds.counter holds.targetPtr countBound targetCase
      hi lo ne08 ned8
  have count : (later hash s).getMem 0x810d0 = BitVec.ofNat 64 limit := by
    rw [frame 0x810d0 (by decide) (by decide) (by decide) (by decide)]
    exact holds.count
  have sourcePtr : (later hash s).getMem 0x810c0 = BitVec.ofNat 64 source := by
    rw [frame 0x810c0 (by decide) (by decide) (by decide) (by decide)]
    exact holds.sourcePtr
  have targetPtr : (later hash s).getMem 0x810c8 = BitVec.ofNat 64 target := by
    rw [frame 0x810c8 (by decide) (by decide) (by decide) (by decide)]
    exact holds.targetPtr
  have condition : s.getMem 0x810d8 + 1 = BitVec.ofNat 64 (n+1) := by
    rw [holds.counter]
    simp [BitVec.ofNat_add]
  refine ⟨trace,?_,?_,?_,
    GroupedBalancedSignBottomTreeTickStack67.inner_tick_sp hash s,?_⟩
  · intro next
    have neq : BitVec.ofNat 64 (n+1) ≠ BitVec.ofNat 64 limit := by
      intro h
      have hn := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : n+1 < 2^64),
        Nat.mod_eq_of_lt (by omega : limit < 2^64)] at hn
      omega
    have nextPc : (later hash s).pc = 0x1f08 := by
      rw [condition,holds.count] at pc
      simpa only [if_pos neq] using pc
    exact ⟨nextPc,counter,count,sourcePtr,targetPtr⟩
  · intro last
    have eq : BitVec.ofNat 64 (n+1) = BitVec.ofNat 64 limit := by rw [last]
    have donePc : (later hash s).pc = 0x2058 := by
      rw [condition,holds.count] at pc
      simpa only [eq, ne_eq, not_true_eq_false, ite_false] using pc
    exact ⟨donePc,by simpa only [last] using counter,count,sourcePtr,targetPtr⟩
  · intro a ⟨hi,lo,ne08,ned8⟩
    exact frame a hi lo ne08 ned8
  · intro a high
    exact GroupedBalancedSignBottomTreeProtectedTick67.inner_high hash s n
      target a holds.counter holds.targetPtr (by omega) targetCase high

theorem fold (hash : Hash) (limit source target n : Nat) (s : MachineState)
    (holds : At limit source target n s)
    (small : limit ≤ 8) (nBound : n < limit)
    (sourceCase : source = 0x83000 ∨ source = 0x88000)
    (targetCase : target = 0x83000 ∨ target = 0x88000) :
    ∃ final : MachineState,
      Trace hash image s (84*(limit-n)) (91*(limit-n))
        (limit-n) (limit-n) final ∧
      Done limit source target final ∧
      (∀ a, Stable a → final.getMem a = s.getMem a) ∧
      final.getReg .x2 = s.getReg .x2 ∧
      (∀ a : Word, 0x90000 ≤ a.toNat →
        final.getMem a = s.getMem a) := by
  suffices H : ∀ remaining n (s : MachineState), remaining = limit-n →
      n < limit → At limit source target n s →
      ∃ final,
        Trace hash image s (84*remaining) (91*remaining)
          remaining remaining final ∧
        Done limit source target final ∧
        (∀ a, Stable a → final.getMem a = s.getMem a) ∧
        final.getReg .x2 = s.getReg .x2 ∧
        (∀ a : Word, 0x90000 ≤ a.toNat →
          final.getMem a = s.getMem a) by
    exact H (limit-n) n s rfl nBound holds
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
      intro n s remEq nBound holds
      obtain ⟨tick,next,last,tickFrame,tickSp,tickHigh⟩ := one_tick hash limit source target n s
        holds small nBound sourceCase targetCase
      by_cases more : n+1 < limit
      · obtain ⟨final,rest,done,restFrame,restSp,restHigh⟩ := ih (limit-(n+1)) (by omega)
          (n+1) (later hash s) (by omega) more (next more)
        refine ⟨final,?_,done,?_,?_,?_⟩
        · convert tick.trans rest using 1 <;> omega
        · intro a safe
          exact (restFrame a safe).trans (tickFrame a safe)
        · exact restSp.trans tickSp
        · intro a high
          exact (restHigh a high).trans (tickHigh a high)
      · have atEnd : n+1=limit := by omega
        refine ⟨later hash s,?_,last atEnd,tickFrame,tickSp,tickHigh⟩
        have one : remaining = 1 := by omega
        simpa only [one,Nat.mul_one] using tick

theorem first_level (hash : Hash) (s : MachineState)
    (level witnessBase limit source target : Nat)
    (pc : s.pc = 0x1e94)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000)
    (witnessAligned : witnessBase % 8 = 0)
    (selectedBound : (s.getMem 0x810e8).toNat < 1024)
    (count : s.getMem 0x810d0 = BitVec.ofNat 64 limit)
    (sourcePtr : s.getMem 0x810c0 = BitVec.ofNat 64 source)
    (targetPtr : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (bases : (source = 0x83000 ∧ target = 0x88000) ∨
      (source = 0x88000 ∧ target = 0x83000))
    (positive : 0 < limit) (small : limit ≤ 8) :
    ∃ final : MachineState,
      Trace hash image s (113+84*(limit-1)) (120+91*(limit-1))
        limit limit final ∧
      Done limit source target final ∧
      (∀ a, Stable a → final.getMem a = s.getMem a) ∧
      final.getReg .x2 = s.getReg .x2 ∧
      (∀ a : Word, 0x90000 ≤ a.toNat →
        final.getMem a = s.getMem a) := by
  have sourceCase : source = 0x83000 ∨ source = 0x88000 := by
    rcases bases with ⟨h,_⟩ | ⟨h,_⟩
    · exact Or.inl h
    · exact Or.inr h
  have targetCase : target = 0x83000 ∨ target = 0x88000 := by
    rcases bases with ⟨_,h⟩ | ⟨_,h⟩
    · exact Or.inr h
    · exact Or.inl h
  have firstTrace := GroupedBalancedSignUpperTreeFirstTick67.executes hash s
    level witnessBase source target pc levelWord witness levelBound
    witnessBound witnessAligned selectedBound sourcePtr sourceCase targetPtr
    targetCase
  have firstCounter : (first hash s).getMem 0x810d8 = 1 :=
    GroupedBalancedSignUpperTreeFirstControl67.tick_count hash s level
      witnessBase target levelWord witness levelBound witnessBound targetPtr
      targetCase
  have firstPc := GroupedBalancedSignUpperTreeFirstControl67.tick_pc hash s
    level witnessBase target pc levelWord witness levelBound witnessBound
    targetPtr targetCase
  have frame (a : Word) (hi : 0x81000 ≤ a.toNat)
      (lo : a.toNat < 0x83000) (neCounter : a ≠ 0x810d8)
      (neAddr : a ≠ 0x81008) :
      (first hash s).getMem a = s.getMem a :=
    GroupedBalancedSignUpperTreeFirstControl67.tick_control_frame hash s
      level witnessBase target a levelWord witness levelBound witnessBound
      targetPtr targetCase hi lo neCounter neAddr
  have firstCount : (first hash s).getMem 0x810d0 =
      BitVec.ofNat 64 limit := by
    rw [frame 0x810d0 (by decide) (by decide) (by decide) (by decide)]
    exact count
  have firstSource : (first hash s).getMem 0x810c0 =
      BitVec.ofNat 64 source := by
    rw [frame 0x810c0 (by decide) (by decide) (by decide) (by decide)]
    exact sourcePtr
  have firstTarget : (first hash s).getMem 0x810c8 =
      BitVec.ofNat 64 target := by
    rw [frame 0x810c8 (by decide) (by decide) (by decide) (by decide)]
    exact targetPtr
  by_cases more : 1 < limit
  · have neq : (1:Word) ≠ BitVec.ofNat 64 limit := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : limit < 2^64)] at hn
      have oneWord : (1:Word).toNat = 1 := by decide
      rw [oneWord] at hn
      omega
    have pcNext : (first hash s).pc = 0x1f08 := by
      rw [count] at firstPc
      simpa only [if_pos neq] using firstPc
    have inv : At limit source target 1 (first hash s) :=
      ⟨pcNext,firstCounter,firstCount,firstSource,firstTarget⟩
    obtain ⟨final,rest,done,restFrame,restSp,restHigh⟩ := fold hash limit source target 1
      (first hash s) inv small more sourceCase targetCase
    refine ⟨final,?_,done,?_,?_,?_⟩
    have countEq : 1 + (limit-1) = limit := by omega
    simpa only [countEq] using firstTrace.trans rest
    intro a ⟨hi,lo,ne08,ned8⟩
    exact (restFrame a ⟨hi,lo,ne08,ned8⟩).trans
      (frame a hi lo ned8 ne08)
    exact restSp.trans
      (GroupedBalancedSignBottomTreeTickStack67.first_tick_sp hash s)
    intro a high
    exact (restHigh a high).trans
      (GroupedBalancedSignUpperTreeHighFrame67.first_high hash s level
        witnessBase target a levelWord witness levelBound witnessBound
        targetPtr targetCase high)
  · have one : limit=1 := by omega
    have pcDone : (first hash s).pc = 0x2058 := by
      rw [count,one] at firstPc
      simpa using firstPc
    refine ⟨first hash s,?_,⟨pcDone,by simpa [one] using firstCounter,
      firstCount,firstSource,firstTarget⟩,?_,
      GroupedBalancedSignBottomTreeTickStack67.first_tick_sp hash s,?_⟩
    · simpa [one] using firstTrace
    · intro a ⟨hi,lo,ne08,ned8⟩
      exact frame a hi lo ned8 ne08
    · intro a high
      exact GroupedBalancedSignUpperTreeHighFrame67.first_high hash s level
        witnessBase target a levelWord witness levelBound witnessBound
        targetPtr targetCase high

#print axioms first_level
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeParentTrace67
