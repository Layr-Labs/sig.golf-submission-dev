import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsFullChain67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenChainsFold67

/-! The keygen H1/H2 control frame survives all 67 WOTS chains. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsChainsFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenRootControlsTick67
open GroupedBalancedKeygenRootControlsFullChain67
open GroupedBalancedKeygenCacheTick67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem regular_pair_control (hash : Hash) (s final : MachineState) (k : Nat)
    (pc : s.pc = 0x1050) (bound : k < 32)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 (2*k))
    (level : s.getMem 0x81000 = 156)
    (trace : Trace hash image s 325 374 7 7 final) :
    ControlFrame s final ∧ LowFrame s final := by
  have even : s.getMem 0x81030 &&& 1 = 0 := by
    rw [counter]
    interval_cases k <;> decide
  obtain ⟨mid,first,midPC,midCounter,midLevel,_⟩ :=
    GroupedBalancedKeygenEvenChain67.regular_even_chain hash s (2*k)
      pc (by omega) counter even level
  have firstFrame := regular_even_control hash s mid (2*k)
    pc (by omega) counter even level first
  have odd : mid.getMem 0x81030 &&& 1 ≠ 0 := by
    rw [midCounter]
    interval_cases k <;> decide
  obtain ⟨made,second,_,_,_,_⟩ :=
    GroupedBalancedKeygenOddChain67.regular_odd_chain hash mid (2*k+1)
      midPC (by omega) midCounter odd
  have secondFrame := regular_odd_control hash mid made (2*k+1)
    midPC (by omega) midCounter odd second
  have total : Trace hash image s 325 374 7 7 made := by
    simpa only [Nat.reduceAdd] using first.trans second
  have same : final = made := Trace.deterministic trace total
  rw [same]
  exact ⟨firstFrame.1.trans secondFrame.1,
    firstFrame.2.trans secondFrame.2⟩

theorem regular_pairs_control (hash : Hash) (s final : MachineState) (k : Nat)
    (bound : k ≤ 32) (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 0)
    (level : s.getMem 0x81000 = 156)
    (trace : Trace hash image s (325*k) (374*k) (7*k) (7*k) final) :
    ControlFrame s final ∧ LowFrame s final := by
  induction k generalizing final with
  | zero =>
      have same : final = s := Trace.deterministic trace (Trace.refl s)
      rw [same]
      exact ⟨ControlFrame.refl s,LowFrame.refl s⟩
  | succ k ih =>
      obtain ⟨mid,first,midPC,midCounter,midLevel,_⟩ :=
        GroupedBalancedKeygenChainsFold67.regular_pairs hash s k
          (by omega) pc counter level
      have firstFrame := ih mid (by omega) first
      obtain ⟨made,second,_,_,_,_⟩ :=
        GroupedBalancedKeygenChainsFold67.regular_pair hash mid k
          midPC (by omega) midCounter midLevel
      have secondFrame := regular_pair_control hash mid made k
        midPC (by omega) midCounter midLevel second
      have total : Trace hash image s (325*(k+1)) (374*(k+1))
          (7*(k+1)) (7*(k+1)) made := by
        simpa only [Nat.mul_succ,Nat.add_comm] using first.trans second
      have same : final = made := Trace.deterministic trace total
      rw [same]
      exact ⟨firstFrame.1.trans secondFrame.1,
        firstFrame.2.trans secondFrame.2⟩

theorem all_chains_control (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 0)
    (level : s.getMem 0x81000 = 156)
    (trace : Trace hash image s 10985 12714 247 247 final) :
    ControlFrame s final ∧ LowFrame s final := by
  obtain ⟨after64,first,pc64,counter64,level64,_⟩ :=
    GroupedBalancedKeygenChainsFold67.regular_pairs hash s 32
      (by decide) pc counter level
  have frame64 := regular_pairs_control hash s after64 32
    (by decide) pc counter level first
  have even64 : after64.getMem 0x81030 &&& 1 = 0 := by
    rw [counter64]
    decide
  obtain ⟨after65,second,pc65,counter65,level65,_⟩ :=
    GroupedBalancedKeygenEvenChain67.regular_even_chain hash after64 64
      pc64 (by decide) (by simpa using counter64) even64 level64
  have frame65 := regular_even_control hash after64 after65 64 pc64
    (by decide) (by simpa using counter64) even64 level64 second
  have odd65 : after65.getMem 0x81030 &&& 1 ≠ 0 := by
    rw [counter65]
    decide
  obtain ⟨after66,third,pc66,counter66,level66,_⟩ :=
    GroupedBalancedKeygenOddChain67.special65_odd_chain hash after65
      pc65 (by simpa using counter65) odd65
  have frame66 := special65_control hash after65 after66 pc65
    (by simpa using counter65) odd65 third
  have even66 : after66.getMem 0x81030 &&& 1 = 0 := by
    rw [counter66]
    decide
  obtain ⟨made,fourth,_,_,_,_⟩ :=
    GroupedBalancedKeygenEvenChain67.special66_even_chain hash after66
      pc66 counter66 even66 (level66.trans level65)
  have frame67 := special66_control hash after66 made pc66 counter66
    even66 (level66.trans level65) fourth
  have total : Trace hash image s 10985 12714 247 247 made := by
    simpa only [Nat.reduceMul,Nat.reduceAdd] using
      ((first.trans second).trans third).trans fourth
  have same : final = made := Trace.deterministic trace total
  rw [same]
  exact ⟨((frame64.1.trans frame65.1).trans frame66.1).trans frame67.1,
    ((frame64.2.trans frame65.2).trans frame66.2).trans frame67.2⟩

#print axioms regular_pair_control
#print axioms all_chains_control
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsChainsFold67
