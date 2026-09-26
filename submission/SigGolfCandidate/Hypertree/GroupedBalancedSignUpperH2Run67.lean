import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Invariant67

/-! A complete 3-, 8-, or 10-step direct67 upper WOTS chain. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Run67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedUpperTree67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
noncomputable section H2Run
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev Data := GroupedBalancedSignUpperH2Invariant67.Data
private abbrev round := GroupedBalancedSignUpperH2Round67.roundResult

private theorem word_ne_small (a b : Nat) (lt : a < b) (bound : b ≤ 10) :
    (BitVec.ofNat 64 a : Word) ≠ BitVec.ofNat 64 b := by
  intro eq
  have hn := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : a < 2^64),
    Nat.mod_eq_of_lt (by omega : b < 2^64)] at hn
  omega

theorem run_remaining (hash : Hash) (s : MachineState)
    (base leaf witnessBase : Nat) (chain : ChainMixed)
    (step remaining : Nat) (seed : Reference.Digest)
    (positive : 0 < remaining)
    (total : step + remaining = maxDigit chain)
    (data : Data hash s base leaf witnessBase chain step seed)
    (pc : s.pc = 0x1a38)
    (baseBound : base < 256)
    (witnessBound : witnessBase + 16*chain.val + 16 ≤ 0x80000)
    (aligned : witnessBase % 8 = 0) :
    ∃ (n : Nat) (final : MachineState),
      n ≤ 30*remaining ∧
      Trace hash image s n (n + 7*remaining) remaining remaining final ∧
      final.pc = 0x1ab0 ∧
      Data hash final base leaf witnessBase chain (step+remaining) seed := by
  induction remaining generalizing s step with
  | zero => omega
  | succ rest ih =>
    have stepLt : step < maxDigit chain := by omega
    obtain ⟨n,nBound,first,nextPC,nextData⟩ :=
      GroupedBalancedSignUpperH2Invariant67.round_data hash s
        base leaf witnessBase chain step seed data pc baseBound stepLt
        witnessBound aligned
    by_cases last : rest = 0
    · subst rest
      have done : (round hash s).pc = 0x1ab0 := by
        rw [nextPC]
        have eq : step+1 = maxDigit chain := by omega
        rw [eq]
        simp
      refine ⟨n,round hash s,by omega,?_,done,?_⟩
      · simpa only [Nat.mul_one] using first
      · simpa only [Nat.add_zero] using nextData
    · have remainingPositive : 0 < rest := by omega
      have more : step+1 < maxDigit chain := by omega
      have nextStart : (round hash s).pc = 0x1a38 := by
        rw [nextPC,if_pos (word_ne_small (step+1) (maxDigit chain)
          more (GroupedBalancedSignUpperH2Invariant67.max_bounds chain).2)]
      obtain ⟨m,final,mBound,second,done,finalData⟩ :=
        ih (round hash s) (step+1) remainingPositive
          (by omega) nextData nextStart
      refine ⟨n+m,final,by omega,?_,done,?_⟩
      · have both := first.trans second
        convert both using 1 <;> omega
      · have arith : step + 1 + rest = step + (rest+1) := by omega
        simpa only [arith] using finalData

#print axioms run_remaining
end H2Run
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Run67
