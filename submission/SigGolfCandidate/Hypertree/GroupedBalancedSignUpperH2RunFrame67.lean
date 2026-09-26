import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureWitnessAfter67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Invariant67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Run67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2WitnessFrame67


/-! Every H2 round leaves the four secret-key words untouched. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2RoundKey67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree GroupedBalancedUpperTree67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev Data := GroupedBalancedSignUpperH2Invariant67.Data
private abbrev advanced := GroupedBalancedSignUpperH2Tick67.advanced
private noncomputable abbrev round := GroupedBalancedSignUpperH2Round67.roundResult

theorem round_key (hash : Hash) (s : MachineState)
    (base leaf witnessBase : Nat) (chain : ChainMixed)
    (step : Nat) (seed : Reference.Digest)
    (data : Data hash s base leaf witnessBase chain step seed)
    (witnessLower : 0x20060 ≤ witnessBase)
    (witnessBound : witnessBase + 16*chain.val + 16 ≤ 0x80000)
    (j : Fin 4) :
    (round hash s).getMem (Signing.wordAddress 0x20 j.val) =
      s.getMem (Signing.wordAddress 0x20 j.val) := by
  let a := Signing.wordAddress 0x20 j.val
  have aSmall : a.toNat < 0x100 := by fin_cases j <;> decide
  have counterFrame := GroupedBalancedSignUpperH2Tick67.advanced_frame
    hash s data.source data.destination 0x81030
    (by decide) (by intro i; fin_cases i <;> decide)
  have witnessFrame := GroupedBalancedSignUpperH2Tick67.advanced_frame
    hash s data.source data.destination 0x810f0
    (by decide) (by intro i; fin_cases i <;> decide)
  have targetNat :
      (GroupedBalancedSignUpperCaptureWitnessAfter67.target (advanced hash s)).toNat =
        witnessBase + 16*chain.val := by
    exact GroupedBalancedSignUpperCaptureSafety67.pointer_nat
      (advanced hash s) witnessBase chain.val
      (witnessFrame.trans data.witness)
      (counterFrame.trans data.counter) chain.isLt witnessBound
  have targetNextNat :
      (GroupedBalancedSignUpperCaptureWitnessAfter67.target (advanced hash s) + 8).toNat =
        witnessBase + 16*chain.val + 8 := by
    rw [BitVec.toNat_add,targetNat]
    change (witnessBase+16*chain.val+8) % 2^64 = _
    rw [Nat.mod_eq_of_lt (by omega : witnessBase+16*chain.val+8 < 2^64)]
  have ne0 : a ≠ GroupedBalancedSignUpperCaptureWitnessAfter67.target (advanced hash s) := by
    intro eq
    have he := congrArg BitVec.toNat eq
    rw [targetNat] at he
    omega
  have ne1 : a ≠ GroupedBalancedSignUpperCaptureWitnessAfter67.target (advanced hash s) + 8 := by
    intro eq
    have he := congrArg BitVec.toNat eq
    rw [targetNextNat] at he
    omega
  have advFrame := GroupedBalancedSignUpperH2Tick67.advanced_frame
    hash s data.source data.destination a
    (by fin_cases j <;> decide)
    (by intro i; fin_cases i <;> fin_cases j <;> decide)
  change (GroupedBalancedSignUpperH2CaptureAny67.captureResult
    (advanced hash s)).getMem a = s.getMem a
  rw [GroupedBalancedSignUpperCaptureWitnessAfter67.capture_mem]
  unfold GroupedBalancedSignUpperCaptureWitnessAfter67.expectedMem
  split_ifs with e
  all_goals first
    | exact False.elim (ne1 e)
    | exact False.elim (ne0 e)
    | exact advFrame

#print axioms round_key
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2RoundKey67


/-! Preserve stack and upper control/table words across every H2 chain step. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2RunFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree GroupedBalancedUpperTree67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
noncomputable section
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

theorem round_frame (hash : Hash) (s : MachineState)
    (base leaf witnessBase : Nat) (chain : ChainMixed)
    (step : Nat) (seed : Reference.Digest)
    (data : Data hash s base leaf witnessBase chain step seed)
    (pc : s.pc = 0x1a38)
    (witnessBound : witnessBase + 16*chain.val + 16 ≤ 0x80000)
    (aligned : witnessBase % 8 = 0) :
    (round hash s).getReg .x2 = s.getReg .x2 ∧
    ∀ a : Word, 0x80600 ≤ a.toNat →
      (round hash s).getMem a = s.getMem a := by
  have safe := GroupedBalancedSignUpperH2Round67.safe_after_hash hash s
    data.source data.destination witnessBase chain.val
    data.witness data.counter chain.isLt witnessBound aligned
  obtain ⟨safeDigit,safeWitness,safeWitnessNext,low0,low1⟩ := safe
  obtain ⟨n,nBound,path,nextPc,nextStep,nextMax,nextChain,nextService,
    nextSource,nextBits,nextDestination,highFrame⟩ :=
      GroupedBalancedSignUpperH2Round67.round_trace hash s pc
        data.service data.source data.bits data.destination
        safeDigit safeWitness safeWitnessNext low0 low1
  exact ⟨GroupedBalancedSignUpperH2Round67.round_stack hash s,highFrame⟩

theorem run_remaining_framed (hash : Hash) (s : MachineState)
    (base leaf witnessBase : Nat) (chain : ChainMixed)
    (step remaining : Nat) (seed : Reference.Digest)
    (positive : 0 < remaining)
    (total : step + remaining = maxDigit chain)
    (data : Data hash s base leaf witnessBase chain step seed)
    (pc : s.pc = 0x1a38)
    (baseBound : base < 256)
    (witnessBound : witnessBase + 16*chain.val + 16 ≤ 0x80000)
    (witnessLower : 0x20060 ≤ witnessBase)
    (aligned : witnessBase % 8 = 0) :
    ∃ (n : Nat) (final : MachineState),
      n ≤ 30*remaining ∧
      Trace hash image s n (n + 7*remaining) remaining remaining final ∧
      final.pc = 0x1ab0 ∧
      Data hash final base leaf witnessBase chain (step+remaining) seed ∧
      final.getReg .x2 = s.getReg .x2 ∧
      (∀ a : Word, 0x80600 ≤ a.toNat → final.getMem a = s.getMem a) ∧
      (∀ j : Fin 4,
        final.getMem (Signing.wordAddress 0x20 j.val) =
          s.getMem (Signing.wordAddress 0x20 j.val)) ∧
      (∀ a : Word, a.toNat < 0x80000 →
        a ≠ GroupedBalancedSignUpperH2WitnessFrame67.slot witnessBase chain 0 →
        a ≠ GroupedBalancedSignUpperH2WitnessFrame67.slot witnessBase chain 1 →
        final.getMem a = s.getMem a) := by
  induction remaining generalizing s step with
  | zero => omega
  | succ rest ih =>
    have stepLt : step < maxDigit chain := by omega
    obtain ⟨n,nBound,first,nextPC,nextData⟩ :=
      GroupedBalancedSignUpperH2Invariant67.round_data hash s
        base leaf witnessBase chain step seed data pc baseBound stepLt
        witnessBound aligned
    obtain ⟨stackFrame,highFrame⟩ :=
      round_frame hash s base leaf witnessBase chain step seed data pc
        witnessBound aligned
    have keyFrame (j : Fin 4) :=
      GroupedBalancedSignUpperH2RoundKey67.round_key hash s
        base leaf witnessBase chain step seed data witnessLower
        witnessBound j
    by_cases last : rest = 0
    · subst rest
      have done : (round hash s).pc = 0x1ab0 := by
        rw [nextPC]
        have eq : step+1 = maxDigit chain := by omega
        rw [eq]
        simp
      refine ⟨n,round hash s,by omega,?_,done,?_,stackFrame,highFrame,
        keyFrame,?_⟩
      · simpa only [Nat.mul_one] using first
      · simpa only [Nat.add_zero] using nextData
      · intro a low ne0 ne1
        exact GroupedBalancedSignUpperH2WitnessFrame67.round_other hash s
          base leaf witnessBase chain step seed data witnessBound a low ne0 ne1
    · have more : step+1 < maxDigit chain := by omega
      have nextStart : (round hash s).pc = 0x1a38 := by
        rw [nextPC,if_pos (word_ne_small
          (step+1) (maxDigit chain) more
          (GroupedBalancedSignUpperH2Invariant67.max_bounds chain).2)]
      obtain ⟨m,final,mBound,second,done,finalData,stackLater,highLater,
        keyLater,lowLater⟩ :=
        ih (round hash s) (step+1) (by omega : 0 < rest)
          (by omega) nextData nextStart
      refine ⟨n+m,final,by omega,?_,done,?_,?_,?_,?_,?_⟩
      · have both := first.trans second
        convert both using 1 <;> omega
      · have arith : step + 1 + rest = step + (rest+1) := by omega
        simpa only [arith] using finalData
      · exact stackLater.trans stackFrame
      · intro a high
        exact (highLater a high).trans (highFrame a high)
      · intro j
        exact (keyLater j).trans (keyFrame j)
      · intro a low ne0 ne1
        exact (lowLater a low ne0 ne1).trans
          (GroupedBalancedSignUpperH2WitnessFrame67.round_other hash s
            base leaf witnessBase chain step seed data witnessBound a low ne0 ne1)

#print axioms run_remaining_framed
end
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2RunFrame67
