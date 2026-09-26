import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2StartData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2RunFrame67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperUnselectedCapture67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperUnselectedRun67. -/
section
/-! An unselected upper leaf never writes the low-memory WOTS witness. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperUnselectedCapture67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree GroupedBalancedUpperTree67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
noncomputable section
private abbrev Data := GroupedBalancedSignUpperH2Invariant67.Data
private abbrev advanced := GroupedBalancedSignUpperH2Tick67.advanced
private abbrev round := GroupedBalancedSignUpperH2Round67.roundResult

theorem initial_low (s : MachineState)
    (unselected : s.getMem 0x810e0≠s.getMem 0x810e8)
    (a : Word) :
    (GroupedBalancedSignUpperInitialCapture67.captureResult s).getMem a =
      s.getMem a := by
  classical
  change s.getMem 528608#64 ≠ s.getMem 528616#64 at unselected
  simp [GroupedBalancedSignUpperInitialCapture67.captureResult,
    unselected,GroupedBalancedSignUpperCaptureSelector67.selector_frame]

theorem after_low (s : MachineState)
    (unselected : s.getMem 0x810e0≠s.getMem 0x810e8)
    (a : Word) :
    (GroupedBalancedSignUpperH2CaptureAny67.captureResult s).getMem a =
      s.getMem a := by
  classical
  change s.getMem 528608#64 ≠ s.getMem 528616#64 at unselected
  simp [GroupedBalancedSignUpperH2CaptureAny67.captureResult,
    unselected,GroupedBalancedSignUpperH2Exit67.branchState,
    execInstrBr,GroupedBalancedSignUpperCaptureSelectorAfter67.selector_frame]

theorem advanced_low (hash : Hash) (s : MachineState)
    (source : s.getReg .x10=0x80000)
    (destination : s.getReg .x12=0x80020)
    (a : Word) (low : a.toNat<0x80000) :
    (advanced hash s).getMem a=s.getMem a := by
  apply GroupedBalancedSignUpperH2Tick67.advanced_frame hash s
    source destination a
  · intro eq
    have hn := congrArg BitVec.toNat eq
    have numeric : (0x80000 : Word).toNat=0x80000 := by decide
    rw [numeric] at hn
    omega
  · intro j eq
    have hn := congrArg BitVec.toNat eq
    simp only [Signing.wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := j.isLt; omega :
        0x80020+8*j.val<2^64)] at hn
    omega

theorem advanced_selected (hash : Hash) (s : MachineState)
    (source : s.getReg .x10=0x80000)
    (destination : s.getReg .x12=0x80020)
    (unselected : s.getMem 0x810e0≠s.getMem 0x810e8) :
    (advanced hash s).getMem 0x810e0≠
      (advanced hash s).getMem 0x810e8 := by
  rw [GroupedBalancedSignUpperH2Tick67.advanced_frame hash s source
      destination 0x810e0 (by decide)
      (by intro j; fin_cases j <;> decide),
    GroupedBalancedSignUpperH2Tick67.advanced_frame hash s source
      destination 0x810e8 (by decide)
      (by intro j; fin_cases j <;> decide)]
  exact unselected

theorem round_low (hash : Hash) (s : MachineState)
    (source : s.getReg .x10=0x80000)
    (destination : s.getReg .x12=0x80020)
    (unselected : s.getMem 0x810e0≠s.getMem 0x810e8)
    (a : Word) (low : a.toNat<0x80000) :
    (round hash s).getMem a=s.getMem a := by
  change (GroupedBalancedSignUpperH2CaptureAny67.captureResult
    (advanced hash s)).getMem a=s.getMem a
  rw [after_low (advanced hash s)
      (advanced_selected hash s source destination unselected) a]
  exact advanced_low hash s source destination a low

#print axioms initial_low
#print axioms after_low
#print axioms round_low
end
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperUnselectedCapture67

end

/-! Every H2 round of an unselected WOTS leaf preserves all low memory. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperUnselectedRun67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree GroupedBalancedUpperTree67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
noncomputable section
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev Data := GroupedBalancedSignUpperH2Invariant67.Data
private abbrev round := GroupedBalancedSignUpperH2Round67.roundResult

theorem run_remaining (hash : Hash) (s : MachineState)
    (base leaf witnessBase : Nat) (chain : ChainMixed)
    (step remaining : Nat) (seed : Reference.Digest)
    (positive : 0<remaining)
    (total : step+remaining=maxDigit chain)
    (data : Data hash s base leaf witnessBase chain step seed)
    (pc : s.pc=0x1a38)
    (unselected : s.getMem 0x810e0≠s.getMem 0x810e8)
    (baseBound : base<256)
    (witnessBound : witnessBase+16*chain.val+16≤0x80000)
    (aligned : witnessBase%8=0) :
    ∃ (n : Nat) (final : MachineState),
      n≤30*remaining ∧
      Trace hash image s n (n+7*remaining) remaining remaining final ∧
      final.pc=0x1ab0 ∧
      Data hash final base leaf witnessBase chain (step+remaining) seed ∧
      final.getMem 0x810e0≠final.getMem 0x810e8 ∧
      final.getReg .x2=s.getReg .x2 ∧
      (∀ a : Word, 0x80600≤a.toNat →
        final.getMem a=s.getMem a) ∧
      (∀ a : Word, a.toNat<0x80000 →
        final.getMem a=s.getMem a) := by
  induction remaining generalizing s step with
  | zero => omega
  | succ rest ih =>
    have stepLt : step<maxDigit chain := by omega
    obtain ⟨n,nBound,first,nextPC,nextData⟩ :=
      GroupedBalancedSignUpperH2Invariant67.round_data hash s
        base leaf witnessBase chain step seed data pc baseBound stepLt
        witnessBound aligned
    have lowFrame :=
      GroupedBalancedSignUpperUnselectedCapture67.round_low hash s
        data.source data.destination unselected
    obtain ⟨stackFrame,highFrame⟩ :=
      GroupedBalancedSignUpperH2RunFrame67.round_frame hash s
        base leaf witnessBase chain step seed data pc witnessBound
        aligned
    have nextUnselected : (round hash s).getMem 0x810e0≠
        (round hash s).getMem 0x810e8 := by
      rw [highFrame 0x810e0 (by decide),
        highFrame 0x810e8 (by decide)]
      exact unselected
    by_cases last : rest=0
    · subst rest
      have done : (round hash s).pc=0x1ab0 := by
        rw [nextPC]
        have eq : step+1=maxDigit chain := by omega
        rw [eq]
        simp
      refine ⟨n,round hash s,by omega,?_,done,?_,nextUnselected,
        stackFrame,highFrame,?_⟩
      · simpa only [Nat.mul_one] using first
      · simpa only [Nat.add_zero] using nextData
      · intro a low
        exact lowFrame a low
    · have more : step+1<maxDigit chain := by omega
      have ne : (BitVec.ofNat 64 (step+1) : Word) ≠
          BitVec.ofNat 64 (maxDigit chain) := by
        intro eq
        have hn := congrArg BitVec.toNat eq
        have maxBound := (GroupedBalancedSignUpperH2Invariant67.max_bounds
          chain).2
        simp only [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : step+1<2^64),
          Nat.mod_eq_of_lt (by omega : maxDigit chain<2^64)] at hn
        omega
      have nextPc : (round hash s).pc=0x1a38 := by
        rw [nextPC,if_pos ne]
      obtain ⟨m,final,mBound,second,done,finalData,finalUnselected,
        stackLater,highLater,lowLater⟩ :=
        ih (round hash s) (step+1) (by omega : 0<rest)
          (by omega) nextData nextPc nextUnselected
      refine ⟨n+m,final,by omega,?_,done,?_,finalUnselected,?_,
        ?_,?_⟩
      · have both := first.trans second
        convert both using 1 <;> omega
      · have arith : step+1+rest=step+(rest+1) := by omega
        simpa only [arith] using finalData
      · exact stackLater.trans stackFrame
      · intro a high
        exact (highLater a high).trans (highFrame a high)
      · intro a low
        exact (lowLater a low).trans (lowFrame a low)

#print axioms run_remaining
end
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperUnselectedRun67
