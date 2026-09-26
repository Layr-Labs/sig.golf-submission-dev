import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Invariant67
import SigGolfCandidate.Hypertree.SignMemory
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureWitnessAfter67

/-! A WOTS H2 round only changes its own selected witness pair below the
hash input buffer. This frame is used to keep earlier witness chains intact. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2WitnessFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree GroupedBalancedUpperTree67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
noncomputable section
private abbrev Data := GroupedBalancedSignUpperH2Invariant67.Data
private abbrev round := GroupedBalancedSignUpperH2Round67.roundResult
private abbrev advanced := GroupedBalancedSignUpperH2Tick67.advanced
private abbrev target := GroupedBalancedSignUpperCaptureWitnessAfter67.target

def slot (witnessBase : Nat) (chain : ChainMixed) (j : Fin 2) : Word :=
  Signing.wordAddress (witnessBase + 16*chain.val) j.val

def digitAddress (chain : ChainMixed) : Word :=
  BitVec.ofNat 64 (0x80600+chain.val)

theorem digit_byte_frame (s t : MachineState) (chain : ChainMixed)
    (frame : ∀ a : Word, 0x80600 ≤ a.toNat → t.getMem a=s.getMem a) :
    t.getByte (digitAddress chain) = s.getByte (digitAddress chain) := by
  have bound : 0x80600+chain.val<2^64 := by have := chain.isLt; omega
  have high : 0x80600 ≤
      (Signing.wordAddress 0x80600 (chain.val/8)).toNat := by
    change 0x80600 ≤ (BitVec.ofNat 64 (0x80600+8*(chain.val/8))).toNat
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := chain.isLt; omega)]
    omega
  simp only [digitAddress,
    Signing.getByte_word t 0x80600 chain.val (by decide) bound,
    Signing.getByte_word s 0x80600 chain.val (by decide) bound,
    frame _ high]

theorem digit_byte_frame_except (s t : MachineState) (chain : ChainMixed)
    (frame : ∀ a : Word, 0x80600 ≤ a.toNat → a ≠ 0x81038 →
      t.getMem a=s.getMem a) :
    t.getByte (digitAddress chain) = s.getByte (digitAddress chain) := by
  have bound : 0x80600+chain.val<2^64 := by have := chain.isLt; omega
  have digitWord : 0x80600 ≤
      (Signing.wordAddress 0x80600 (chain.val/8)).toNat := by
    change 0x80600 ≤ (BitVec.ofNat 64 (0x80600+8*(chain.val/8))).toNat
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := chain.isLt; omega)]
    omega
  have neStep : Signing.wordAddress 0x80600 (chain.val/8) ≠ 0x81038 := by
    intro eq
    have h := congrArg BitVec.toNat eq
    change (BitVec.ofNat 64 (0x80600+8*(chain.val/8))).toNat = _ at h
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt
      (by have := chain.isLt; omega : 0x80600+8*(chain.val/8)<2^64)] at h
    have right : (0x81038 : Word).toNat=0x81038 := by decide
    rw [right] at h
    omega
  simp only [digitAddress,
    Signing.getByte_word t 0x80600 chain.val (by decide) bound,
    Signing.getByte_word s 0x80600 chain.val (by decide) bound,
    frame _ digitWord neStep]

theorem slot_nat (witnessBase : Nat) (chain : ChainMixed) (j : Fin 2)
    (bound : witnessBase + 16*chain.val + 16 ≤ 0x80000) :
    (slot witnessBase chain j).toNat = witnessBase + 16*chain.val + 8*j.val := by
  change (BitVec.ofNat 64 (witnessBase + 16*chain.val + 8*j.val)).toNat = _
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]

theorem target_nat (hash : Hash) (s : MachineState)
    (base leaf witnessBase : Nat) (chain : ChainMixed)
    (step : Nat) (seed : Reference.Digest)
    (data : Data hash s base leaf witnessBase chain step seed)
    (bound : witnessBase + 16*chain.val + 16 ≤ 0x80000) :
    (target (advanced hash s)).toNat = witnessBase + 16*chain.val := by
  have counter := GroupedBalancedSignUpperH2Tick67.advanced_frame hash s
    data.source data.destination 0x81030
      (by decide) (by intro i; fin_cases i <;> decide)
  have witness := GroupedBalancedSignUpperH2Tick67.advanced_frame hash s
    data.source data.destination 0x810f0
      (by decide) (by intro i; fin_cases i <;> decide)
  simpa only [target,GroupedBalancedSignUpperCaptureWitnessAfter67.target] using
    (GroupedBalancedSignUpperCaptureSafety67.pointer_nat
    (advanced hash s) witnessBase chain.val
    (witness.trans data.witness) (counter.trans data.counter)
    chain.isLt bound)

theorem target_eq_slot (hash : Hash) (s : MachineState)
    (base leaf witnessBase : Nat) (chain : ChainMixed)
    (step : Nat) (seed : Reference.Digest)
    (data : Data hash s base leaf witnessBase chain step seed)
    (bound : witnessBase + 16*chain.val + 16 ≤ 0x80000) :
    target (advanced hash s) = slot witnessBase chain 0 ∧
    target (advanced hash s) + 8 = slot witnessBase chain 1 := by
  have hn := target_nat hash s base leaf witnessBase chain step seed data bound
  have first : target (advanced hash s) = slot witnessBase chain 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [hn,slot_nat witnessBase chain 0 bound]
    omega
  refine ⟨first,?_⟩
  rw [first]
  simp [slot,Signing.wordAddress,BitVec.ofNat_add]

theorem round_other (hash : Hash) (s : MachineState)
    (base leaf witnessBase : Nat) (chain : ChainMixed)
    (step : Nat) (seed : Reference.Digest)
    (data : Data hash s base leaf witnessBase chain step seed)
    (bound : witnessBase + 16*chain.val + 16 ≤ 0x80000)
    (a : Word) (low : a.toNat < 0x80000)
    (ne0 : a ≠ slot witnessBase chain 0)
    (ne1 : a ≠ slot witnessBase chain 1) :
    (round hash s).getMem a = s.getMem a := by
  have targets := target_eq_slot hash s base leaf witnessBase chain step seed data bound
  have hashFrame := GroupedBalancedSignUpperH2Tick67.advanced_frame hash s
    data.source data.destination a
    (by intro e; have h := congrArg BitVec.toNat e; simp at h; omega)
    (by intro i e; have h := congrArg BitVec.toNat e;
        fin_cases i <;> simp [Signing.wordAddress] at h <;> omega)
  change (GroupedBalancedSignUpperH2CaptureAny67.captureResult
    (advanced hash s)).getMem a = _
  rw [GroupedBalancedSignUpperCaptureWitnessAfter67.capture_mem]
  unfold GroupedBalancedSignUpperCaptureWitnessAfter67.expectedMem
  dsimp only [target] at targets
  rw [targets.2,targets.1]
  split_ifs with e
  all_goals first
    | exact False.elim (ne1 e)
    | exact False.elim (ne0 e)
    | exact hashFrame

private theorem word_ne_small (a b : Nat) (lt : a < b) (bound : b ≤ 10) :
    (BitVec.ofNat 64 a : Word) ≠ BitVec.ofNat 64 b := by
  intro eq
  have hn := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : a < 2^64),
    Nat.mod_eq_of_lt (by omega : b < 2^64)] at hn
  omega

theorem run_remaining_other (hash : Hash) (s : MachineState)
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
      Trace hash GroupedBalancedSignImage67Byte.image s n
        (n+7*remaining) remaining remaining final ∧
      final.pc = 0x1ab0 ∧
      Data hash final base leaf witnessBase chain (step+remaining) seed ∧
      (∀ a : Word, a.toNat < 0x80000 →
        a ≠ slot witnessBase chain 0 →
        a ≠ slot witnessBase chain 1 →
        final.getMem a = s.getMem a) := by
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
      refine ⟨n,round hash s,by omega,?_,done,?_,?_⟩
      · simpa only [Nat.mul_one] using first
      · simpa only [Nat.add_zero] using nextData
      · intro a low ne0 ne1
        exact round_other hash s base leaf witnessBase chain step seed
          data witnessBound a low ne0 ne1
    · have more : step+1 < maxDigit chain := by omega
      have nextStart : (round hash s).pc = 0x1a38 := by
        rw [nextPC,if_pos (word_ne_small (step+1) (maxDigit chain)
          more (GroupedBalancedSignUpperH2Invariant67.max_bounds chain).2)]
      obtain ⟨m,final,mBound,second,done,finalData,lowLater⟩ :=
        ih (round hash s) (step+1) (by omega : 0 < rest)
          (by omega) nextData nextStart
      refine ⟨n+m,final,by omega,?_,done,?_,?_⟩
      · have both := first.trans second
        convert both using 1 <;> omega
      · have arith : step + 1 + rest = step + (rest+1) := by omega
        simpa only [arith] using finalData
      · intro a low ne0 ne1
        exact (lowLater a low ne0 ne1).trans
          (round_other hash s base leaf witnessBase chain step seed
            data witnessBound a low ne0 ne1)

#print axioms round_other
#print axioms run_remaining_other
end
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2WitnessFrame67
