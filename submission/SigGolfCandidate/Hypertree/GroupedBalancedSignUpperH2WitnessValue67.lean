import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2StartData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2WitnessFrame67

/-! The selected WOTS prefix is written at the digit indicated by the
decoder table, with the exact functional chain value. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2WitnessValue67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree GroupedBalancedUpperTree67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
noncomputable section
private abbrev Data := GroupedBalancedSignUpperH2Invariant67.Data
private abbrev round := GroupedBalancedSignUpperH2Round67.roundResult
private abbrev advanced := GroupedBalancedSignUpperH2Tick67.advanced
private abbrev slot := GroupedBalancedSignUpperH2WitnessFrame67.slot
private abbrev digitAddress := GroupedBalancedSignUpperH2WitnessFrame67.digitAddress

theorem initial_selected_value (s : MachineState)
    (witnessBase : Nat) (chain : ChainMixed) (seed : Reference.Digest)
    (counter : s.getMem 0x81030=BitVec.ofNat 64 chain.val)
    (witness : s.getMem 0x810f0=BitVec.ofNat 64 witnessBase)
    (stepReg : s.getReg .x21=0)
    (seedWords : ∀j : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 j.val)=
        seed.extractLsb' (64*j.val) 64)
    (selected : s.getMem 0x810e0=s.getMem 0x810e8)
    (digitZero : s.getByte (digitAddress chain)=0)
    (witnessBound : witnessBase+16*chain.val+16≤0x80000)
    (j : Fin 2) :
    (GroupedBalancedSignUpperInitialCapture67.captureResult s).getMem
      (slot witnessBase chain j) = seed.extractLsb' (64*j.val) 64 := by
  have addr : 0x80600 + BitVec.ofNat 64 chain.val = digitAddress chain := by
    change BitVec.ofNat 64 0x80600 + BitVec.ofNat 64 chain.val =
      BitVec.ofNat 64 (0x80600+chain.val)
    exact (BitVec.ofNat_add _ _).symm
  have matched : GroupedBalancedSignUpperCaptureCompose67.DigitMatches s := by
    unfold GroupedBalancedSignUpperCaptureCompose67.DigitMatches
    rw [counter,addr,digitZero,stepReg]
    rfl
  have hn := GroupedBalancedSignUpperInitialCapture67.pointer_nat s
    witnessBase chain.val witness counter chain.isLt witnessBound
  have target0 : GroupedBalancedSignUpperCaptureWitnessInitial67.target s =
      slot witnessBase chain 0 := by
    apply BitVec.eq_of_toNat_eq
    have hn' : (GroupedBalancedSignUpperCaptureWitnessInitial67.target s).toNat =
        witnessBase+16*chain.val := by
      simpa only [GroupedBalancedSignUpperCaptureWitnessInitial67.target] using hn
    rw [hn',GroupedBalancedSignUpperH2WitnessFrame67.slot_nat
      witnessBase chain 0 witnessBound]
    omega
  have target1 : GroupedBalancedSignUpperCaptureWitnessInitial67.target s+8 =
      slot witnessBase chain 1 := by
    rw [target0]
    simp [slot,GroupedBalancedSignUpperH2WitnessFrame67.slot,
      Signing.wordAddress,BitVec.ofNat_add]
  rw [GroupedBalancedSignUpperCaptureWitnessInitial67.capture_mem]
  unfold GroupedBalancedSignUpperCaptureWitnessInitial67.expectedMem
  rw [if_pos ⟨selected,matched⟩,target1,target0]
  fin_cases j
  · have neq : slot witnessBase chain 0 ≠ slot witnessBase chain 1 := by
      intro eq
      have h := congrArg BitVec.toNat eq
      rw [GroupedBalancedSignUpperH2WitnessFrame67.slot_nat witnessBase chain 0 witnessBound,
        GroupedBalancedSignUpperH2WitnessFrame67.slot_nat witnessBase chain 1 witnessBound] at h
      omega
    change (if slot witnessBase chain 0 = slot witnessBase chain 1 then
        s.getMem 0x80028 else if slot witnessBase chain 0 = slot witnessBase chain 0 then
          s.getMem 0x80020 else s.getMem (slot witnessBase chain 0)) =
      seed.extractLsb' 0 64
    rw [if_neg neq,if_pos rfl]
    simpa [Signing.wordAddress] using seedWords (0 : Fin 2)
  · change (if slot witnessBase chain 1 = slot witnessBase chain 1 then
        s.getMem 0x80028 else if slot witnessBase chain 1 = slot witnessBase chain 0 then
          s.getMem 0x80020 else s.getMem (slot witnessBase chain 1)) =
      seed.extractLsb' 64 64
    rw [if_pos rfl]
    simpa [Signing.wordAddress] using seedWords (1 : Fin 2)

theorem advanced_selected (hash : Hash) (s : MachineState)
    (base leaf witnessBase : Nat) (chain : ChainMixed)
    (step : Nat) (seed : Reference.Digest)
    (data : Data hash s base leaf witnessBase chain step seed)
    (selected : s.getMem 0x810e0=s.getMem 0x810e8) :
    (advanced hash s).getMem 0x810e0 = (advanced hash s).getMem 0x810e8 := by
  rw [GroupedBalancedSignUpperH2Tick67.advanced_frame hash s
      data.source data.destination 0x810e0
      (by decide) (by intro i; fin_cases i <;> decide),
    GroupedBalancedSignUpperH2Tick67.advanced_frame hash s
      data.source data.destination 0x810e8
      (by decide) (by intro i; fin_cases i <;> decide)]
  exact selected

theorem advanced_matches (hash : Hash) (s : MachineState)
    (base leaf witnessBase : Nat) (chain : ChainMixed)
    (step d : Nat) (seed : Reference.Digest)
    (data : Data hash s base leaf witnessBase chain step seed)
    (stepBound : step<maxDigit chain)
    (digit : s.getByte (digitAddress chain)=BitVec.ofNat 8 d)
    (dBound : d<256) :
    GroupedBalancedSignUpperCaptureComposeAfter67.DigitMatches
      (advanced hash s) ↔ step+1=d := by
  have counter := GroupedBalancedSignUpperH2Tick67.advanced_frame hash s
    data.source data.destination 0x81030
      (by decide) (by intro i; fin_cases i <;> decide)
  have byte := GroupedBalancedSignUpperH2WitnessFrame67.digit_byte_frame
    s (advanced hash s) chain (by
      intro a high
      exact GroupedBalancedSignUpperH2Tick67.advanced_frame hash s
        data.source data.destination a
        (by intro eq; have h:=congrArg BitVec.toNat eq; simp at h; omega)
        (by intro i eq; have h:=congrArg BitVec.toNat eq;
            fin_cases i <;> simp [Signing.wordAddress] at h <;> omega))
  have addr : 0x80600 + BitVec.ofNat 64 chain.val = digitAddress chain := by
    change BitVec.ofNat 64 0x80600 + BitVec.ofNat 64 chain.val =
      BitVec.ofNat 64 (0x80600+chain.val)
    exact (BitVec.ofNat_add _ _).symm
  unfold GroupedBalancedSignUpperCaptureComposeAfter67.DigitMatches
  rw [counter,data.counter,addr,byte,digit,
    (GroupedBalancedSignUpperH2Tick67.advanced_regs hash s).1,
    data.stepReg]
  have cast8 : (BitVec.ofNat 8 d).zeroExtend 64 = BitVec.ofNat 64 d := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.zeroExtend,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    omega
  have add : BitVec.ofNat 64 step + 1 = BitVec.ofNat 64 (step+1) := by
    simpa using (BitVec.ofNat_add step 1).symm
  rw [cast8,add]
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at hn
    have stepSmall : step+1<2^64 := by
      have b := (GroupedBalancedSignUpperH2Invariant67.max_bounds chain).2
      omega
    rw [Nat.mod_eq_of_lt (by omega : d<2^64),
      Nat.mod_eq_of_lt stepSmall] at hn
    exact hn.symm
  · intro h
    subst d
    rfl

theorem round_selected_value (hash : Hash) (s : MachineState)
    (base leaf witnessBase : Nat) (chain : ChainMixed)
    (step d : Nat) (seed : Reference.Digest)
    (data : Data hash s base leaf witnessBase chain step seed)
    (pc : s.pc=0x1a38)
    (baseBound : base<256)
    (stepBound : step<maxDigit chain)
    (witnessBound : witnessBase+16*chain.val+16≤0x80000)
    (aligned : witnessBase%8=0)
    (selected : s.getMem 0x810e0=s.getMem 0x810e8)
    (digit : s.getByte (digitAddress chain)=BitVec.ofNat 8 d)
    (dBound : d<256)
    (isDigit : step+1=d) (j : Fin 2) :
    (round hash s).getMem (slot witnessBase chain j) =
      (walk (chainHash hash base leaf chain) 0 (step+1) seed).extractLsb'
        (64*j.val) 64 := by
  have selectedA := advanced_selected hash s base leaf witnessBase chain step
    seed data selected
  have matchedA := (advanced_matches hash s base leaf witnessBase chain
    step d seed data stepBound digit dBound).mpr isDigit
  have targets := GroupedBalancedSignUpperH2WitnessFrame67.target_eq_slot
    hash s base leaf witnessBase chain step seed data witnessBound
  have safe := GroupedBalancedSignUpperH2Round67.safe_after_hash hash s
    data.source data.destination witnessBase chain.val data.witness
    data.counter chain.isLt witnessBound aligned
  obtain ⟨_,_,_,low0,low1⟩ := safe
  obtain ⟨_,_,_,_,nextData⟩ :=
    GroupedBalancedSignUpperH2Invariant67.round_data hash s base leaf
      witnessBase chain step seed data pc baseBound stepBound witnessBound aligned
  have advancedValue (w : Fin 2) :
      (advanced hash s).getMem (Signing.wordAddress 0x80020 w.val) =
        (walk (chainHash hash base leaf chain) 0 (step+1) seed).extractLsb'
          (64*w.val) 64 := by
    have hf := GroupedBalancedSignUpperH2CaptureAny67.capture_high_frame
      (advanced hash s) (Signing.wordAddress 0x80020 w.val)
      (by fin_cases w <;> decide) low0 low1
    rw [← hf]
    exact nextData.value w
  change (GroupedBalancedSignUpperH2CaptureAny67.captureResult
    (advanced hash s)).getMem (slot witnessBase chain j) = _
  rw [GroupedBalancedSignUpperCaptureWitnessAfter67.capture_mem]
  unfold GroupedBalancedSignUpperCaptureWitnessAfter67.expectedMem
  rw [if_pos ⟨selectedA,matchedA⟩]
  have target0 : GroupedBalancedSignUpperCaptureWitnessAfter67.target
      (advanced hash s) = slot witnessBase chain 0 := targets.1
  have target1 : GroupedBalancedSignUpperCaptureWitnessAfter67.target
      (advanced hash s) + 8 = slot witnessBase chain 1 := targets.2
  rw [target1,target0]
  fin_cases j
  · have neq : slot witnessBase chain 0 ≠ slot witnessBase chain 1 := by
      intro eq
      have h := congrArg BitVec.toNat eq
      rw [GroupedBalancedSignUpperH2WitnessFrame67.slot_nat witnessBase chain 0 witnessBound,
        GroupedBalancedSignUpperH2WitnessFrame67.slot_nat witnessBase chain 1 witnessBound] at h
      omega
    change (if slot witnessBase chain 0 = slot witnessBase chain 1 then
        (advanced hash s).getMem 0x80028 else
        if slot witnessBase chain 0 = slot witnessBase chain 0 then
          (advanced hash s).getMem 0x80020 else
          (advanced hash s).getMem (slot witnessBase chain 0)) =
      (walk (chainHash hash base leaf chain) 0 (step+1) seed).extractLsb' 0 64
    rw [if_neg neq,if_pos rfl]
    simpa [Signing.wordAddress] using advancedValue (0 : Fin 2)
  · change (if slot witnessBase chain 1 = slot witnessBase chain 1 then
        (advanced hash s).getMem 0x80028 else
        if slot witnessBase chain 1 = slot witnessBase chain 0 then
          (advanced hash s).getMem 0x80020 else
          (advanced hash s).getMem (slot witnessBase chain 1)) =
      (walk (chainHash hash base leaf chain) 0 (step+1) seed).extractLsb' 64 64
    rw [if_pos rfl]
    simpa [Signing.wordAddress] using advancedValue (1 : Fin 2)

theorem round_witness_preserve (hash : Hash) (s : MachineState)
    (base leaf witnessBase : Nat) (chain : ChainMixed)
    (step d : Nat) (seed : Reference.Digest)
    (data : Data hash s base leaf witnessBase chain step seed)
    (stepBound : step<maxDigit chain)
    (witnessBound : witnessBase+16*chain.val+16≤0x80000)
    (digit : s.getByte (digitAddress chain)=BitVec.ofNat 8 d)
    (dBound : d<256) (other : step+1≠d) (j : Fin 2) :
    (round hash s).getMem (slot witnessBase chain j) =
      s.getMem (slot witnessBase chain j) := by
  have unmatched := (advanced_matches hash s base leaf witnessBase chain
    step d seed data stepBound digit dBound).not.mpr other
  have low : (slot witnessBase chain j).toNat<0x80000 := by
    rw [GroupedBalancedSignUpperH2WitnessFrame67.slot_nat
      witnessBase chain j witnessBound]
    have hj := j.isLt
    omega
  have hashFrame := GroupedBalancedSignUpperH2Tick67.advanced_frame
    hash s data.source data.destination (slot witnessBase chain j)
    (by intro eq; have h:=congrArg BitVec.toNat eq; simp at h; omega)
    (by intro i eq; have h:=congrArg BitVec.toNat eq;
        fin_cases i <;> simp [Signing.wordAddress] at h <;> omega)
  change (GroupedBalancedSignUpperH2CaptureAny67.captureResult
    (advanced hash s)).getMem (slot witnessBase chain j) = _
  rw [GroupedBalancedSignUpperCaptureWitnessAfter67.capture_mem]
  unfold GroupedBalancedSignUpperCaptureWitnessAfter67.expectedMem
  simp only [unmatched, and_false, ↓reduceIte]
  exact hashFrame

private theorem word_ne_small (a b : Nat) (lt : a<b) (bound : b≤10) :
    (BitVec.ofNat 64 a : Word) ≠ BitVec.ofNat 64 b := by
  intro eq
  have h := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : a<2^64),
    Nat.mod_eq_of_lt (by omega : b<2^64)] at h
  omega

theorem run_remaining_selected (hash : Hash) (s : MachineState)
    (base leaf witnessBase : Nat) (chain : ChainMixed)
    (step remaining d : Nat) (seed : Reference.Digest)
    (positive : 0<remaining)
    (total : step+remaining=maxDigit chain)
    (digitBound : d≤maxDigit chain)
    (data : Data hash s base leaf witnessBase chain step seed)
    (pc : s.pc=0x1a38)
    (baseBound : base<256)
    (witnessBound : witnessBase+16*chain.val+16≤0x80000)
    (aligned : witnessBase%8=0)
    (selected : s.getMem 0x810e0=s.getMem 0x810e8)
    (digit : s.getByte (digitAddress chain)=BitVec.ofNat 8 d)
    (early : d≤step → ∀j : Fin 2,
      s.getMem (slot witnessBase chain j) =
        (walk (chainHash hash base leaf chain) 0 d seed).extractLsb'
          (64*j.val) 64) :
    ∃ (n : Nat) (final : MachineState),
      n≤30*remaining ∧
      Trace hash GroupedBalancedSignImage67Byte.image s n
        (n+7*remaining) remaining remaining final ∧
      final.pc=0x1ab0 ∧
      Data hash final base leaf witnessBase chain (step+remaining) seed ∧
      (∀j : Fin 2,
        final.getMem (slot witnessBase chain j) =
          (walk (chainHash hash base leaf chain) 0 d seed).extractLsb'
            (64*j.val) 64) ∧
      final.getReg .x2=s.getReg .x2 ∧
      (∀a : Word, 0x80600≤a.toNat → final.getMem a=s.getMem a) ∧
      (∀a : Word, a.toNat<0x80000 →
        a≠slot witnessBase chain 0 → a≠slot witnessBase chain 1 →
        final.getMem a=s.getMem a) := by
  induction remaining generalizing s step with
  | zero => omega
  | succ rest ih =>
    have stepBound : step<maxDigit chain := by omega
    have dSmall : d<256 := by
      have b := (GroupedBalancedSignUpperH2Invariant67.max_bounds chain).2
      omega
    obtain ⟨n,nBound,first,nextPC,nextData⟩ :=
      GroupedBalancedSignUpperH2Invariant67.round_data hash s base leaf
        witnessBase chain step seed data pc baseBound stepBound
        witnessBound aligned
    have safe := GroupedBalancedSignUpperH2Round67.safe_after_hash hash s
      data.source data.destination witnessBase chain.val data.witness
      data.counter chain.isLt witnessBound aligned
    obtain ⟨safeDigit,safeWitness,safeWitnessNext,low0,low1⟩ := safe
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,highFrame⟩ :=
      GroupedBalancedSignUpperH2Round67.round_trace hash s pc
        data.service data.source data.bits data.destination
        safeDigit safeWitness safeWitnessNext low0 low1
    have nextSelected : (round hash s).getMem 0x810e0 =
        (round hash s).getMem 0x810e8 := by
      rw [highFrame 0x810e0 (by decide),
        highFrame 0x810e8 (by decide)]
      exact selected
    have nextDigit : (round hash s).getByte (digitAddress chain) =
        BitVec.ofNat 8 d := by
      rw [GroupedBalancedSignUpperH2WitnessFrame67.digit_byte_frame
        s (round hash s) chain highFrame]
      exact digit
    have nextEarly : d≤step+1 → ∀j : Fin 2,
        (round hash s).getMem (slot witnessBase chain j) =
          (walk (chainHash hash base leaf chain) 0 d seed).extractLsb'
            (64*j.val) 64 := by
      intro seen j
      by_cases here : step+1=d
      · rw [round_selected_value hash s base leaf witnessBase chain
          step d seed data pc baseBound stepBound witnessBound aligned
          selected digit dSmall here j,here]
      · rw [round_witness_preserve hash s base leaf witnessBase chain
          step d seed data stepBound witnessBound digit dSmall here j]
        exact early (by omega) j
    by_cases last : rest=0
    · subst rest
      have done : (round hash s).pc=0x1ab0 := by
        rw [nextPC]
        have eq : step+1=maxDigit chain := by omega
        rw [eq]
        simp
      refine ⟨n,round hash s,by omega,?_,done,?_,?_,
        GroupedBalancedSignUpperH2Round67.round_stack hash s,highFrame,?_⟩
      · simpa only [Nat.mul_one] using first
      · simpa only [Nat.add_zero] using nextData
      · exact nextEarly (by omega)
      · intro a low ne0 ne1
        exact GroupedBalancedSignUpperH2WitnessFrame67.round_other hash s
          base leaf witnessBase chain step seed data witnessBound a low ne0 ne1
    · have more : step+1<maxDigit chain := by omega
      have nextStart : (round hash s).pc=0x1a38 := by
        rw [nextPC,if_pos (word_ne_small (step+1) (maxDigit chain)
          more (GroupedBalancedSignUpperH2Invariant67.max_bounds chain).2)]
      obtain ⟨m,final,mBound,second,done,finalData,finalValue,
        stackLater,highLater,lowLater⟩ :=
        ih (round hash s) (step+1) (by omega : 0<rest)
          (by omega) nextData nextStart nextSelected nextDigit nextEarly
      refine ⟨n+m,final,by omega,?_,done,?_,finalValue,?_,?_,?_⟩
      · have both := first.trans second
        convert both using 1 <;> omega
      · have arith : step+1+rest=step+(rest+1) := by omega
        simpa only [arith] using finalData
      · exact stackLater.trans
          (GroupedBalancedSignUpperH2Round67.round_stack hash s)
      · intro a high
        exact (highLater a high).trans (highFrame a high)
      · intro a low ne0 ne1
        exact (lowLater a low ne0 ne1).trans
          (GroupedBalancedSignUpperH2WitnessFrame67.round_other hash s
            base leaf witnessBase chain step seed data witnessBound a low ne0 ne1)

#print axioms advanced_matches
#print axioms round_selected_value
#print axioms round_witness_preserve
#print axioms run_remaining_selected
end
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2WitnessValue67
