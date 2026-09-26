import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2OneChain67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2WitnessValue67

/-! A complete selected upper WOTS chain writes the exact signature witness. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2SelectedChain67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree GroupedBalancedUpperTree67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
noncomputable section
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev slot := GroupedBalancedSignUpperH2WitnessFrame67.slot
private abbrev digitAddress := GroupedBalancedSignUpperH2WitnessFrame67.digitAddress
private abbrev store := GroupedBalancedSignUpperEndpointStore67.storeState
private abbrev dst := GroupedBalancedSignUpperEndpointStore67.address

theorem selected_chain (hash : Hash) (s : MachineState)
    (base leaf witnessBase : Nat) (chain : ChainMixed)
    (seed : Reference.Digest) (d : Nat)
    (entry : GroupedBalancedSignUpperH2StartData67.Entry s base leaf
      witnessBase chain seed)
    (baseBound : base<256)
    (witnessLower : 0x20060≤witnessBase)
    (witnessBound : witnessBase+16*chain.val+16≤0x80000)
    (aligned : witnessBase%8=0)
    (selected : s.getMem 0x810e0=s.getMem 0x810e8)
    (digit : s.getByte (digitAddress chain)=BitVec.ofNat 8 d)
    (digitBound : d≤maxDigit chain) :
    ∃ (n c : Nat) (final : MachineState),
      Trace hash image s n c (maxDigit chain) (maxDigit chain) final ∧
      final.pc=(if chain.val+1=67 then 0x1afc else 0x1760) ∧
      (∀j : Fin 2,
        final.getMem (slot witnessBase chain j)=
          (walk (chainHash hash base leaf chain) 0 d seed).extractLsb'
            (64*j.val) 64) ∧
      final.getMem 0x81030=BitVec.ofNat 64 (chain.val+1) ∧
      (∀j : Fin 2,
        final.getMem (Signing.wordAddress (0x80800+16*chain.val) j.val)=
          (walk (chainHash hash base leaf chain) 0 (maxDigit chain) seed).extractLsb'
            (64*j.val) 64) ∧
      final.getReg .x2=s.getReg .x2 ∧
      (∀a : Word, 0x80600≤a.toNat → a≠0x81038 → a≠0x81030 →
        a≠Signing.wordAddress (0x80800+16*chain.val) 0 →
        a≠Signing.wordAddress (0x80800+16*chain.val) 1 →
        final.getMem a=s.getMem a) ∧
      (∀a : Word, a.toNat<0x80000 →
        a≠slot witnessBase chain 0 → a≠slot witnessBase chain 1 →
        final.getMem a=s.getMem a) ∧
      n ≤ 400 ∧ c ≤ 470 := by
  obtain ⟨captureN,captured,captureBound,captureTrace,capturePc,
    captureData,captureStack,captureFrame,captureKey,captureLow,
    ready,prep,capEq,stepReg,counter,
    witness,seedWords,readyFrame⟩ :=
      GroupedBalancedSignUpperH2StartData67.captured_state hash s
        base leaf witnessBase chain seed entry witnessLower witnessBound aligned
  have selectedReady : ready.getMem 0x810e0=ready.getMem 0x810e8 := by
    rw [readyFrame 0x810e0 (by decide) (by decide),
      readyFrame 0x810e8 (by decide) (by decide)]
    exact selected
  have digitReady : ready.getByte (digitAddress chain)=BitVec.ofNat 8 d := by
    rw [GroupedBalancedSignUpperH2WitnessFrame67.digit_byte_frame_except
      s ready chain readyFrame]
    exact digit
  have selectedCaptured : captured.getMem 0x810e0=captured.getMem 0x810e8 := by
    rw [captureFrame 0x810e0 (by decide) (by decide),
      captureFrame 0x810e8 (by decide) (by decide)]
    exact selected
  have digitCaptured : captured.getByte (digitAddress chain)=
      BitVec.ofNat 8 d := by
    rw [GroupedBalancedSignUpperH2WitnessFrame67.digit_byte_frame_except
      s captured chain captureFrame]
    exact digit
  have early : d≤0 → ∀j : Fin 2,
      captured.getMem (slot witnessBase chain j)=
        (walk (chainHash hash base leaf chain) 0 d seed).extractLsb'
          (64*j.val) 64 := by
    intro hd j
    have dZero : d=0 := by omega
    subst d
    rw [capEq]
    have initial := GroupedBalancedSignUpperH2WitnessValue67.initial_selected_value
      ready witnessBase chain seed counter witness stepReg seedWords
      selectedReady (by simpa using digitReady) witnessBound j
    simpa [walk] using initial
  have positive : 0<maxDigit chain := by
    have b := (GroupedBalancedSignUpperH2Invariant67.max_bounds chain).1
    omega
  obtain ⟨loopN,mid,loopBound,loopTrace,midPc,midData,midValue,
    loopStack,loopHigh,loopLow⟩ :=
    GroupedBalancedSignUpperH2WitnessValue67.run_remaining_selected
      hash captured base leaf witnessBase chain 0 (maxDigit chain) d seed
      positive (by simp) digitBound captureData capturePc baseBound
      witnessBound aligned selectedCaptured digitCaptured early
  have midCounter : mid.getMem 0x81030=BitVec.ofNat 64 chain.val :=
    midData.counter
  obtain ⟨safe0,safe1⟩ :=
    GroupedBalancedSignUpperEndpointStore67.address_valid mid chain.val
      midCounter chain.isLt
  have storeTrace := GroupedBalancedSignUpperEndpointStore67.store_steps
    mid midPc safe0 safe1
  let final := store mid
  have pretrace : Trace hash image s
      (47+GroupedBalancedSignUpperMaxChoice67.stepsFor
        (BitVec.ofNat 64 chain.val)+captureN)
      (47+GroupedBalancedSignUpperMaxChoice67.stepsFor
        (BitVec.ofNat 64 chain.val)+captureN) 0 0 captured :=
    captureTrace.trace
  have full := (pretrace.trans loopTrace).trans
    (storeTrace.trace (hash := hash))
  have stepsBound : GroupedBalancedSignUpperMaxChoice67.stepsFor
      (BitVec.ofNat 64 chain.val) ≤ 8 := by
    simp only [GroupedBalancedSignUpperMaxChoice67.stepsFor]
    split_ifs <;> omega
  have maxBound := (GroupedBalancedSignUpperH2Invariant67.max_bounds chain).2
  refine ⟨(47+GroupedBalancedSignUpperMaxChoice67.stepsFor
      (BitVec.ofNat 64 chain.val)+captureN)+loopN+19,
    (47+GroupedBalancedSignUpperMaxChoice67.stepsFor
      (BitVec.ofNat 64 chain.val)+captureN)+
      (loopN+7*maxDigit chain)+19,final,?_,?_,?_,?_,?_,?_,?_,?_,
      ?_,?_⟩
  · simpa [final,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using full
  · exact GroupedBalancedSignUpperEndpointControl67.store_pc_chain mid
      chain.val midPc midCounter chain.isLt
  · intro j
    have addressEq := GroupedBalancedSignUpperEndpointStore67.address_eq
      mid chain.val midCounter
    have dstNat : (dst mid).toNat=0x80800+16*chain.val := by
      change (GroupedBalancedSignUpperEndpointStore67.address mid).toNat=_
      rw [addressEq]
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt
        (by omega : 0x80800+16*chain.val<2^64)]
    have nextNat : (dst mid+8).toNat=0x80800+16*chain.val+8 := by
      rw [BitVec.toNat_add,dstNat]
      change (0x80800+16*chain.val+8)%2^64=_
      rw [Nat.mod_eq_of_lt (by omega : 0x80800+16*chain.val+8<2^64)]
    have slotLow : (slot witnessBase chain j).toNat<0x80000 := by
      rw [GroupedBalancedSignUpperH2WitnessFrame67.slot_nat
        witnessBase chain j witnessBound]
      have hj := j.isLt
      omega
    have neDst : slot witnessBase chain j ≠ dst mid := by
      intro eq
      have h := congrArg BitVec.toNat eq
      rw [dstNat] at h
      omega
    have neNext : slot witnessBase chain j ≠ dst mid+8 := by
      intro eq
      have h := congrArg BitVec.toNat eq
      rw [nextNat] at h
      omega
    have neCounter : slot witnessBase chain j ≠ 0x81030 := by
      intro eq
      have h := congrArg BitVec.toNat eq
      simp at h
      omega
    rw [GroupedBalancedSignUpperEndpointStore67.store_frame mid _
      neCounter neDst neNext]
    exact midValue j
  · exact GroupedBalancedSignUpperEndpointControl67.store_counter_eq
      mid chain.val midCounter
  · intro j
    rw [GroupedBalancedSignUpperEndpointData67.store_values mid chain.val
      midCounter chain.isLt j]
    simpa only [Nat.zero_add] using midData.value j
  · rw [GroupedBalancedSignUpperEndpointStore67.store_stack,
      loopStack,captureStack]
  · intro a high neStep neCounter neDst0 neDst1
    have addressEq := GroupedBalancedSignUpperEndpointStore67.address_eq
      mid chain.val midCounter
    have neq0 : a≠dst mid := by
      simpa only [dst,addressEq,Signing.wordAddress,Nat.mul_zero,
        Nat.add_zero] using neDst0
    have neq1 : a≠dst mid+8 := by
      have next : dst mid+8=Signing.wordAddress
          (0x80800+16*chain.val) 1 := by
        change GroupedBalancedSignUpperEndpointStore67.address mid+8=_
        rw [addressEq]
        simp [Signing.wordAddress,BitVec.ofNat_add]
      simpa only [next] using neDst1
    rw [GroupedBalancedSignUpperEndpointStore67.store_frame mid a
      neCounter neq0 neq1]
    exact (loopHigh a high).trans (captureFrame a high neStep)
  · intro a low ne0 ne1
    have addressEq := GroupedBalancedSignUpperEndpointStore67.address_eq
      mid chain.val midCounter
    have dstNat : (dst mid).toNat=0x80800+16*chain.val := by
      change (GroupedBalancedSignUpperEndpointStore67.address mid).toNat=_
      rw [addressEq]
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt
        (by omega : 0x80800+16*chain.val<2^64)]
    have nextNat : (dst mid+8).toNat=0x80800+16*chain.val+8 := by
      rw [BitVec.toNat_add,dstNat]
      change (0x80800+16*chain.val+8)%2^64=_
      rw [Nat.mod_eq_of_lt (by omega : 0x80800+16*chain.val+8<2^64)]
    have neDst : a≠dst mid := by
      intro eq
      have h := congrArg BitVec.toNat eq
      rw [dstNat] at h
      omega
    have neNext : a≠dst mid+8 := by
      intro eq
      have h := congrArg BitVec.toNat eq
      rw [nextNat] at h
      omega
    have neCounter : a≠0x81030 := by
      intro eq
      have h := congrArg BitVec.toNat eq
      simp at h
      omega
    rw [GroupedBalancedSignUpperEndpointStore67.store_frame mid a
      neCounter neDst neNext]
    exact (loopLow a low ne0 ne1).trans (captureLow a low ne0 ne1)
  · omega
  · omega

#print axioms selected_chain
end
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2SelectedChain67
