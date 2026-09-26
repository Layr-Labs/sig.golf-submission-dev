import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperUnselectedRun67
import SigGolfCandidate.Hypertree.KeygenCopyFrame
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperEndpointControl67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperUnselectedStart67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperUnselectedChain67. -/
section
/-! The zero-step capture also preserves every witness word for an
unselected upper leaf. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperUnselectedStart67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree GroupedBalancedUpperTree67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
noncomputable section
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev Data := GroupedBalancedSignUpperH2Invariant67.Data

theorem captured_state (hash : Hash) (s : MachineState)
    (base leaf witnessBase : Nat) (chain : ChainMixed)
    (seed : Reference.Digest)
    (entry : GroupedBalancedSignUpperH2StartData67.Entry s base leaf
      witnessBase chain seed)
    (unselected : s.getMem 0x810e0≠s.getMem 0x810e8)
    (witnessLower : 0x20060≤witnessBase)
    (witnessBound : witnessBase+16*chain.val+16≤0x80000)
    (aligned : witnessBase%8=0) :
    ∃ (n : Nat) (captured : MachineState),
      n≤26 ∧
      OrdinarySteps image s
        (47+GroupedBalancedSignUpperMaxChoice67.stepsFor
          (BitVec.ofNat 64 chain.val)+n) captured ∧
      captured.pc=0x1a38 ∧
      Data hash captured base leaf witnessBase chain 0 seed ∧
      captured.getReg .x2=s.getReg .x2 ∧
      (∀ a : Word, 0x80600≤a.toNat → a≠0x81038 →
        captured.getMem a=s.getMem a) ∧
      (∀ j : Fin 4,
        captured.getMem (Signing.wordAddress 0x20 j.val)=
          s.getMem (Signing.wordAddress 0x20 j.val)) ∧
      captured.getMem 0x810e0≠captured.getMem 0x810e8 ∧
      (∀ a : Word, a.toNat<0x80000 →
        captured.getMem a=s.getMem a) := by
  obtain ⟨n,captured,nBound,path,pc,data,stack,frame,key,_low,
    ready,readyPath,capEq,_stepReg,_counter,_witnessReady,_value,
    readyFrame⟩ :=
    GroupedBalancedSignUpperH2StartData67.captured_state hash s
      base leaf witnessBase chain seed entry witnessLower witnessBound
      aligned
  obtain ⟨prepared,preparedPath,_pc,_service,_source,_bits,_dst,
    _chainReg,_maxReg,_stepReg2,_stack,_header,_index,_value2,
    _counter2,_witness2,_frame,_keyFrame,preparedLow⟩ :=
    GroupedBalancedSignUpperH2StartData67.prepared_state s base leaf
      witnessBase chain seed entry
  have same : ready=prepared :=
    Keygen.ordinary_deterministic readyPath preparedPath
  have readyLow (a : Word) (low : a.toNat<0x80000) :
      ready.getMem a=s.getMem a := by
    rw [same]
    exact preparedLow a low
  have readyUnselected : ready.getMem 0x810e0≠ready.getMem 0x810e8 := by
    rw [readyFrame 0x810e0 (by decide) (by decide),
      readyFrame 0x810e8 (by decide) (by decide)]
    exact unselected
  have capturedUnselected : captured.getMem 0x810e0≠
      captured.getMem 0x810e8 := by
    rw [capEq,
      GroupedBalancedSignUpperUnselectedCapture67.initial_low ready
        readyUnselected 0x810e0,
      GroupedBalancedSignUpperUnselectedCapture67.initial_low ready
        readyUnselected 0x810e8]
    exact readyUnselected
  refine ⟨n,captured,nBound,path,pc,data,stack,frame,key,
    capturedUnselected,?_⟩
  intro a low
  rw [capEq,GroupedBalancedSignUpperUnselectedCapture67.initial_low
    ready readyUnselected a]
  exact readyLow a low

#print axioms captured_state
end
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperUnselectedStart67

end

/-! A complete unselected upper WOTS chain keeps the entire signature
buffer unchanged while producing its endpoint. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperUnselectedChain67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree GroupedBalancedUpperTree67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
noncomputable section
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev store := GroupedBalancedSignUpperEndpointStore67.storeState
private abbrev dst := GroupedBalancedSignUpperEndpointStore67.address

theorem one_chain (hash : Hash) (s : MachineState)
    (base leaf witnessBase : Nat) (chain : ChainMixed)
    (seed : Reference.Digest)
    (entry : GroupedBalancedSignUpperH2StartData67.Entry s base leaf
      witnessBase chain seed)
    (unselected : s.getMem 0x810e0≠s.getMem 0x810e8)
    (baseBound : base<256)
    (witnessLower : 0x20060≤witnessBase)
    (witnessBound : witnessBase+16*chain.val+16≤0x80000)
    (aligned : witnessBase%8=0) :
    ∃ (n c : Nat) (final : MachineState),
      Trace hash image s n c (maxDigit chain) (maxDigit chain) final ∧
      final.pc=(if chain.val+1=67 then 0x1afc else 0x1760) ∧
      final.getMem 0x81030=BitVec.ofNat 64 (chain.val+1) ∧
      (∀ w : Fin 2,
        final.getMem (Signing.wordAddress (0x80800+16*chain.val) w.val)=
          (walk (chainHash hash base leaf chain) 0 (maxDigit chain)
            seed).extractLsb' (64*w.val) 64) ∧
      final.getReg .x2=s.getReg .x2 ∧
      final.getMem 0x810e0≠final.getMem 0x810e8 ∧
      (∀ a : Word, 0x80600≤a.toNat → a≠0x81038 → a≠0x81030 →
        a≠Signing.wordAddress (0x80800+16*chain.val) 0 →
        a≠Signing.wordAddress (0x80800+16*chain.val) 1 →
        final.getMem a=s.getMem a) ∧
      (∀ a : Word, a.toNat<0x80000 →
        final.getMem a=s.getMem a) ∧
      n ≤ 400 ∧ c ≤ 470 := by
  obtain ⟨captureN,captured,captureBound,capturePath,capturePc,
    captureData,captureSp,captureHigh,_captureKey,captureUnselected,
    captureLow⟩ :=
    GroupedBalancedSignUpperUnselectedStart67.captured_state hash s
      base leaf witnessBase chain seed entry unselected witnessLower
      witnessBound aligned
  have positive : 0<maxDigit chain := by
    have bound := (GroupedBalancedSignUpperH2Invariant67.max_bounds chain).1
    omega
  obtain ⟨loopN,mid,loopBound,loopTrace,midPc,midData,
    midUnselected,midSp,midHigh,midLow⟩ :=
    GroupedBalancedSignUpperUnselectedRun67.run_remaining hash captured
      base leaf witnessBase chain 0 (maxDigit chain) seed positive
      (by simp) captureData capturePc captureUnselected baseBound
      witnessBound aligned
  have counter : mid.getMem 0x81030=BitVec.ofNat 64 chain.val :=
    midData.counter
  obtain ⟨safe0,safe1⟩ :=
    GroupedBalancedSignUpperEndpointStore67.address_valid mid chain.val
      counter chain.isLt
  have storeTrace := GroupedBalancedSignUpperEndpointStore67.store_steps
    mid midPc safe0 safe1
  have stepsBound : GroupedBalancedSignUpperMaxChoice67.stepsFor
      (BitVec.ofNat 64 chain.val) ≤ 8 := by
    simp only [GroupedBalancedSignUpperMaxChoice67.stepsFor]
    split_ifs <;> omega
  have maxBound := (GroupedBalancedSignUpperH2Invariant67.max_bounds chain).2
  let final := store mid
  have pretrace : Trace hash image s
      (47+GroupedBalancedSignUpperMaxChoice67.stepsFor
        (BitVec.ofNat 64 chain.val)+captureN)
      (47+GroupedBalancedSignUpperMaxChoice67.stepsFor
        (BitVec.ofNat 64 chain.val)+captureN) 0 0 captured :=
    capturePath.trace
  have full := (pretrace.trans loopTrace).trans
    (storeTrace.trace (hash := hash))
  have addressEq := GroupedBalancedSignUpperEndpointStore67.address_eq
    mid chain.val counter
  have dstNat : (dst mid).toNat=0x80800+16*chain.val := by
    change (GroupedBalancedSignUpperEndpointStore67.address mid).toNat=_
    rw [addressEq]
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt
      (by have := chain.isLt; omega :
        0x80800+16*chain.val<2^64)]
  have nextNat : (dst mid+8).toNat=0x80800+16*chain.val+8 := by
    rw [BitVec.toNat_add,dstNat]
    change (0x80800+16*chain.val+8)%2^64=_
    rw [Nat.mod_eq_of_lt (by have := chain.isLt; omega :
      0x80800+16*chain.val+8<2^64)]
  have storeHigh (a : Word) (high : 0x81000≤a.toNat)
      (ne30 : a≠0x81030) :
      final.getMem a=mid.getMem a := by
    have neDst : a≠dst mid := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      rw [dstNat] at hn
      have := chain.isLt
      omega
    have neNext : a≠dst mid+8 := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      rw [nextNat] at hn
      have := chain.isLt
      omega
    exact GroupedBalancedSignUpperEndpointStore67.store_frame mid a
      ne30 neDst neNext
  refine ⟨(47+GroupedBalancedSignUpperMaxChoice67.stepsFor
      (BitVec.ofNat 64 chain.val)+captureN)+loopN+19,
    (47+GroupedBalancedSignUpperMaxChoice67.stepsFor
      (BitVec.ofNat 64 chain.val)+captureN)+
      (loopN+7*maxDigit chain)+19,final,?_,?_,?_,?_,?_,?_,?_,?_,
      ?_,?_⟩
  · simpa [final,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using full
  · exact GroupedBalancedSignUpperEndpointControl67.store_pc_chain mid
      chain.val midPc counter chain.isLt
  · exact GroupedBalancedSignUpperEndpointControl67.store_counter_eq
      mid chain.val counter
  · intro w
    rw [GroupedBalancedSignUpperEndpointData67.store_values mid chain.val
      counter chain.isLt w]
    simpa only [Nat.zero_add] using midData.value w
  · rw [GroupedBalancedSignUpperEndpointStore67.store_stack,
      midSp,captureSp]
  · rw [storeHigh 0x810e0 (by decide) (by decide),
      storeHigh 0x810e8 (by decide) (by decide)]
    exact midUnselected
  · intro a high ne38 ne30 neDst0 neDst1
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
      ne30 neq0 neq1]
    exact (midHigh a high).trans (captureHigh a high ne38)
  · intro a low
    have neCounter : a≠0x81030 := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      have numeric : (0x81030 : Word).toNat=0x81030 := by decide
      rw [numeric] at hn
      omega
    have neDst : a≠dst mid := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      rw [dstNat] at hn
      omega
    have neNext : a≠dst mid+8 := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      rw [nextNat] at hn
      omega
    rw [GroupedBalancedSignUpperEndpointStore67.store_frame mid a
      neCounter neDst neNext]
    exact (midLow a low).trans (captureLow a low)
  · omega
  · omega

#print axioms one_chain
end
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperUnselectedChain67
