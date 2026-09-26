import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2StartData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperEndpointControl67

/-! The machine executes one complete H2 WOTS chain, stores its endpoint,
and branches to the next chain or leaf compression. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2OneChain67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree GroupedBalancedUpperTree67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
noncomputable section
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev Entry := GroupedBalancedSignUpperH2StartData67.Entry
private abbrev store := GroupedBalancedSignUpperEndpointStore67.storeState
private abbrev dst := GroupedBalancedSignUpperEndpointStore67.address

theorem one_chain (hash : Hash) (s : MachineState)
    (base leaf witnessBase : Nat) (chain : ChainMixed)
    (seed : Reference.Digest)
    (entry : Entry s base leaf witnessBase chain seed)
    (baseBound : base < 256)
    (witnessLower : 0x20060 ≤ witnessBase)
    (witnessBound : witnessBase + 16*chain.val + 16 ≤ 0x80000)
    (aligned : witnessBase % 8 = 0) :
    ∃ (n c : Nat) (final : MachineState),
      Trace hash image s n c (maxDigit chain) (maxDigit chain) final ∧
      final.pc = (if chain.val+1=67 then 0x1afc else 0x1760) ∧
      final.getMem 0x81030 = BitVec.ofNat 64 (chain.val+1) ∧
      (∀ j : Fin 2,
        final.getMem (Signing.wordAddress (0x80800+16*chain.val) j.val) =
          (walk (chainHash hash base leaf chain) 0 (maxDigit chain) seed).extractLsb'
            (64*j.val) 64) ∧
      final.getReg .x2 = s.getReg .x2 ∧
      (∀ j : Fin 4,
        final.getMem (Signing.wordAddress 0x20 j.val) =
          s.getMem (Signing.wordAddress 0x20 j.val)) ∧
      (∀ a : Word, 0x80600 ≤ a.toNat → a ≠ 0x81038 →
        a ≠ 0x81030 →
        a ≠ Signing.wordAddress (0x80800+16*chain.val) 0 →
        a ≠ Signing.wordAddress (0x80800+16*chain.val) 1 →
        final.getMem a = s.getMem a) ∧
      (∀ a : Word, a.toNat < 0x80000 →
        a ≠ Signing.wordAddress (witnessBase+16*chain.val) 0 →
        a ≠ Signing.wordAddress (witnessBase+16*chain.val) 1 →
        final.getMem a = s.getMem a) ∧
      n ≤ 400 ∧ c ≤ 470 := by
  obtain ⟨captureN,captured,captureBound,captureTrace,capturePc,
    captureData,captureStack,captureFrame,captureKey,captureLow,_⟩ :=
      GroupedBalancedSignUpperH2StartData67.captured_state hash s
        base leaf witnessBase chain seed entry witnessLower witnessBound aligned
  have positive : 0 < maxDigit chain := by
    have bound := (GroupedBalancedSignUpperH2Invariant67.max_bounds chain).1
    omega
  obtain ⟨loopN,mid,loopBound,loopTrace,midPc,midData,
    loopStack,loopFrame,loopKey,loopLow⟩ :=
      GroupedBalancedSignUpperH2RunFrame67.run_remaining_framed
        hash captured base leaf witnessBase chain 0 (maxDigit chain)
        seed positive (by simp) captureData capturePc baseBound
        witnessBound witnessLower aligned
  have counter : mid.getMem 0x81030 = BitVec.ofNat 64 chain.val :=
    midData.counter
  obtain ⟨safe0,safe1⟩ :=
    GroupedBalancedSignUpperEndpointStore67.address_valid mid chain.val
      counter chain.isLt
  have storeTrace := GroupedBalancedSignUpperEndpointStore67.store_steps
    mid midPc safe0 safe1
  let final := store mid
  have pretrace : Trace hash image s
      (47 + GroupedBalancedSignUpperMaxChoice67.stepsFor
        (BitVec.ofNat 64 chain.val) + captureN)
      (47 + GroupedBalancedSignUpperMaxChoice67.stepsFor
        (BitVec.ofNat 64 chain.val) + captureN) 0 0 captured :=
    captureTrace.trace
  have full := (pretrace.trans loopTrace).trans
    (storeTrace.trace (hash := hash))
  have stepsBound : GroupedBalancedSignUpperMaxChoice67.stepsFor
      (BitVec.ofNat 64 chain.val) ≤ 8 := by
    simp only [GroupedBalancedSignUpperMaxChoice67.stepsFor]
    split_ifs <;> omega
  have digitBound := (GroupedBalancedSignUpperH2Invariant67.max_bounds chain).2
  refine ⟨(47 + GroupedBalancedSignUpperMaxChoice67.stepsFor
      (BitVec.ofNat 64 chain.val) + captureN) + loopN + 19,
    (47 + GroupedBalancedSignUpperMaxChoice67.stepsFor
      (BitVec.ofNat 64 chain.val) + captureN) +
      (loopN+7*maxDigit chain)+19,final,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [final,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using full
  · exact GroupedBalancedSignUpperEndpointControl67.store_pc_chain mid
      chain.val midPc counter chain.isLt
  · exact GroupedBalancedSignUpperEndpointControl67.store_counter_eq
      mid chain.val counter
  · intro j
    rw [GroupedBalancedSignUpperEndpointData67.store_values mid chain.val
      counter chain.isLt j]
    simpa only [Nat.zero_add] using midData.value j
  · rw [GroupedBalancedSignUpperEndpointStore67.store_stack,
      loopStack,captureStack]
  · intro j
    let a := Signing.wordAddress 0x20 j.val
    have aSmall : a.toNat < 0x100 := by fin_cases j <;> decide
    have addressEq := GroupedBalancedSignUpperEndpointStore67.address_eq
      mid chain.val counter
    have dstNat : (dst mid).toNat = 0x80800+16*chain.val := by
      change (GroupedBalancedSignUpperEndpointStore67.address mid).toNat = _
      rw [addressEq]
      have small : 0x80800+16*chain.val < 18446744073709551616 := by omega
      simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
    have nextNat : (dst mid + 8).toNat = 0x80800+16*chain.val+8 := by
      change (GroupedBalancedSignUpperEndpointStore67.address mid + 8).toNat = _
      rw [addressEq]
      have sum : BitVec.ofNat 64 (0x80800+16*chain.val) + 8 =
          BitVec.ofNat 64 (0x80800+16*chain.val+8) :=
        (BitVec.ofNat_add _ _).symm
      rw [sum]
      have small : 0x80800+16*chain.val+8 < 18446744073709551616 := by omega
      simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
    have neDst : a ≠ dst mid := by
      intro eq
      have he := congrArg BitVec.toNat eq
      rw [dstNat] at he
      omega
    have neNext : a ≠ dst mid + 8 := by
      intro eq
      have he := congrArg BitVec.toNat eq
      rw [nextNat] at he
      omega
    have neCounter : a ≠ 0x81030 := by fin_cases j <;> decide
    rw [GroupedBalancedSignUpperEndpointStore67.store_frame mid a
      neCounter neDst neNext,loopKey j,captureKey j]
  · intro a high notStep notCounter notDst0 notDst1
    have addressEq := GroupedBalancedSignUpperEndpointStore67.address_eq
      mid chain.val counter
    have neq0 : a ≠ dst mid := by
      simpa only [dst,addressEq,Signing.wordAddress,Nat.mul_zero,
        Nat.add_zero] using notDst0
    have neq1 : a ≠ dst mid + 8 := by
      have next : dst mid + 8 = Signing.wordAddress
          (0x80800+16*chain.val) 1 := by
        change GroupedBalancedSignUpperEndpointStore67.address mid + 8 = _
        rw [addressEq]
        simp [Signing.wordAddress,BitVec.ofNat_add]
      simpa only [next] using notDst1
    rw [GroupedBalancedSignUpperEndpointStore67.store_frame mid a
      notCounter neq0 neq1]
    exact (loopFrame a high).trans (captureFrame a high notStep)
  · intro a low ne0 ne1
    have addressEq := GroupedBalancedSignUpperEndpointStore67.address_eq
      mid chain.val counter
    have dstNat : (dst mid).toNat = 0x80800+16*chain.val := by
      change (GroupedBalancedSignUpperEndpointStore67.address mid).toNat = _
      rw [addressEq]
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt
        (by omega : 0x80800+16*chain.val < 2^64)]
    have nextNat : (dst mid + 8).toNat = 0x80800+16*chain.val+8 := by
      rw [BitVec.toNat_add,dstNat]
      change (0x80800+16*chain.val+8) % 2^64 = _
      rw [Nat.mod_eq_of_lt (by omega : 0x80800+16*chain.val+8 < 2^64)]
    have ndst : a ≠ dst mid := by
      intro eq
      have h := congrArg BitVec.toNat eq
      rw [dstNat] at h
      omega
    have nnext : a ≠ dst mid + 8 := by
      intro eq
      have h := congrArg BitVec.toNat eq
      rw [nextNat] at h
      omega
    have ncounter : a ≠ 0x81030 := by
      intro eq
      have h := congrArg BitVec.toNat eq
      simp at h
      omega
    rw [GroupedBalancedSignUpperEndpointStore67.store_frame mid a
      ncounter ndst nnext]
    have lowMid := loopLow a low ne0 ne1
    exact lowMid.trans (captureLow a low ne0 ne1)
  · omega
  · omega

end
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2OneChain67
