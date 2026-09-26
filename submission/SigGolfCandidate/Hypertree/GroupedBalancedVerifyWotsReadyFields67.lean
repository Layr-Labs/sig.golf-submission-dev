import SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsReady67

/-! The verifier state after the decoder enters the existing concrete WOTS proof. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsReadyFields67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyWotsReady67
open GroupedBalancedVerifyWotsHeaderFields67
open GroupedBalancedByteFastChainReady67
open GroupedBalancedByteFastChainCarry67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem ready_witness_ptr (s : MachineState) :
    (readyState s).getReg .x22 = s.getMem 0x81048 := by
  change (GroupedBalancedByteFastLimit67.initialChainState
    (GroupedBalancedVerifyWotsHeaderBlock67.headerState s)).getReg .x22 = _
  rw [GroupedBalancedByteFastLimit67.initialChainState]
  simp [GroupedBalancedByteFastLimit67.initialState,
    GroupedBalancedByteFastLimit67.pointerState,execInstrBr,
    MachineState.getReg_setReg_ne,
    header_witness_ptr]

theorem ready_witnesses (s : MachineState) (start : Nat)
    (values : Fin 67 → Reference.Digest)
    (safe : SafeWitnesses start)
    (witnesses : WitnessWords s start values) :
    WitnessWords (readyState s) start values := by
  intro chain half
  rw [ready_mem,header_low_frame s _ (safe chain half).2]
  exact witnesses chain half

theorem ready_first (s : MachineState) (base leaf start : Nat)
    (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (pc : s.pc = 0x1518)
    (baseWord : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (index : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (startWord : s.getMem 0x81048 = BitVec.ofNat 64 start)
    (safe : SafeWitnesses start)
    (witnesses : WitnessWords s start values)
    (tables : GroupedBalancedVerifyByteContract67.Tables (readyState s))
    (digits : GroupedBalancedByteFastWotsFrame67.Digits
      (readyState s) message) :
    Ready (readyState s) base leaf start ⟨0,by decide⟩
      message values := by
  obtain ⟨chain,output,digit,limit,src,len,dst,service⟩ :=
    GroupedBalancedByteFastLimit67.initial_chain_fields
      (GroupedBalancedVerifyWotsHeaderBlock67.headerState s)
  constructor
  · exact ready_pc s pc
  · refine ⟨⟨0,by decide⟩,?_,?_,src,len,dst,service⟩
    · exact ⟨0,by decide,ready_header s base baseWord⟩
    · exact ready_index s leaf index
  · simpa using (ready_witness_ptr s).trans startWord
  · simpa [readyState] using chain
  · simpa [readyState] using output
  · simpa [readyState] using digit
  · simpa [readyState,GroupedBalancedChecksum67.maxDigit] using limit
  · exact ready_witnesses s start values safe witnesses
  · exact digits
  · exact tables

#print axioms ready_witness_ptr
#print axioms ready_witnesses
#print axioms ready_first
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsReadyFields67
