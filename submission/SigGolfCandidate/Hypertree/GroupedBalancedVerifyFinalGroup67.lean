import SigGolfCandidate.Hypertree.GroupedBalancedVerifyNonfinalGroup67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyFinalPath67

/-! The last verifier group compares its recovered root to the public key. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyFinalGroup67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

def publicKeyDigest (s : MachineState) : Reference.Digest :=
  s.getMem 0x48 ++ s.getMem 0x40

def recoveredRoot (hash : Hash) (s : MachineState)
    (base leaf start height : Nat) : Reference.Digest :=
  GroupedBalancedByteFastUpperPathIter67.rootAt hash base leaf
    (GroupedBalancedUpperTree67.compressLeaf hash base leaf
      (GroupedBalancedByteFastEndpointAccum67.expectedEndpoint hash
        base leaf (GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot s)
        (GroupedBalancedVerifyGenericPath67.witnessDigest s start)))
    (GroupedBalancedVerifyGenericPath67.siblingDigest s start) height

theorem final_cycles_bound (message : Reference.Digest)
    (height cycles extra : Nat)
    (cycleBound : cycles ≤ 202+172*height)
    (extraBound : extra ≤ 27) :
    1+GroupedBalancedVerifyNonfinalGroup67.decoderCost message+
      (11*GroupedBalancedChecksum67.suffixCost message+1281+cycles)+
      extra ≤ 2869+172*height := by
  have suffix := GroupedBalancedChecksum67.suffix_cost_le message
  have decoder := GroupedBalancedVerifyNonfinalGroup67.decoderCost_le message
  omega

theorem public_key_words (s : MachineState) :
    ∀ half : Fin 2,
      s.getMem (BitVec.ofNat 64 (0x40+8*half.val)) =
        (publicKeyDigest s).extractLsb' (64*half.val) 64 := by
  intro half
  fin_cases half
  · change s.getMem 0x40 =
      (s.getMem 0x48 ++ s.getMem 0x40).extractLsb' 0 64
    exact BitVec.extractLsb'_append_eq_right.symm
  · change s.getMem 0x48 =
      (s.getMem 0x48 ++ s.getMem 0x40).extractLsb' 64 64
    exact BitVec.extractLsb'_append_eq_left.symm

theorem final_group (hash : Hash) (s : MachineState)
    (base leaf start height : Nat)
    (pc : s.pc = 0x1514)
    (stack : s.getReg .x2 = 0xfff700)
    (group : s.getMem 0x81058 = 44)
    (baseWord : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (index : GroupedBalancedByteFastEdgeIndexRefine67.StoredIndex s
      (BitVec.ofNat 192 leaf))
    (startWord : s.getMem 0x81048 = BitVec.ofNat 64 start)
    (heightWord : s.getMem 0x81060 = BitVec.ofNat 64 height)
    (tables : GroupedBalancedVerifyByteContract67.Tables s)
    (heightChoice : height = 3 ∨ height = 4)
    (aligned : start % 8 = 0)
    (wireBound : start + 16*67 + 16*height ≤ 0x38da0)
    (baseBound : base < 256)
    (leafBound : leaf < 2^192) :
    let message := GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot s
    let root := recoveredRoot hash s base leaf start height
    let pk := publicKeyDigest s
    ∃ (extra steps cycles : Nat) (final : MachineState), extra ≤ 27 ∧
      cycles ≤ 202+172*height ∧
      1+GroupedBalancedVerifyNonfinalGroup67.decoderCost message+
        (11*GroupedBalancedChecksum67.suffixCost message+1281+cycles)+
        extra ≤ 2869+172*height ∧
      1+GroupedBalancedVerifyNonfinalGroup67.decoderCost message+
        (4*GroupedBalancedChecksum67.suffixCost message+1281+steps)+
        extra ≤
      1+GroupedBalancedVerifyNonfinalGroup67.decoderCost message+
        (11*GroupedBalancedChecksum67.suffixCost message+1281+cycles)+
        extra ∧
      Executes hash image s
        (1+GroupedBalancedVerifyNonfinalGroup67.decoderCost message+
          (4*GroupedBalancedChecksum67.suffixCost message+1281+steps)+extra)
        ⟨if root = pk then .success else .failure,
          final,
          1+GroupedBalancedVerifyNonfinalGroup67.decoderCost message+
            (11*GroupedBalancedChecksum67.suffixCost message+1281+cycles)+extra,
          GroupedBalancedChecksum67.suffixCost message+1+height,
          GroupedBalancedChecksum67.suffixCost message+18+height⟩ := by
  let message := GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot s
  let called := GroupedBalancedVerifyTreePost67.callState s
  have call := GroupedBalancedVerifyTreePost67.call_step s pc
  have callPc := GroupedBalancedVerifyTreePost67.call_pc s pc
  have callLink := GroupedBalancedVerifyTreePost67.call_link s pc
  have callStack : called.getReg .x2 = 0xfff700 := by
    have h := GroupedBalancedVerifyStackGlobal67.trace_stack hash call.trace
    exact h.trans stack
  have callTables : GroupedBalancedVerifyByteContract67.Tables called :=
    GroupedBalancedVerifyTableProtected67.tables_of_table_frame
      (s := s) (t := called)
      (by intro a _; exact GroupedBalancedVerifyTreePost67.call_mem s a)
      tables
  have rootEq :
      GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot called =
        message := by
    change (GroupedBalancedVerifyTreePost67.callState s).getMem 0x80508 ++
      (GroupedBalancedVerifyTreePost67.callState s).getMem 0x80500 =
      s.getMem 0x80508 ++ s.getMem 0x80500
    rw [GroupedBalancedVerifyTreePost67.call_mem,
      GroupedBalancedVerifyTreePost67.call_mem]
  let decoded := GroupedBalancedVerifyByteFull67.fullDecoderState called
    (GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot called)
  obtain ⟨decoder,decoderDigits,decodedPc,decodedTables⟩ :=
    GroupedBalancedVerifyTreeDecoderHandoff67.decode_from_call called
      callPc callStack callLink callTables
  have decodedDigits : GroupedBalancedByteFastWotsFrame67.Digits
      decoded message := by
    simpa [decoded,GroupedBalancedByteFastWotsFrame67.Digits,rootEq]
      using decoderDigits
  have decodedMem (a : Word)
      (outside : a.toNat < 0x80600 ∨ 0x80648 ≤ a.toNat) :
      decoded.getMem a = s.getMem a := by
    rw [GroupedBalancedVerifyNonfinalGroup67.decoder_mem_other
      called _ a outside,GroupedBalancedVerifyTreePost67.call_mem]
  have decodedBase : decoded.getMem 0x81000 = BitVec.ofNat 64 base := by
    rw [decodedMem 0x81000 (Or.inr (by decide))]
    exact baseWord
  have decodedIndex : GroupedBalancedByteFastEdgeIndexRefine67.StoredIndex
      decoded (BitVec.ofNat 192 leaf) := by
    intro i
    rw [decodedMem _ (Or.inr (by fin_cases i <;> decide))]
    exact index i
  have decodedStart : decoded.getMem 0x81048 = BitVec.ofNat 64 start := by
    rw [decodedMem 0x81048 (Or.inr (by decide))]
    exact startWord
  have decodedHeight : decoded.getMem 0x81060 =
      BitVec.ofNat 64 height := by
    rw [decodedMem 0x81060 (Or.inr (by decide))]
    exact heightWord
  have decodedGroup : decoded.getMem 0x81058 = 44 := by
    rw [decodedMem 0x81058 (Or.inr (by decide))]
    exact group
  obtain ⟨mid,steps,cycles,path,midPc,midRoot,_,_,_,_,_,
    groupCarry,low,_,cycleBound⟩ :=
    GroupedBalancedVerifyGenericPath67.path_from_decoder hash decoded
      base leaf start height message decodedPc decodedBase decodedIndex
      decodedStart decodedHeight decodedTables decodedDigits heightChoice
      aligned wireBound baseBound leafBound
  have decodedLow (a : Word) (ha : a.toNat < 0x80000) :
      decoded.getMem a = s.getMem a :=
    decodedMem a (Or.inl (by omega))
  have rootFrame := GroupedBalancedVerifyWireFrame67.group_root_frame
    hash s decoded base leaf start height message wireBound decodedLow
  have rootWords : ∀ half : Fin 2,
      mid.getMem (BitVec.ofNat 64 (0x80500+8*half.val)) =
        (recoveredRoot hash s base leaf start height).extractLsb'
          (64*half.val) 64 := by
    intro half
    have h := midRoot half
    simpa [recoveredRoot,message,Signing.wordAddress,rootFrame] using h
  have fullTrace : Trace hash image s
      (1+GroupedBalancedVerifyNonfinalGroup67.decoderCost message+
        (4*GroupedBalancedChecksum67.suffixCost message+1281+steps))
      (1+GroupedBalancedVerifyNonfinalGroup67.decoderCost message+
        (11*GroupedBalancedChecksum67.suffixCost message+1281+cycles))
      (GroupedBalancedChecksum67.suffixCost message+1+height)
      (GroupedBalancedChecksum67.suffixCost message+18+height) mid := by
    have decoderTrace : OrdinarySteps image called
        (GroupedBalancedVerifyNonfinalGroup67.decoderCost message)
        decoded := by
      simpa [GroupedBalancedVerifyNonfinalGroup67.decoderCost,decoded,rootEq]
        using decoder
    have all := (call.trace.trans decoderTrace.trace).trans path
    convert all using 1 <;> omega
  have lowFrame (a : Word) (ha : a.toNat < 0x80000) :
      mid.getMem a = s.getMem a := by
    rw [low a ha,decodedLow a ha]
  obtain ⟨extra,final,extraBound,run⟩ :=
    GroupedBalancedVerifyFinalPath67.final_path_executes hash s mid
      _ _ _ _ (recoveredRoot hash s base leaf start height)
      (publicKeyDigest s) fullTrace midPc
      (groupCarry.trans decodedGroup) rootWords (public_key_words s)
      lowFrame
  have stepsLeCycles :=
    GroupedBalancedVerifyNonfinalGroup67.trace_steps_le_cycles hash image
      fullTrace
  dsimp [message] at stepsLeCycles
  exact ⟨extra,steps,cycles,final,extraBound,cycleBound,
    final_cycles_bound message height cycles extra cycleBound extraBound,
    by omega,run⟩

#print axioms final_group
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyFinalGroup67
