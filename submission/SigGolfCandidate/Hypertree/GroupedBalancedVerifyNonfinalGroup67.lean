import SigGolfCandidate.Hypertree.GroupedBalancedVerifyNonfinalDecoded67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeDecoderHandoff67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyStackGlobal67
import SigGolfCandidate.Hypertree.GroupedBalancedSignByteFullMemFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyWireFrame67

/-! One complete nonfinal verifier group from call site to next call site. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyNonfinalGroup67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem trace_steps_le_cycles (hash : Hash) (program : Image)
    {s t : MachineState} {steps cycles calls blocks : Nat}
    (run : Trace hash program s steps cycles calls blocks t) :
    steps ≤ cycles := by
  induction run with
  | refl => omega
  | ordinary state next final instruction steps cycles calls blocks
      fetched step tail ih =>
      omega
  | hash state final steps cycles calls blocks fetched service valid tail ih =>
      have charged : 1 ≤ 8 * compressions (hashInput state).1 := by
        have one : 1 ≤ compressions (hashInput state).1 := by
          unfold compressions
          exact Nat.le_max_left 1 _
        omega
      omega

def decoderCost (message : Reference.Digest) : Nat :=
  8+112+(if GroupedBalancedQuaternary.rawSum message < 96 then 9 else 10)+144+6

theorem decoderCost_le (message : Reference.Digest) :
    decoderCost message ≤ 280 := by
  unfold decoderCost
  split_ifs <;> omega

theorem charged_cycles_bound (message : Reference.Digest)
    (height cycles tailSteps : Nat)
    (cycleBound : cycles ≤ 202+172*height)
    (tailBound : tailSteps ≤ 15) :
    1+decoderCost message+
      (11*GroupedBalancedChecksum67.suffixCost message+1281+
        cycles+tailSteps) ≤ 2857+172*height := by
  have suffix := GroupedBalancedChecksum67.suffix_cost_le message
  have decoder := decoderCost_le message
  omega

theorem decoder_mem_other (s : MachineState)
    (message : Reference.Digest) (a : Word)
    (outside : a.toNat < 0x80600 ∨ 0x80648 ≤ a.toNat) :
    (GroupedBalancedVerifyByteFull67.fullDecoderState s message).getMem a =
      s.getMem a := by
  have hflag : a ≠ (0x80640 : Word) := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rcases outside with lo | hi <;> simp at hn <;> omega
  have hcopy : ∀ k, k < 16 →
      a ≠ alignToDword (BitVec.ofNat 64 (0x80600+4*k)) := by
    intro k hk eq
    have hn := congrArg BitVec.toNat eq
    have hv : (alignToDword (BitVec.ofNat 64 (0x80600+4*k))).toNat =
        0x80600 + 8*(k/2) := by
      interval_cases k <;> decide
    rw [hv] at hn
    rcases outside with lo | hi <;> omega
  exact GroupedBalancedSignByteFullMemFrame67.fullDecoder_mem s message a
    hflag hcopy

theorem next_group (hash : Hash) (s : MachineState)
    (g base leaf start height : Nat)
    (pc : s.pc = 0x1514)
    (stack : s.getReg .x2 = 0xfff700)
    (group : s.getMem 0x81058 = BitVec.ofNat 64 g)
    (groupBound : g < 44)
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
    ∃ next steps cycles tailSteps,
      tailSteps ≤ 15 ∧
      Trace hash image s
        (1+decoderCost message+
          (4*GroupedBalancedChecksum67.suffixCost message+1281+
            steps+tailSteps))
        (1+decoderCost message+
          (11*GroupedBalancedChecksum67.suffixCost message+1281+
            cycles+tailSteps))
        (GroupedBalancedChecksum67.suffixCost message+1+height)
        (GroupedBalancedChecksum67.suffixCost message+18+height) next ∧
      next.pc = 0x1514 ∧
      next.getMem 0x81048 =
        BitVec.ofNat 64 (start+16*67+16*height) ∧
      next.getMem 0x81058 = BitVec.ofNat 64 (g+1) ∧
      next.getMem 0x81060 =
        (if g = 29 then 4 else BitVec.ofNat 64 height) ∧
      next.getMem 0x81000 = BitVec.ofNat 64 (base+height) ∧
      GroupedBalancedByteFastEdgeIndexRefine67.StoredIndex next
        (BitVec.ofNat 192 (leaf/2^height)) ∧
      (∀ a : Word, a.toNat < 0x80000 → next.getMem a = s.getMem a) ∧
      GroupedBalancedVerifyByteContract67.Tables next ∧
      next.getReg .x2 = 0xfff700 ∧
      (∀ half : Fin 2,
        next.getMem (Signing.wordAddress 0x80500 half.val) =
          (GroupedBalancedByteFastUpperPathIter67.rootAt hash base leaf
            (GroupedBalancedUpperTree67.compressLeaf hash base leaf
              (GroupedBalancedByteFastEndpointAccum67.expectedEndpoint hash
                base leaf message
                (GroupedBalancedVerifyGenericPath67.witnessDigest
                  s start)))
            (GroupedBalancedVerifyGenericPath67.siblingDigest s start)
            height).extractLsb' (64*half.val) 64) ∧
      cycles ≤ 202+172*height := by
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
  have decodedBase : decoded.getMem 0x81000 = BitVec.ofNat 64 base := by
    rw [decoder_mem_other called _ 0x81000 (Or.inr (by decide)),
      GroupedBalancedVerifyTreePost67.call_mem]
    exact baseWord
  have decodedIndex : GroupedBalancedByteFastEdgeIndexRefine67.StoredIndex
      decoded (BitVec.ofNat 192 leaf) := by
    intro i
    rw [decoder_mem_other called _ _ (Or.inr (by fin_cases i <;> decide)),
      GroupedBalancedVerifyTreePost67.call_mem]
    exact index i
  have decodedStart : decoded.getMem 0x81048 = BitVec.ofNat 64 start := by
    rw [decoder_mem_other called _ 0x81048 (Or.inr (by decide)),
      GroupedBalancedVerifyTreePost67.call_mem]
    exact startWord
  have decodedHeight : decoded.getMem 0x81060 =
      BitVec.ofNat 64 height := by
    rw [decoder_mem_other called _ 0x81060 (Or.inr (by decide)),
      GroupedBalancedVerifyTreePost67.call_mem]
    exact heightWord
  have decodedGroup : decoded.getMem 0x81058 = BitVec.ofNat 64 g := by
    rw [decoder_mem_other called _ 0x81058 (Or.inr (by decide)),
      GroupedBalancedVerifyTreePost67.call_mem]
    exact group
  obtain ⟨next,steps,cycles,tailSteps,tailBound,run,nextPc,root,ptr,
    groupNext,heightNext,baseNext,indexNext,low,tablesNext,
    cyclesBound⟩ :=
    GroupedBalancedVerifyNonfinalDecoded67.next_group hash decoded
      g base leaf start height message decodedPc decodedGroup groupBound
      decodedBase decodedIndex decodedStart decodedHeight decodedTables
      decodedDigits heightChoice aligned wireBound baseBound leafBound
  have decodedLow (a : Word) (ha : a.toNat < 0x80000) :
      decoded.getMem a = s.getMem a := by
    rw [decoder_mem_other called _ a (Or.inl (by omega)),
      GroupedBalancedVerifyTreePost67.call_mem]
  have fullTrace : Trace hash image s
      (1+decoderCost message+
        (4*GroupedBalancedChecksum67.suffixCost message+1281+
          steps+tailSteps))
      (1+decoderCost message+
        (11*GroupedBalancedChecksum67.suffixCost message+1281+
          cycles+tailSteps))
      (GroupedBalancedChecksum67.suffixCost message+1+height)
      (GroupedBalancedChecksum67.suffixCost message+18+height) next := by
    have decoderTrace : OrdinarySteps image called (decoderCost message)
        decoded := by
      simpa [decoderCost,decoded,rootEq] using decoder
    have all := (call.trace.trans decoderTrace.trace).trans run
    convert all using 1 <;> omega
  have nextStack := GroupedBalancedVerifyStackGlobal67.trace_stack hash
    fullTrace
  refine ⟨next,steps,cycles,tailSteps,tailBound,fullTrace,
    nextPc,ptr,groupNext,heightNext,baseNext,indexNext,?_,tablesNext,?_,
    ?_,cyclesBound⟩
  · intro a ha
    rw [low a ha,decodedLow a ha]
  · exact nextStack.trans stack
  · intro half
    rw [root half,
      GroupedBalancedVerifyWireFrame67.group_root_frame hash s decoded
        base leaf start height message wireBound decodedLow]

#print axioms next_group
#print axioms trace_steps_le_cycles
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyNonfinalGroup67
