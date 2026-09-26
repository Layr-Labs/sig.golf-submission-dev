import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafEntry67
import SigGolfCandidate.Hypertree.GroupedBalancedSignByteFullMemFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafFold67


/-! The upper decoder writes only its digit buffer and two local control words. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafEntryFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open GroupedBalancedSignUpperDecoderCall67
open GroupedBalancedSignUpperDecoded67
open GroupedBalancedSignUpperLeafInit67
open GroupedBalancedSignUpperLeafEntry67
open GroupedBalancedSignByteFullMemFrame67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem entry_mem (s : MachineState) (message : BitVec 128)
    (a : Word) (notCount : a ≠ 0x810e0) (notWitness : a ≠ 0x810f8)
    (notFlag : a ≠ 0x80640)
    (notCopy : ∀ k, k < 16 →
      a ≠ alignToDword (BitVec.ofNat 64 (0x80600+4*k))) :
    (leafEntryState s message).getMem a = s.getMem a := by
  change (initState (decodedState s message)).getMem a = _
  rw [init_frame _ a notCount]
  change (GroupedBalancedSignByteFull67.fullDecoderState (callState s) message).getMem a = _
  rw [fullDecoder_mem _ _ a notFlag notCopy,
    call_mem_other s a notWitness]

theorem entry_stack (s : MachineState) (message : BitVec 128) :
    (leafEntryState s message).getReg .x2 = s.getReg .x2 := by
  have init_stack (t : MachineState) : (initState t).getReg .x2 = t.getReg .x2 := by
    simp [initState, execInstrBr, MachineState.getReg_setReg_ne]
  rw [leafEntryState, init_stack]
  change (GroupedBalancedSignByteFull67.fullDecoderState (callState s) message).getReg .x2 = _
  rw [fullDecoder_x2, call_stack]

theorem entry_witness (s : MachineState) (message : BitVec 128) :
    (leafEntryState s message).getMem 0x810f8 =
      s.getMem 0x810f0 + 1072 := by
  rw [leafEntryState, init_frame _ _ (by decide)]
  change (GroupedBalancedSignByteFull67.fullDecoderState (callState s) message).getMem 0x810f8 = _
  rw [fullDecoder_mem _ _ _ (by decide)
    (by intro k hk; interval_cases k <;> decide), call_path]

end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafEntryFrame67


/-! A decoded upper group starts its 67-chain loop with all tree and key data. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafInitial67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open GroupedBalancedSignUpperLeafFold67
open GroupedBalancedSignUpperLeafH3Data67
open GroupedBalancedSignUpperLeafEntry67
open GroupedBalancedSignUpperLeafEntryFrame67
open GroupedBalancedVerifyByteContract67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

theorem initial (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected witnessBase : Nat)
    (s : MachineState) (message : BitVec 128)
    (pc : s.pc = 0x1720)
    (stack : s.getReg .x2 = 0xfff700)
    (hmsg : ∀ j : Fin 16,
      s.getByte (BitVec.ofNat 64 (0x80500+j.val)) =
        message.extractLsb' (8*j.val) 8)
    (tables : Tables s)
    (limit : s.getMem 0x810d0 = BitVec.ofNat 64 (2^height))
    (chosen : s.getMem 0x810e8 = BitVec.ofNat 64 selected)
    (tree : s.getMem 0x81000 = BitVec.ofNat 64 treeBase)
    (heightWord : s.getMem 0x81060 = BitVec.ofNat 64 height)
    (current : ∃ b : Nat,
      s.getMem 0x810f0 = BitVec.ofNat 64 b ∧
      witnessBase=b+1072 ∧ 0x20060≤b ∧ b+16*67≤0x80000 ∧ b%8=0)
    (address : ∀ w : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 w.val) =
        (BitVec.ofNat 192 leafBase).extractLsb' (64*w.val) 64)
    (scratch : ∀ w : Fin 3,
      s.getMem (Signing.wordAddress 0x810a8 w.val) =
        (BitVec.ofNat 192 leafBase).extractLsb' (64*w.val) 64)
    (keyWords : ∀ j : Fin 4,
      s.getMem (Signing.wordAddress 0x20 j.val) =
        secretKey.extractLsb' (64*j.val) 64) :
    OrdinarySteps image s
      (8 + (8+112+(if GroupedBalancedQuaternary.rawSum message < 96 then 9 else 10)+144+6) + 4)
      (leafEntryState s message) ∧
    Inv hash secretKey treeBase leafBase height selected witnessBase 0
      (leafEntryState s message) := by
  obtain ⟨path,entryPc,entryCount,digits,entryTables⟩ :=
    leaf_entry s message pc stack hmsg tables
  let finish := leafEntryState s message
  have stable (a : Word) (notCount : a≠0x810e0)
      (notWitness : a≠0x810f8) (notFlag : a≠0x80640)
      (notCopy : ∀ k, k<16 →
        a ≠ alignToDword (BitVec.ofNat 64 (0x80600+4*k))) :
      finish.getMem a=s.getMem a :=
    entry_mem s message a notCount notWitness notFlag notCopy
  have stableHigh (a : Word) (ha : 0x81000 ≤ a.toNat)
      (hc : a≠0x810e0) (hw : a≠0x810f8) :
      finish.getMem a=s.getMem a := by
    apply stable a hc hw
    · intro he
      have hn := congrArg BitVec.toNat he
      simp at hn
      omega
    · intro k hk he
      have hn := congrArg BitVec.toNat he
      have hsmall : (alignToDword (BitVec.ofNat 64 (0x80600+4*k))).toNat < 0x81000 := by
        interval_cases k <;> decide
      omega
  have stableLow (a : Word) (ha : a.toNat<0x100) :
      finish.getMem a=s.getMem a := by
    apply stable a
    · intro he
      have hn := congrArg BitVec.toNat he
      simp at hn
      omega
    · intro he
      have hn := congrArg BitVec.toNat he
      simp at hn
      omega
    · intro he
      have hn := congrArg BitVec.toNat he
      simp at hn
      omega
    · intro k hk he
      have hn := congrArg BitVec.toNat he
      have hlarge : 0x80600 ≤
          (alignToDword (BitVec.ofNat 64 (0x80600+4*k))).toNat := by
        interval_cases k <;> decide
      omega
  obtain ⟨b,bword,bnext,bLower,bUpper,bAlign⟩ := current
  have witness : finish.getMem 0x810f8 = BitVec.ofNat 64 witnessBase := by
    rw [entry_witness, bword, bnext]
    simp [BitVec.ofNat_add]
  have currentWitness : ∃ b : Nat,
      finish.getMem 0x810f0 = BitVec.ofNat 64 b ∧
      0x20060 ≤ b ∧ b+16*67 ≤ 0x80000 ∧ b%8=0 := by
    exact ⟨b, (stableHigh 0x810f0 (by decide) (by decide)
      (by decide)).trans bword,bLower,bUpper,bAlign⟩
  have finishAddress : ∀ w : Fin 3,
      finish.getMem (Signing.wordAddress 0x81008 w.val) =
        (BitVec.ofNat 192 leafBase).extractLsb' (64*w.val) 64 := by
    intro w
    rw [stableHigh _ (by fin_cases w <;> decide)
      (by fin_cases w <;> decide) (by fin_cases w <;> decide)]
    exact address w
  have finishScratch : ∀ w : Fin 3,
      finish.getMem (Signing.wordAddress 0x810a8 w.val) =
        (BitVec.ofNat 192 leafBase).extractLsb' (64*w.val) 64 := by
    intro w
    rw [stableHigh _ (by fin_cases w <;> decide)
      (by fin_cases w <;> decide) (by fin_cases w <;> decide)]
    exact scratch w
  refine ⟨path,?_,?_,witness,currentWitness,?_,?_⟩
  · refine ⟨?_,entryCount,?_,?_,?_,?_,finishScratch,?_⟩
    · simpa using entryPc
    · exact (stableHigh 0x810d0 (by decide) (by decide)
        (by decide)).trans limit
    · exact (stableHigh 0x810e8 (by decide) (by decide)
        (by decide)).trans chosen
    · exact (stableHigh 0x81000 (by decide) (by decide)
        (by decide)).trans tree
    · intro hi w
      simpa using finishAddress w
    · intro j hj
      omega
  · exact (stableHigh 0x81060 (by decide) (by decide)
      (by decide)).trans heightWord
  · rw [entry_stack,stack]
    right
    rfl
  · intro j
    rw [stableLow _ (by fin_cases j <;> decide)]
    exact keyWords j

#print axioms initial
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafInitial67
