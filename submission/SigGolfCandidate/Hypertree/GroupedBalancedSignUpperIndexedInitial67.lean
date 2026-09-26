import SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafPath67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperIndexMask67


/-! Two digest words at 0x80500 determine the next decoder's 16 bytes. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastDigestBytes67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

theorem digest_words_bytes (s : MachineState)
    (digest : Reference.Digest)
    (words : ∀ half : Fin 2,
      s.getMem (Signing.wordAddress 0x80500 half.val) =
        digest.extractLsb' (64*half.val) 64) :
    ∀ j : Fin 16,
      s.getByte (BitVec.ofNat 64 (0x80500+j.val)) =
        digest.extractLsb' (8*j.val) 8 := by
  intro j
  have lowWord : s.getMem 0x80500 = digest.extractLsb' 0 64 := by
    simpa [Signing.wordAddress] using words 0
  have highWord : s.getMem 0x80508 = digest.extractLsb' 64 64 := by
    simpa [Signing.wordAddress] using words 1
  have addr0 : (525568#64) = (0x80500 : Word) := by decide
  have addr1 : (525576#64) = (0x80508 : Word) := by decide
  fin_cases j <;>
    simp [MachineState.getByte,alignToDword,byteOffset,extractByte] <;>
    (first | rw [addr0,lowWord] | rw [addr1,highWord]) <;>
    apply BitVec.eq_of_toNat_eq <;>
    simp [BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,
      BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow] <;>
    omega

#print axioms digest_words_bytes

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastDigestBytes67


/-! The 192-bit index supplies both upper-group setup branches directly. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperIndexedInitial67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperLeafFold67
open GroupedBalancedSignUpperBaseToInitial67
open GroupedBalancedSignUpperIndexMask67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

def CurrentWords (s : MachineState) (message : BitVec 128) : Prop :=
  ∀ half : Fin 2,
    s.getMem (Signing.wordAddress 0x80500 half.val)=
      message.extractLsb' (64*half.val) 64

private theorem current_outside : OutsideCommon (0x810f0 : Word) := by
  unfold OutsideCommon
  refine ⟨by decide,by decide,by decide,?_,?_⟩
  · intro i hi
    interval_cases i <;> decide
  · intro i hi
    interval_cases i <;> decide

theorem current_message_bytes (s : MachineState) (message : BitVec 128)
    (current : CurrentWords s message) :
    ∀ j : Fin 16,
      s.getByte (BitVec.ofNat 64 (0x80500+j.val))=
        message.extractLsb' (8*j.val) 8 := by
  exact GroupedBalancedByteFastDigestBytes67.digest_words_bytes s message current

theorem boundary_current (s t : MachineState) (message : BitVec 128)
    (frame : BoundaryFrame s t) (current : CurrentWords s message) :
    CurrentWords t message := by
  rcases frame with ⟨_,_,_,_,low,high,_⟩
  intro half
  fin_cases half
  · change t.getMem 0x80500 = _
    rw [low]
    simpa [Signing.wordAddress] using current (0 : Fin 2)
  · change t.getMem 0x80508 = _
    rw [high]
    simpa [Signing.wordAddress] using current (1 : Fin 2)

theorem boundary_index (s t : MachineState) (index : BitVec 192)
    (frame : BoundaryFrame s t)
    (words : ∀ w : Fin 3,
      s.getMem (Signing.wordAddress 0x81090 w.val)=
        index.extractLsb' (64*w.val) 64) :
    ∀ w : Fin 3,
      t.getMem (Signing.wordAddress 0x81090 w.val)=
        index.extractLsb' (64*w.val) 64 := by
  rcases frame with ⟨_,w0,w1,w2,_,_,_⟩
  intro w
  fin_cases w
  · change t.getMem 0x81090 = _
    rw [w0]
    simpa [Signing.wordAddress] using words (0 : Fin 3)
  · change t.getMem 0x81098 = _
    rw [w1]
    simpa [Signing.wordAddress] using words (1 : Fin 3)
  · change t.getMem 0x810a0 = _
    rw [w2]
    simpa [Signing.wordAddress] using words (2 : Fin 3)

theorem boundary_key (s t : MachineState) (secretKey : SecretKey)
    (frame : BoundaryFrame s t)
    (keyWords : ∀ j : Fin 4,
      s.getMem (Signing.wordAddress 0x20 j.val)=
        secretKey.extractLsb' (64*j.val) 64) :
    ∀ j : Fin 4,
      t.getMem (Signing.wordAddress 0x20 j.val)=
        secretKey.extractLsb' (64*j.val) 64 := by
  rcases frame with ⟨_,_,_,_,_,_,low⟩
  intro j
  rw [low _ (by fin_cases j <;> decide)]
  exact keyWords j

theorem boundary_layer (s t : MachineState)
    (frame : BoundaryFrame s t) :
    t.getMem 0x81058=s.getMem 0x81058 := frame.1

theorem entry_table_frame (s t : MachineState)
    (frame : ∀ a : Word, OutsideCommon a →
      (a.toNat<0x80600 ∨ 0x80800≤a.toNat) →
      a≠0x810e0 → a≠0x810f8 → t.getMem a=s.getMem a) :
    ∀ a : Word, 0xfff700≤a.toNat → t.getMem a=s.getMem a := by
  intro a ha
  have different (b : Word) (hb : b.toNat<0x90000) : a≠b := by
    intro he
    subst a
    omega
  exact frame a (outside_range a (Or.inr (by omega)))
    (Or.inr (by omega))
    (different 0x810e0 (by decide))
    (different 0x810f8 (by decide))

theorem h3 (hash : Hash) (secretKey : SecretKey)
    (treeBase witnessBase : Nat) (index : BitVec 192)
    (s : MachineState) (message : BitVec 128)
    (pc : s.pc=0x15e0) (height : s.getMem 0x81060=3)
    (stack : s.getReg .x2=0xfff700)
    (hmsg : ∀ j : Fin 16,
      s.getByte (BitVec.ofNat 64 (0x80500+j.val)) =
        message.extractLsb' (8*j.val) 8)
    (tables : GroupedBalancedVerifyByteContract67.Tables s)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (current : ∃ b : Nat,
      s.getMem 0x810f0=BitVec.ofNat 64 b ∧ witnessBase=b+1072 ∧
      0x20060≤b ∧ b+16*67≤0x80000 ∧ b%8=0)
    (keyWords : ∀ j : Fin 4,
      s.getMem (Signing.wordAddress 0x20 j.val)=
        secretKey.extractLsb' (64*j.val) 64)
    (indexWords : ∀ w : Fin 3,
      s.getMem (Signing.wordAddress 0x81090 w.val)=
        index.extractLsb' (64*w.val) 64) :
    ∃ finish : MachineState,
      OrdinarySteps image s (61+entryCost message) finish ∧
      Inv hash secretKey treeBase (index.toNat/8*8) 3
        (index.toNat%8) witnessBase 0 finish ∧
      BoundaryFrame s finish ∧
      finish.getReg .x2=s.getReg .x2 ∧
      (∀ a : Word, 0xfff700≤a.toNat → finish.getMem a=s.getMem a) ∧
      (∀ j : GroupedBalancedUpperTree67.ChainMixed,
        finish.getByte (BitVec.ofNat 64 (0x80600+j.val))=
          BitVec.ofNat 8 (GroupedBalancedUpperTree67.digit message j).val) ∧
      (∀ a : Word, a.toNat<0x80000 → finish.getMem a=s.getMem a) ∧
      finish.getMem 0x810f0=s.getMem 0x810f0 := by
  obtain ⟨selected,rounded,upper⟩ := h3_fields s index indexWords
  obtain ⟨finish,path,inv,frame,sp,digits,signatureFrame⟩ :=
    h3_initial hash secretKey treeBase (index.toNat/8*8)
      (index.toNat%8) witnessBase s message pc height stack hmsg tables
      tree current keyWords selected rounded upper
  exact ⟨finish,path,inv,boundary_frame s finish frame,sp,
    entry_table_frame s finish frame,digits,signatureFrame,
    frame 0x810f0 current_outside
      (Or.inr (by decide)) (by decide) (by decide)⟩

theorem h4 (hash : Hash) (secretKey : SecretKey)
    (treeBase witnessBase : Nat) (index : BitVec 192)
    (s : MachineState) (message : BitVec 128)
    (pc : s.pc=0x15e0) (height : s.getMem 0x81060=4)
    (stack : s.getReg .x2=0xfff700)
    (hmsg : ∀ j : Fin 16,
      s.getByte (BitVec.ofNat 64 (0x80500+j.val)) =
        message.extractLsb' (8*j.val) 8)
    (tables : GroupedBalancedVerifyByteContract67.Tables s)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (current : ∃ b : Nat,
      s.getMem 0x810f0=BitVec.ofNat 64 b ∧ witnessBase=b+1072 ∧
      0x20060≤b ∧ b+16*67≤0x80000 ∧ b%8=0)
    (keyWords : ∀ j : Fin 4,
      s.getMem (Signing.wordAddress 0x20 j.val)=
        secretKey.extractLsb' (64*j.val) 64)
    (indexWords : ∀ w : Fin 3,
      s.getMem (Signing.wordAddress 0x81090 w.val)=
        index.extractLsb' (64*w.val) 64) :
    ∃ finish : MachineState,
      OrdinarySteps image s (60+entryCost message) finish ∧
      Inv hash secretKey treeBase (index.toNat/16*16) 4
        (index.toNat%16) witnessBase 0 finish ∧
      BoundaryFrame s finish ∧
      finish.getReg .x2=s.getReg .x2 ∧
      (∀ a : Word, 0xfff700≤a.toNat → finish.getMem a=s.getMem a) ∧
      (∀ j : GroupedBalancedUpperTree67.ChainMixed,
        finish.getByte (BitVec.ofNat 64 (0x80600+j.val))=
          BitVec.ofNat 8 (GroupedBalancedUpperTree67.digit message j).val) ∧
      (∀ a : Word, a.toNat<0x80000 → finish.getMem a=s.getMem a) ∧
      finish.getMem 0x810f0=s.getMem 0x810f0 := by
  obtain ⟨selected,rounded,upper⟩ := h4_fields s index indexWords
  obtain ⟨finish,path,inv,frame,sp,digits,signatureFrame⟩ :=
    h4_initial hash secretKey treeBase (index.toNat/16*16)
      (index.toNat%16) witnessBase s message pc height stack hmsg tables
      tree current keyWords selected rounded upper
  exact ⟨finish,path,inv,boundary_frame s finish frame,sp,
    entry_table_frame s finish frame,digits,signatureFrame,
    frame 0x810f0 current_outside
      (Or.inr (by decide)) (by decide) (by decide)⟩

#print axioms h3
#print axioms h4
#print axioms current_message_bytes
#print axioms boundary_current
#print axioms boundary_index
#print axioms boundary_key
#print axioms entry_table_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperIndexedInitial67
