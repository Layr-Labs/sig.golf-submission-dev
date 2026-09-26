import SigGolfCandidate.Hypertree.GroupedBalancedSignPrepare67
import SigGolfCandidate.Hypertree.SignRefine
import SigGolfCandidate.Hypertree.GroupedBalancedProgram67Byte
import SigGolfCandidate.Hypertree.SecurityRandomOracle
import SigGolfCandidate.Hypertree.SignMemory
import SigGolfCandidate.Loader


/-! The direct67 signer's first oracle call is its reference tag6 query. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignRandomizerQuery67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem randomizer_query (original ready : MachineState)
    (secretKey : SecretKey) (message : Message)
    (hsecretKey : ∀ i, i < 32 → original.getByte
      (BitVec.ofNat 64 (0x20+i)) = secretKey.extractLsb' (8*i) 8)
    (hmessage : ∀ i, i < 32 → original.getByte
      (BitVec.ofNat 64 i) = message.extractLsb' (8*i) 8)
    (words : ∀ i : Fin 12,
      ready.getMem (Signing.wordAddress 0x80000 i.val) =
        GroupedBalancedSignPrepare67.randomizerInputWord original i) :
    hashInput (GroupedBalancedSignRandomizer67.randomizerHashState ready) =
      SecurityRandomOracle.randomizerInput secretKey message := by
  have oldWords : ∀ i : Fin 12,
      ready.getMem (Signing.wordAddress 0x80000 i.val) =
        Signing.randomizerInputWord original i := by
    intro i
    simpa [GroupedBalancedSignPrepare67.randomizerInputWord,
      Signing.randomizerInputWord] using words i
  have q := Signing.randomizer_query original ready secretKey message
    hsecretKey hmessage oldWords
  simpa [GroupedBalancedSignRandomizer67.randomizerHashState,
    Signing.randomizerHashState,SecurityRandomOracle.randomizerInput,
    SecurityRandomOracle.addressedInput,Signing.randomizerPayload,
    Reference.packed] using q

theorem entry_randomizer_refines (hash : Hash) (s : MachineState)
    (secretKey : SecretKey) (message : Message)
    (pc : s.pc = 0x1000)
    (hsecretKey : ∀ i, i < 32 → s.getByte
      (BitVec.ofNat 64 (0x20+i)) = secretKey.extractLsb' (8*i) 8)
    (hmessage : ∀ i, i < 32 → s.getByte
      (BitVec.ofNat 64 i) = message.extractLsb' (8*i) 8) :
    ∃ final,
      Trace hash GroupedBalancedSignImage67.image s 108 123 1 2 final ∧
      final.pc = 0x10d8 ∧
      (∀ i : Fin 4,
        final.getMem (Signing.wordAddress 0x20060 i.val) =
        (Reference.randomizer hash secretKey message).extractLsb'
          (64*i.val) 64) := by
  obtain ⟨ready,final,trace,done,words,output⟩ :=
    GroupedBalancedSignPrepare67.entry_randomizer_trace hash s pc
  have query := randomizer_query s ready secretKey message
    hsecretKey hmessage words
  refine ⟨final,trace,done,?_⟩
  intro i
  rw [output i,query]
  rfl

#print axioms entry_randomizer_refines

end SigGolfCandidate.Hypertree.GroupedBalancedSignRandomizerQuery67


/-! Loaded direct67 signer through its exact first oracle call. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignRandomizerLoaded67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev submission := GroupedBalancedProgram67Byte.submission

theorem entry_randomizer_low_frame (hash : Hash) (s : MachineState)
    (secretKey : SecretKey) (message : Message)
    (pc : s.pc = 0x1000)
    (hsecretKey : ∀ i, i < 32 → s.getByte
      (BitVec.ofNat 64 (0x20+i)) = secretKey.extractLsb' (8*i) 8)
    (hmessage : ∀ i, i < 32 → s.getByte
      (BitVec.ofNat 64 i) = message.extractLsb' (8*i) 8) :
    ∃ final,
      Trace hash GroupedBalancedSignImage67.image s 108 123 1 2 final ∧
      final.pc = 0x10d8 ∧
      (∀ i : Fin 4,
        final.getMem (Signing.wordAddress 0x20060 i.val) =
          (Reference.randomizer hash secretKey message).extractLsb'
            (64*i.val) 64) ∧
      (∀ a : Word, a.toNat < 0x20060 → final.getMem a = s.getMem a) ∧
      (∀ a : Word, 0xfff700 ≤ a.toNat → final.getMem a = s.getMem a) := by
  obtain ⟨ready,prepared,readyPC,words,prepareFrame⟩ :=
    GroupedBalancedSignPrepare67.randomizer_prepare s pc
  obtain ⟨final,run,done,output,frame⟩ :=
    GroupedBalancedSignRandomizer67.randomizer_trace_frame hash ready readyPC
  have query := GroupedBalancedSignRandomizerQuery67.randomizer_query
    s ready secretKey message hsecretKey hmessage words
  refine ⟨final,prepared.trace.trans run,done,?_,?_,?_⟩
  · intro i
    rw [output i,query]
    rfl
  · intro a low
    have outside (base count : Nat) (lower : 0x20060 ≤ base)
        (bound : base + 8*count ≤ MEMORY_BYTES) (i : Fin count) :
        a ≠ Signing.wordAddress base i.val := by
      have ne := Signing.outside_copy_word a.toNat base count i.val
        a.isLt bound i.isLt (Or.inl (by omega))
      simpa using ne
    rw [frame a (outside 0x20060 4 (by decide) (by decide))
      (outside 0x80300 4 (by decide) (by decide))]
    exact prepareFrame a
      (outside 0x80440 1 (by decide) (by decide) 0)
      (outside 0x80448 1 (by decide) (by decide) 0)
      (outside 0x80000 12 (by decide) (by decide))
  · intro a high
    have outside (base count : Nat) (upper : base+8*count≤0xfff700)
        (bound : base + 8*count ≤ MEMORY_BYTES) (i : Fin count) :
        a ≠ Signing.wordAddress base i.val := by
      have ne := Signing.outside_copy_word a.toNat base count i.val
        a.isLt bound i.isLt (Or.inr (by omega))
      simpa using ne
    rw [frame a (outside 0x20060 4 (by decide) (by decide))
      (outside 0x80300 4 (by decide) (by decide))]
    exact prepareFrame a
      (outside 0x80440 1 (by decide) (by decide) 0)
      (outside 0x80448 1 (by decide) (by decide) 0)
      (outside 0x80000 12 (by decide) (by decide))

theorem loaded_randomizer (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    ∃ initial final,
      initialState submission .sign (secretKey,cache,message) = some initial ∧
      Trace hash GroupedBalancedSignImage67.image initial 108 123 1 2 final ∧
      final.pc = 0x10d8 ∧
      readBuffer final 0x20060 32 =
        Reference.randomizer hash secretKey message ∧
      (∀ a : Word, a.toNat < 0x20060 →
        final.getMem a = initial.getMem a) := by
  obtain ⟨initial,loaded,pc⟩ :=
    initialState_exists submission GroupedBalancedProgram67Byte.admissible
      .sign (secretKey,cache,message)
  obtain ⟨final,run,done,words,frame,_⟩ :=
    entry_randomizer_low_frame hash initial secretKey message pc
      (Loader.sign_secretKey submission
        (GroupedBalancedProgram67Byte.admissible.2 .sign) (by rfl)
        secretKey cache message initial loaded)
      (Loader.sign_message submission
        (GroupedBalancedProgram67Byte.admissible.2 .sign) (by rfl)
        secretKey cache message initial loaded)
  refine ⟨initial,final,loaded,run,done,?_,frame⟩
  apply Memory.readBuffer_of_bytes
  exact Signing.bytes_of_answer_words final 0x20060
    (Reference.randomizer hash secretKey message)
    (by decide) (by decide) words

#print axioms loaded_randomizer

end SigGolfCandidate.Hypertree.GroupedBalancedSignRandomizerLoaded67
