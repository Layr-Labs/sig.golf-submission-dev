import SigGolfCandidate.Hypertree.KeygenLeafQuery

namespace SigGolfCandidate.Hypertree.VerifyLeafQueryDirect
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096

theorem query_eq (s : MachineState) (head : Word) (tree : Nat)
    (values : Reference.Chain → Reference.Digest)
    (source : s.getReg .x10 = 0x807e0) (bits : s.getReg .x11 = 6144)
    (words : ∀ i : Fin 96, s.getMem (Signing.wordAddress 0x807e0 i.val) =
      KeygenLeaf.inputWord head tree values i) :
    hashInput s = Reference.packed (KeygenLeaf.payload head tree values) := by
  apply Serialization.hashInput_of_list s 0x807e0 (KeygenLeaf.payload head tree values)
  · exact source
  · rw [bits,KeygenLeaf.payload_length]; rfl
  · intro i hi
    have bound : i < 768 := by simpa using hi
    rw [Signing.getByte_word s 0x807e0 i (by decide) (by omega),words ⟨i/8,by omega⟩]
    exact KeygenLeaf.payload_byte head tree values ⟨i,bound⟩

theorem answer_words (hash : Hash) (s : MachineState) (level tree : Nat)
    (side : Bool) (values : Reference.Chain → Reference.Digest)
    (source : s.getReg .x10 = 0x807e0) (bits : s.getReg .x11 = 6144)
    (destination : s.getReg .x12 = 0x80300)
    (words : ∀ i : Fin 96, s.getMem (Signing.wordAddress 0x807e0 i.val) =
      KeygenLeaf.inputWord (BitVec.ofNat 64 (3 + level*2^8 + Reference.sideNumber side*2^16)) tree values i) :
    ∀ i : Fin 2, (writeHash s (hash (hashInput s))).getMem (Signing.wordAddress 0x80300 i.val) =
      (Reference.compressLeaf hash level tree side values).extractLsb' (64*i.val) 64 := by
  intro i
  rw [Signing.hash_answer_word s (hash (hashInput s)) destination ⟨i.val,by have := i.isLt; omega⟩]
  have query := query_eq s _ tree values source bits words
  have answer : Reference.compressLeaf hash level tree side values = Reference.truncate (hash (hashInput s)) := by
    rw [query]
    simp only [Reference.compressLeaf,Reference.query,KeygenLeaf.payload]
    have arithmetic : 3 + level*2^8 + Reference.sideNumber side*2^16 + 0*2^24 + 0*2^32 =
        3 + level*2^8 + Reference.sideNumber side*2^16 := by simp only [Nat.zero_mul,Nat.add_zero]
    rw [arithmetic,KeygenLeaf.endpoints_eq]
  rw [answer]
  change (hash (hashInput s)).extractLsb' (64*i.val) 64 =
    ((hash (hashInput s)).extractLsb' 0 128).extractLsb' (64*i.val) 64
  fin_cases i <;> ext j hj <;> simp (disch := omega)

theorem hash_trace (image : Image) (hash : Hash) (s : MachineState)
    (code : fetch image s = some (.base .ECALL)) (service : s.getReg .x5 = 1)
    (source : s.getReg .x10 = 0x807e0) (bits : s.getReg .x11 = 6144)
    (destination : s.getReg .x12 = 0x80300) :
    Trace hash image s 1 96 1 12 (writeHash s (hash (hashInput s))) := by
  have valid : hashArgumentsValid s = true := by
    simp [hashArgumentsValid,source,bits,destination,accessValid,rangeValid,MEMORY_BYTES]
  have len : (hashInput s).1 = 6144 := by simp [hashInput,bits]
  simpa [len,compressions] using Trace.hash s _ 0 0 0 0 code service valid (Trace.refl _)

/-- info: 'SigGolfCandidate.Hypertree.VerifyLeafQueryDirect.answer_words' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms answer_words

end SigGolfCandidate.Hypertree.VerifyLeafQueryDirect
