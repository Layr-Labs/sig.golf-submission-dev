import SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafQueryWords67
import SigGolfCandidate.Hypertree.SignRandomizer

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafLayout67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafCarry67. -/
section
/-! The Fast2Byte leaf prelude writes the query header and tree index while
preserving all 67 recovered WOTS endpoint words. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafLayout67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.Signing
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafPrelude67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafMemory67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastEndpointAccum67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafQueryWords67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

theorem prelude_header (s : MachineState) (base : Nat)
    (hbase : s.getMem 0x81000 = BitVec.ofNat 64 base) :
    (preludeState s).getMem 0x80000 =
      KeygenDomain.header 3 base 0 0 0 := by
  rw [prelude_mem]
  simp only [if_neg (by decide : (0x80000 : Word) ≠ 0x80018),
    if_neg (by decide : (0x80000 : Word) ≠ 0x80010),
    if_neg (by decide : (0x80000 : Word) ≠ 0x80008),
    if_pos (by decide : (0x80000 : Word) = 0x80000)]
  rw [hbase,KeygenDomain.shift_ofNat]
  simp [KeygenDomain.header,← BitVec.ofNat_add]

theorem prelude_index (s : MachineState) (leaf : Nat)
    (hindex : ∀ i : Fin 3,
      s.getMem (wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64) :
    ∀ i : Fin 3,
      (preludeState s).getMem (wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64 := by
  intro i
  fin_cases i
  · change (preludeState s).getMem 0x80008 = _
    rw [prelude_mem]
    simpa [wordAddress] using hindex 0
  · change (preludeState s).getMem 0x80010 = _
    rw [prelude_mem]
    simpa [wordAddress] using hindex 1
  · change (preludeState s).getMem 0x80018 = _
    rw [prelude_mem]
    simpa [wordAddress] using hindex 2

private theorem endpoint_ne (chain : Fin 67) (half : Fin 2)
    (n : Nat) (separate : n < 0x80020 ∨ 0x80500 ≤ n)
    (small : n < 2^64) :
    endpointAddress chain half ≠ BitVec.ofNat 64 n := by
  intro eq
  have h := congrArg BitVec.toNat eq
  rw [endpoint_address_nat] at h
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at h
  rcases separate with low | high <;> omega

theorem prelude_endpoint (s : MachineState)
    (chain : Fin 67) (half : Fin 2) :
    (preludeState s).getMem (endpointAddress chain half) =
      s.getMem (endpointAddress chain half) := by
  rw [prelude_mem]
  split_ifs with h1 h2 h3 h4 h5
  · exact False.elim ((endpoint_ne chain half 0x80018
      (Or.inl (by decide)) (by decide)) h1)
  · exact False.elim ((endpoint_ne chain half 0x80010
      (Or.inl (by decide)) (by decide)) h2)
  · exact False.elim ((endpoint_ne chain half 0x80008
      (Or.inl (by decide)) (by decide)) h3)
  · exact False.elim ((endpoint_ne chain half 0x80000
      (Or.inl (by decide)) (by decide)) h4)
  · exact False.elim ((endpoint_ne chain half 0x81048
      (Or.inr (by decide)) (by decide)) h5)
  · rfl

theorem prelude_words (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (done : GroupedBalancedByteFastChainEndpoints67.StrongDone hash s
      base leaf start message values)
    (hbase : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (hindex : ∀ i : Fin 3,
      s.getMem (wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64) :
    ∀ i : Fin 138,
      (preludeState s).getMem (wordAddress 0x80000 i.val) =
        inputWord (KeygenDomain.header 3 base 0 0 0) leaf
          (expectedEndpoint hash base leaf message values) i := by
  intro i
  by_cases first : i.val = 0
  · have eq : i = 0 := Fin.ext first
    subst i
    simpa [inputWord,wordAddress] using prelude_header s base hbase
  by_cases index : i.val < 4
  · have pi := prelude_index s leaf hindex
    have cases : i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
    rcases cases with h1 | h2 | h3
    · have eq : i = (1 : Fin 138) := Fin.ext h1
      subst i
      simpa [inputWord,wordAddress] using pi 0
    · have eq : i = (2 : Fin 138) := Fin.ext h2
      subst i
      simpa [inputWord,wordAddress] using pi 1
    · have eq : i = (3 : Fin 138) := Fin.ext h3
      subst i
      simpa [inputWord,wordAddress] using pi 2
  · let c : Fin 67 := ⟨(i.val-4)/2,by have := i.isLt; omega⟩
    let half : Fin 2 := ⟨(i.val-4)%2,Nat.mod_lt _ (by decide)⟩
    have earlier : c.val < 67 := c.isLt
    have addr : wordAddress 0x80000 i.val = endpointAddress c half := by
      apply BitVec.eq_of_toNat_eq
      rw [endpoint_address_nat]
      simp only [wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80000+8*i.val < 2^64)]
      dsimp [c,half]
      omega
    rw [addr,prelude_endpoint]
    have endpoint := done.2 c c.isLt half
    change s.getMem (endpointAddress c half) = _
    simpa only [inputWord,first,index,↓reduceIte,c,half] using endpoint

theorem prelude_hash_eq (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (done : GroupedBalancedByteFastChainEndpoints67.StrongDone hash s
      base leaf start message values)
    (hbase : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (hindex : ∀ i : Fin 3,
      s.getMem (wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64) :
    Reference.truncate (hash (hashInput (preludeState s))) =
      GroupedBalancedUpperTree67.compressLeaf hash base leaf
        (expectedEndpoint hash base leaf message values) := by
  have fields := prelude_fields s done.1.pc
  exact leaf_hash_eq hash (preludeState s) base leaf
    (expectedEndpoint hash base leaf message values)
    fields.source fields.bits
    (prelude_words hash s base leaf start message values done hbase hindex)

theorem leaf_result_words (hash : Hash) (s : MachineState)
    (base leaf start : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (done : GroupedBalancedByteFastChainEndpoints67.StrongDone hash s
      base leaf start message values)
    (hbase : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (hindex : ∀ i : Fin 3,
      s.getMem (wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64) :
    ∀ half : Fin 2,
      (GroupedBalancedByteFastLeaf67.leafState hash s).getMem
        (wordAddress 0x80500 half.val) =
      (GroupedBalancedUpperTree67.compressLeaf hash base leaf
        (expectedEndpoint hash base leaf message values)).extractLsb'
          (64*half.val) 64 := by
  let prepared := preludeState s
  let hashed := writeHash prepared (hash (hashInput prepared))
  have fields := prelude_fields s done.1.pc
  have hashedPC := GroupedBalancedByteFastLeafQuery67.hash_pc hash
    prepared fields
  have answer := prelude_hash_eq hash s base leaf start message values
    done hbase hindex
  intro half
  fin_cases half
  · change (GroupedBalancedByteFastLeafCopy67.copyState hashed).getMem
      0x80500 = _
    rw [GroupedBalancedByteFastLeafCopy67.copy_mem hashed hashedPC]
    simp only [if_neg (by decide : (0x80500 : Word) ≠ 0x80508),
      ↓reduceIte]
    change (writeHash prepared (hash (hashInput prepared))).getMem
      (wordAddress 0x80300 (0 : Fin 4).val) = _
    rw [Signing.hash_answer_word prepared (hash (hashInput prepared))
      fields.destination (0 : Fin 4)]
    rw [← answer]
    ext j hj
    simp (disch := omega) [Reference.truncate,prepared]
  · change (GroupedBalancedByteFastLeafCopy67.copyState hashed).getMem
      0x80508 = _
    rw [GroupedBalancedByteFastLeafCopy67.copy_mem hashed hashedPC]
    simp only [↓reduceIte]
    change (writeHash prepared (hash (hashInput prepared))).getMem
      (wordAddress 0x80300 (1 : Fin 4).val) = _
    rw [Signing.hash_answer_word prepared (hash (hashInput prepared))
      fields.destination (1 : Fin 4)]
    rw [← answer]
    ext j hj
    simp (disch := omega) [Reference.truncate,prepared]

#print axioms prelude_endpoint
#print axioms prelude_words
#print axioms leaf_result_words

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafLayout67

end

/-! Memory and pointer carry from upper WOTS endpoints through the leaf hash. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafCarry67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafPrelude67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafMemory67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def OutsideLeaf (a : Word) : Prop :=
  a ≠ 0x81048 ∧
  (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80000 i.val) ∧
  (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) ∧
  (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80500 i.val)

theorem leaf_mem (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1684) (a : Word) (outside : OutsideLeaf a) :
    (GroupedBalancedByteFastLeaf67.leafState hash s).getMem a = s.getMem a := by
  let prepared := preludeState s
  let hashed := writeHash prepared (hash (hashInput prepared))
  have fields := prelude_fields s pc
  have hashPC := GroupedBalancedByteFastLeafQuery67.hash_pc hash prepared fields
  change (GroupedBalancedByteFastLeafCopy67.copyState hashed).getMem a = _
  rw [GroupedBalancedByteFastLeafCopy67.copy_mem hashed hashPC a]
  have n0 : a ≠ 0x80500 := outside.2.2.2 0
  have n1 : a ≠ 0x80508 := outside.2.2.2 1
  simp only [if_neg n1,if_neg n0]
  have answerFrame := Signing.hash_answer_frame prepared
    (hash (hashInput prepared)) fields.destination a outside.2.2.1
  change hashed.getMem a = _ at answerFrame
  rw [answerFrame]
  rw [prelude_mem]
  have q0 : a ≠ 0x80000 := outside.2.1 0
  have q1 : a ≠ 0x80008 := outside.2.1 1
  have q2 : a ≠ 0x80010 := outside.2.1 2
  have q3 : a ≠ 0x80018 := outside.2.1 3
  rw [if_neg q3,if_neg q2,if_neg q1,if_neg q0,if_neg outside.1]

theorem leaf_pointer (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1684) :
    (GroupedBalancedByteFastLeaf67.leafState hash s).getMem 0x81048 =
      s.getReg .x22 := by
  let prepared := preludeState s
  let hashed := writeHash prepared (hash (hashInput prepared))
  have fields := prelude_fields s pc
  have hashPC := GroupedBalancedByteFastLeafQuery67.hash_pc hash prepared fields
  change (GroupedBalancedByteFastLeafCopy67.copyState hashed).getMem 0x81048 = _
  rw [GroupedBalancedByteFastLeafCopy67.copy_mem hashed hashPC 0x81048]
  simp only [if_neg (by decide : (0x81048 : Word) ≠ 0x80508),
    if_neg (by decide : (0x81048 : Word) ≠ 0x80500)]
  have answerFrame := Signing.hash_answer_frame prepared
    (hash (hashInput prepared)) fields.destination 0x81048
    (by intro i; fin_cases i <;> decide)
  change hashed.getMem 0x81048 = _ at answerFrame
  rw [answerFrame,prelude_mem]
  simp

theorem leaf_x6 (hash : Hash) (s : MachineState) :
    (GroupedBalancedByteFastLeaf67.leafState hash s).getReg .x6 = 0 := by
  change (execInstrBr _ (.ADDI .x6 .x0 0)).getReg .x6 = 0
  simp [execInstrBr,signExtend12,MachineState.getReg_setReg_eq]

private theorem outside_addr_low (a : Word) (low : a.toNat < 0x80000)
    (base n : Nat) (high : 0x80000 ≤ base)
    (small : base+8*n < 2^64) :
    ∀ i : Fin n, a ≠ Signing.wordAddress base i.val := by
  intro i eq
  have h := congrArg BitVec.toNat eq
  simp only [Signing.wordAddress,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : base+8*i.val < 2^64)] at h
  omega

private theorem outside_addr_high (a : Word) (high : 0x81000 ≤ a.toNat)
    (base n : Nat) (small : base+8*n ≤ 0x81000) :
    ∀ i : Fin n, a ≠ Signing.wordAddress base i.val := by
  intro i eq
  have h := congrArg BitVec.toNat eq
  simp only [Signing.wordAddress,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : base+8*i.val < 2^64)] at h
  omega

theorem outside_high (a : Word) (high : 0x81000 ≤ a.toNat)
    (notPtr : a ≠ 0x81048) : OutsideLeaf a := by
  exact ⟨notPtr,
    outside_addr_high a high 0x80000 4 (by decide),
    outside_addr_high a high 0x80300 4 (by decide),
    outside_addr_high a high 0x80500 2 (by decide)⟩

theorem outside_low (a : Word) (low : a.toNat < 0x80000) :
    OutsideLeaf a := by
  refine ⟨?_,outside_addr_low a low 0x80000 4 (by decide) (by decide),
    outside_addr_low a low 0x80300 4 (by decide) (by decide),
    outside_addr_low a low 0x80500 2 (by decide) (by decide)⟩
  · intro eq
    have h := congrArg BitVec.toNat eq
    have hc : (0x81048 : Word).toNat = 0x81048 := by decide
    rw [hc] at h
    omega

#print axioms leaf_mem
#print axioms leaf_pointer
#print axioms leaf_x6

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafCarry67
