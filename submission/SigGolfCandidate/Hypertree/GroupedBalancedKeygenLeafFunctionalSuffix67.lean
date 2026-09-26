import SigGolfCandidate.Hypertree.GroupedBalancedUpperTree67
import SigGolfCandidate.Hypertree.KeygenLeafQuery
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenOneLeaf67
import SigGolfCandidate.TraceDeterminism

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalQuery67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalSuffix67. -/
section
/-! Serialization of the direct67 WOTS endpoints into the keygen H3 query. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalQuery67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

abbrev Chain := GroupedBalancedChecksum67.Chain

def endpointBytes (values : Chain → Reference.Digest) : List Byte :=
  List.ofFn (fun i : Fin (67*16) =>
    (values ⟨i.val/16,by have := i.isLt; omega⟩).extractLsb'
      (8*(i.val%16)) 8)

theorem endpoints_eq (values : Chain → Reference.Digest) :
    ((List.ofFn values).flatMap fun value => bytes value) =
      endpointBytes values := by
  unfold endpointBytes
  rw [List.ofFn_mul (m:=67) (n:=16)]
  simp only [List.flatMap, List.map_ofFn, KeygenLeaf.bytes_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have div : (i.val*16+j.val)/16 = i.val := by omega
  have mod : (i.val*16+j.val)%16 = j.val := by omega
  simp only [div,mod]

def payload (head : Word) (tree : Nat)
    (values : Chain → Reference.Digest) : List Byte :=
  bytes (n:=8) head ++ bytes (n:=24) (BitVec.ofNat 192 tree) ++
    endpointBytes values

@[simp] theorem payload_length (head : Word) (tree : Nat)
    (values : Chain → Reference.Digest) :
    (payload head tree values).length = 1104 := by
  simp only [payload,List.length_append,bytes,List.length_map,
    List.length_range,endpointBytes,List.length_ofFn]

def inputWord (head : Word) (tree : Nat)
    (values : Chain → Reference.Digest) (i : Fin 138) : Word :=
  if i.val=0 then head else if i.val<4 then
    (BitVec.ofNat 192 tree).extractLsb' (64*(i.val-1)) 64 else
    (values ⟨(i.val-4)/2,by have := i.isLt; omega⟩).extractLsb'
      (64*((i.val-4)%2)) 64

theorem payload_byte (head : Word) (tree : Nat)
    (values : Chain → Reference.Digest) (i : Fin 1104) :
    extractByte (inputWord head tree values
      ⟨i.val/8,by have := i.isLt; omega⟩) (i.val%8) =
      (payload head tree values)[i.val]'(by simp) := by
  by_cases first : i.val < 32
  · obtain ⟨i,hi⟩ := i
    dsimp at first
    interval_cases i <;> simp [inputWord,payload,bytes]
    all_goals
      ext j hj
      interval_cases j <;>
        simp [extractByte,← BitVec.getLsbD_eq_getElem,
          BitVec.getLsbD_ofNat]
  · have big : 32 ≤ i.val := by omega
    have q0 : ¬ i.val/8=0 := by omega
    have q4 : ¬ i.val/8<4 := by omega
    have offset : i.val-32 < 1072 := by have := i.isLt; omega
    have div : (i.val/8-4)/2 = (i.val-32)/16 := by omega
    have shift : 64*((i.val/8-4)%2) + (i.val%8*8) =
        8*((i.val-32)%16) := by omega
    simp only [inputWord,q0,q4,↓reduceIte,payload,
      List.getElem_append,bytes,List.length_map,List.length_range,
      List.length_append]
    simp only [show ¬ i.val<8+24 from by omega,↓reduceDIte,
      endpointBytes,List.getElem_ofFn]
    simp only [div]
    ext j hj
    have low : i.val%8*8+j < 64 := by omega
    simp [extractByte,low,← Nat.add_assoc,shift]

theorem query_eq (s : MachineState) (head : Word) (tree : Nat)
    (values : Chain → Reference.Digest)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 8832)
    (words : ∀ i : Fin 138,
      s.getMem (Signing.wordAddress 0x80000 i.val) =
        inputWord head tree values i) :
    hashInput s = Reference.packed (payload head tree values) := by
  apply Serialization.hashInput_of_list s 0x80000
    (payload head tree values)
  · exact source
  · rw [bits,payload_length]
    rfl
  · intro i hi
    have bound : i < 1104 := by simpa using hi
    rw [Signing.getByte_word s 0x80000 i (by decide) (by omega),
      words ⟨i/8,by omega⟩]
    exact payload_byte head tree values ⟨i,bound⟩

theorem answer_words (hash : Hash) (s : MachineState)
    (base leaf : Nat) (values : Chain → Reference.Digest)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 8832)
    (destination : s.getReg .x12 = 0x80300)
    (words : ∀ i : Fin 138,
      s.getMem (Signing.wordAddress 0x80000 i.val) =
        inputWord (KeygenDomain.header 3 base 0 0 0) leaf values i) :
    ∀ i : Fin 2,
      (writeHash s (hash (hashInput s))).getMem
        (Signing.wordAddress 0x80300 i.val) =
        (GroupedBalancedUpperTree67.compressLeaf hash base leaf values).extractLsb'
          (64*i.val) 64 := by
  intro i
  rw [Signing.hash_answer_word s (hash (hashInput s)) destination
    ⟨i.val,by have := i.isLt; omega⟩]
  have query := query_eq s _ leaf values source bits words
  have answer : GroupedBalancedUpperTree67.compressLeaf hash base leaf values =
      Reference.truncate (hash (hashInput s)) := by
    rw [query]
    simp only [GroupedBalancedUpperTree67.compressLeaf,Reference.query,
      payload,KeygenDomain.header]
    have arithmetic :
        3 + base*2^8 + 0*2^16 + 0*2^24 + 0*2^32 =
          3 + base*2^8 := by omega
    rw [arithmetic,endpoints_eq]
  rw [answer]
  change (hash (hashInput s)).extractLsb' (64*i.val) 64 =
    ((hash (hashInput s)).extractLsb' 0 128).extractLsb'
      (64*i.val) 64
  fin_cases i <;> ext j hj <;> simp (disch := omega)

#print axioms query_eq
#print axioms answer_words

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalQuery67

end

/-! The direct67 keygen H3 suffix, conditional on the endpoint table. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalSuffix67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenLeafFunctionalQuery67
set_option maxRecDepth 16384
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedKeygenImage67.image

theorem leaf_header_word (s : MachineState) :
    (GroupedBalancedKeygenLeafHeader67.headerState s).getMem 0x80000 =
      (3 : Word) + (s.getMem 0x81000 <<< 8) := by
  simp [GroupedBalancedKeygenLeafHeader67.headerState, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem leaf_tree_word (s : MachineState) (i : Fin 3) :
    (GroupedBalancedKeygenLeafHeader67.headerState s).getMem
      (Signing.wordAddress 0x80008 i.val) =
        s.getMem (Signing.wordAddress 0x81008 i.val) := by
  fin_cases i <;>
    simp [GroupedBalancedKeygenLeafHeader67.headerState,
      Signing.wordAddress, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem leaf_tail_frame (s : MachineState) (a : Word)
    (lower : 0x80020 ≤ a.toNat) :
    (GroupedBalancedKeygenLeafHeader67.headerState s).getMem a =
      s.getMem a := by
  have h0 : a ≠ 0x80000#64 := by
    intro eq
    rw [eq] at lower
    norm_num at lower
  have h8 : a ≠ 0x80008#64 := by
    intro eq
    rw [eq] at lower
    norm_num at lower
  have h10 : a ≠ 0x80010#64 := by
    intro eq
    rw [eq] at lower
    norm_num at lower
  have h18 : a ≠ 0x80018#64 := by
    intro eq
    rw [eq] at lower
    norm_num at lower
  simp [GroupedBalancedKeygenLeafHeader67.headerState, execInstrBr,
    signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,h0,h8,h10,h18]

theorem leaf_header_eq (base : Nat) :
    (3 : Word) + (BitVec.ofNat 64 base <<< 8) =
      KeygenDomain.header 3 base 0 0 0 := by
  simp [KeygenDomain.header,KeygenDomain.shift_ofNat,
    BitVec.ofNat_add,BitVec.ofNat_mul]

theorem header_words (s : MachineState)
    (base tree : Nat) (values : Chain → Reference.Digest)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (treeWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (endpoints : ∀ i : Fin 134,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        (values ⟨i.val/2,by have := i.isLt; omega⟩).extractLsb'
          (64*(i.val%2)) 64) :
    ∀ i : Fin 138,
      (GroupedBalancedKeygenLeafHeader67.headerState s).getMem
        (Signing.wordAddress 0x80000 i.val) =
          inputWord (KeygenDomain.header 3 base 0 0 0) tree values i := by
  intro i
  by_cases zero : i.val = 0
  · have eqi : i = ⟨0,by decide⟩ := Fin.eq_of_val_eq zero
    subst i
    change (GroupedBalancedKeygenLeafHeader67.headerState s).getMem 0x80000 =
      KeygenDomain.header 3 base 0 0 0
    rw [leaf_header_word,level,leaf_header_eq]
  by_cases head : i.val < 4
  · have range : i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
    rcases range with h | h | h
    · have eqi : i = ⟨1,by decide⟩ := Fin.eq_of_val_eq h
      subst i
      simpa [inputWord,Signing.wordAddress] using
        (leaf_tree_word s ⟨0,by decide⟩).trans (treeWords ⟨0,by decide⟩)
    · have eqi : i = ⟨2,by decide⟩ := Fin.eq_of_val_eq h
      subst i
      simpa [inputWord,Signing.wordAddress] using
        (leaf_tree_word s ⟨1,by decide⟩).trans (treeWords ⟨1,by decide⟩)
    · have eqi : i = ⟨3,by decide⟩ := Fin.eq_of_val_eq h
      subst i
      simpa [inputWord,Signing.wordAddress] using
        (leaf_tree_word s ⟨2,by decide⟩).trans (treeWords ⟨2,by decide⟩)
  · have offset : 0x80020 ≤ (Signing.wordAddress 0x80000 i.val).toNat := by
      simp only [Signing.wordAddress,BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by have := i.isLt; omega)]
      omega
    rw [leaf_tail_frame s _ offset]
    have address : Signing.wordAddress 0x80000 i.val =
        Signing.wordAddress 0x80020 (i.val-4) := by
      change BitVec.ofNat 64 (0x80000 + 8*i.val) =
        BitVec.ofNat 64 (0x80020 + 8*(i.val-4))
      congr 1
      omega
    rw [address]
    have n : i.val - 4 < 134 := by have := i.isLt; omega
    rw [endpoints ⟨i.val-4,n⟩]
    simp [inputWord,zero,head]

theorem copy_header_hash_values (hash : Hash) (s : MachineState)
    (base tree : Nat) (values : Chain → Reference.Digest)
    (pc : s.pc = 0x131c)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (treeWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (endpoints : ∀ i : Fin 134,
      s.getMem (Signing.wordAddress 0x80800 i.val) =
        (values ⟨i.val/2,by have := i.isLt; omega⟩).extractLsb'
          (64*(i.val%2)) 64) :
    ∃ hashed,
      Trace hash image s 844 987 1 18 hashed ∧
      hashed.pc = 0x13d4 ∧
      (∀ i : Fin 2,
        hashed.getMem (Signing.wordAddress 0x80300 i.val) =
          (GroupedBalancedUpperTree67.compressLeaf hash base tree values).extractLsb'
            (64*i.val) 64) := by
  obtain ⟨copied,first,copiedPC,copiedWords,copyFrame⟩ :=
    GroupedBalancedKeygenLeafCopy67.copy_leaf_words s pc
  have copiedHigh (a : Word) (high : 0x81000 ≤ a.toNat) :
      copied.getMem a = s.getMem a := by
    apply copyFrame a
    intro i hi same
    have hn := congrArg BitVec.toNat same
    simp only [Signing.wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80020+8*i < 2^64)] at hn
    omega
  have copiedLevel : copied.getMem 0x81000 = BitVec.ofNat 64 base := by
    rw [copiedHigh 0x81000 (by decide)]
    exact level
  have copiedTree : ∀ i : Fin 3,
      copied.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    rw [copiedHigh _ (by
      simp [Signing.wordAddress,BitVec.toNat_ofNat]
      have := i.isLt
      omega)]
    exact treeWords i
  have copiedEndpoints : ∀ i : Fin 134,
      copied.getMem (Signing.wordAddress 0x80020 i.val) =
        (values ⟨i.val/2,by have := i.isLt; omega⟩).extractLsb'
          (64*(i.val%2)) 64 := by
    intro i
    rw [copiedWords i.val i.isLt]
    exact endpoints i
  let ready := GroupedBalancedKeygenLeafHeader67.headerState copied
  have second : Trace hash image copied 34 34 0 0 ready :=
    (GroupedBalancedKeygenLeafHeader67.header_steps copied copiedPC).trace
  have readyPC := GroupedBalancedKeygenLeafHeader67.header_pc copied copiedPC
  have regs := GroupedBalancedKeygenLeafHeader67.header_regs copied
  have words := header_words copied base tree values
    copiedLevel copiedTree copiedEndpoints
  let hashed := writeHash ready (hash (hashInput ready))
  have third : Trace hash image ready 1 144 1 18 hashed :=
    GroupedBalancedKeygenLeafHash67.hash_trace hash ready readyPC regs
  refine ⟨hashed,?_,?_,?_⟩
  · have full := (first.trace (hash := hash)).trans second |>.trans third
    simpa only [Nat.reduceAdd] using full
  · change ready.pc + 4 = 0x13d4
    rw [readyPC]
    decide
  · exact answer_words hash ready base tree values
      regs.2.1 regs.2.2.1 regs.2.2.2 words

theorem store_digest_words (s : MachineState) (n : Nat)
    (bound : n < 16)
    (counter : s.getMem 0x81008#64 = BitVec.ofNat 64 n)
    (value : Reference.Digest)
    (answer : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80300 i.val) =
        value.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (GroupedBalancedKeygenLeafStore67.storeState s).getMem
        (Signing.wordAddress 0x82000 (2*n+i.val)) =
          value.extractLsb' (64*i.val) 64 := by
  have base : (s.getMem 0x81008#64 <<< 4) + 0x82000#64 =
      Signing.wordAddress 0x82000 (2*n) := by
    rw [counter,KeygenDomain.shift_ofNat]
    change BitVec.ofNat 64 (n*16) + BitVec.ofNat 64 0x82000 =
      BitVec.ofNat 64 (0x82000 + 8*(2*n))
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  have next : (s.getMem 0x81008#64 <<< 4) + 0x82000#64 + 8#64 =
      Signing.wordAddress 0x82000 (2*n+1) := by
    rw [base]
    change BitVec.ofNat 64 (0x82000 + 8*(2*n)) + 8 =
      BitVec.ofNat 64 (0x82000 + 8*(2*n+1))
    change BitVec.ofNat 64 (0x82000 + 8*(2*n)) +
      BitVec.ofNat 64 8 =
      BitVec.ofNat 64 (0x82000 + 8*(2*n+1))
    rw [← BitVec.ofNat_add]
    congr 1
  intro i
  fin_cases i
  · change (GroupedBalancedKeygenLeafStore67.storeState s).getMem
        (Signing.wordAddress 0x82000 (2*n)) = value.extractLsb' 0 64
    have distinct :
        Signing.wordAddress 0x82000 (2*n) ≠ 0x81008#64 := by
      intro eq
      have h := congrArg BitVec.toNat eq
      simp [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x82000+8*(2*n) < 2^64)] at h
      omega
    rw [GroupedBalancedKeygenLeafStore67.store_mem,if_neg distinct]
    have first : Signing.wordAddress 0x82000 (2*n) =
        (s.getMem 0x81008#64 <<< 4) + 0x82000#64 := base.symm
    rw [first]
    have ne : (s.getMem 0x81008#64 <<< 4) + 0x82000#64 ≠
        (s.getMem 0x81008#64 <<< 4) + 0x82000#64 + 8#64 := by
      rw [next,base]
      intro eq
      have h := congrArg BitVec.toNat eq
      simp [Signing.wordAddress,BitVec.toNat_ofNat] at h
      omega
    rw [if_neg ne,if_pos rfl]
    simpa [Signing.wordAddress] using answer ⟨0,by decide⟩
  · change (GroupedBalancedKeygenLeafStore67.storeState s).getMem
        (Signing.wordAddress 0x82000 (2*n+1)) = value.extractLsb' 64 64
    have distinct :
        Signing.wordAddress 0x82000 (2*n+1) ≠ 0x81008#64 := by
      intro eq
      have h := congrArg BitVec.toNat eq
      simp [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x82000+8*(2*n+1) < 2^64)] at h
      omega
    rw [GroupedBalancedKeygenLeafStore67.store_mem,if_neg distinct]
    have second : Signing.wordAddress 0x82000 (2*n+1) =
        (s.getMem 0x81008#64 <<< 4) + 0x82000#64 + 8#64 := next.symm
    rw [second,if_pos rfl]
    simpa [Signing.wordAddress] using answer ⟨1,by decide⟩

theorem leaf_suffix_values (hash : Hash) (s : MachineState)
    (base tree n : Nat) (values : Chain → Reference.Digest)
    (pc : s.pc = 0x131c) (bound : n < 16)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (counter : s.getMem 0x81008#64 = BitVec.ofNat 64 n)
    (treeWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (endpoints : ∀ i : Fin 134,
      s.getMem (Signing.wordAddress 0x80800 i.val) =
        (values ⟨i.val/2,by have := i.isLt; omega⟩).extractLsb'
          (64*(i.val%2)) 64) :
    ∃ final,
      Trace hash image s 865 1008 1 18 final ∧
      final.pc = (if n = 15 then 0x1428 else 0x1040) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x82000 (2*n+i.val)) =
          (GroupedBalancedUpperTree67.compressLeaf hash base tree values).extractLsb'
            (64*i.val) 64) := by
  obtain ⟨hashed,first,hashedPC,answer⟩ :=
    copy_header_hash_values hash s base tree values pc level treeWords endpoints
  obtain ⟨other,otherTrace,_,otherHigh⟩ :=
    GroupedBalancedKeygenLeafHash67.copy_header_hash hash s pc
  have same : hashed = other := Trace.deterministic first otherTrace
  have high (a : Word) (lower : 0x81000 ≤ a.toNat) :
      hashed.getMem a = s.getMem a := by
    rw [same]
    exact otherHigh a lower
  have hashedCounter : hashed.getMem 0x81008#64 = BitVec.ofNat 64 n := by
    rw [high 0x81008#64 (by decide)]
    exact counter
  obtain ⟨safe,safeNext⟩ :=
    GroupedBalancedKeygenLeafStore67.store_accesses hashed n bound hashedCounter
  let final := GroupedBalancedKeygenLeafStore67.storeState hashed
  have second : Trace hash image hashed 21 21 0 0 final :=
    (GroupedBalancedKeygenLeafStore67.store_steps hashed hashedPC safe safeNext).trace
  refine ⟨final,?_,?_,?_⟩
  · simpa only [Nat.reduceAdd] using first.trans second
  · rw [GroupedBalancedKeygenLeafStore67.store_pc hashed hashedPC,
      hashedCounter]
    have succ : (BitVec.ofNat 64 n : Word) + 1 =
        BitVec.ofNat 64 (n+1) := by simp [BitVec.ofNat_add]
    rw [succ]
    have eq : ((BitVec.ofNat 64 (n+1) : Word) = 16) ↔ n = 15 := by
      interval_cases n <;> decide
    simp only [eq]
  · exact store_digest_words hashed n bound hashedCounter
      (GroupedBalancedUpperTree67.compressLeaf hash base tree values) answer

theorem leaf_suffix_root (hash : Hash) (secretKey : SecretKey)
    (s : MachineState) (base n : Nat)
    (pc : s.pc = 0x131c) (bound : n < 16)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (counter : s.getMem 0x81008#64 = BitVec.ofNat 64 n)
    (treeWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 n).extractLsb' (64*i.val) 64)
    (endpoints : ∀ i : Fin 134,
      s.getMem (Signing.wordAddress 0x80800 i.val) =
        (GroupedBalancedUpperTree67.endpoint hash secretKey base n
          ⟨i.val/2,by have := i.isLt; omega⟩).extractLsb'
          (64*(i.val%2)) 64) :
    ∃ final,
      Trace hash image s 865 1008 1 18 final ∧
      final.pc = (if n = 15 then 0x1428 else 0x1040) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x82000 (2*n+i.val)) =
          (GroupedBalancedUpperTree67.leafRoot hash secretKey base n).extractLsb'
            (64*i.val) 64) := by
  simpa only [GroupedBalancedUpperTree67.leafRoot] using
    leaf_suffix_values hash s base n n
      (GroupedBalancedUpperTree67.endpoint hash secretKey base n)
      pc bound level counter treeWords endpoints

#print axioms leaf_header_word
#print axioms leaf_tree_word
#print axioms header_words
#print axioms copy_header_hash_values
#print axioms store_digest_words
#print axioms leaf_suffix_values
#print axioms leaf_suffix_root

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalSuffix67
