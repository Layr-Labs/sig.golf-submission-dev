import SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalEndpoint67


/-! The WOTS header and tree words prepared by the actual direct67 keygen. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalPrepared67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev wots := GroupedBalancedKeygenWotsPrepared67.wotsState

theorem header_eq (base chain : Nat) :
    (2 : Word) + (BitVec.ofNat 64 base <<< 8) +
      (BitVec.ofNat 64 chain <<< 24) =
        KeygenDomain.header 2 base 0 chain 0 := by
  simp [KeygenDomain.header,KeygenDomain.shift_ofNat,
    BitVec.ofNat_add,BitVec.ofNat_mul,Nat.add_assoc,BitVec.add_assoc]

theorem prepared_header (s : MachineState) (base chain : Nat)
    (pc : s.pc = 0x11d8)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 chain) :
    (wots s).getMem 0x80000 =
      KeygenDomain.header 2 base 0 chain 0 := by
  rw [GroupedBalancedKeygenWotsPrepared67.wots_header s pc,
    level,counter]
  exact header_eq base chain

theorem prepared_counter (s : MachineState) :
    (wots s).getMem 0x81030 = s.getMem 0x81030 := by
  simp [wots,GroupedBalancedKeygenWotsPrepared67.wotsState,
    GroupedBalancedKeygenWotsPrepared67.all_mem,
    GroupedBalancedKeygenWotsHeader67.header_mem_other,
    GroupedBalancedKeygenWotsHeader67.reset_mem_other]

theorem prepared_seed (s : MachineState) (i : Fin 2) :
    (wots s).getMem (Signing.wordAddress 0x80020 i.val) =
      s.getMem (Signing.wordAddress 0x80020 i.val) := by
  fin_cases i <;>
    simp [wots,GroupedBalancedKeygenWotsPrepared67.wotsState,
      GroupedBalancedKeygenWotsPrepared67.all_mem,
      GroupedBalancedKeygenWotsHeader67.header_mem_other,
      GroupedBalancedKeygenWotsHeader67.reset_mem_other,
      Signing.wordAddress]

theorem prepared_tree (s : MachineState) (i : Fin 3) :
    (wots s).getMem (Signing.wordAddress 0x80008 i.val) =
      s.getMem (Signing.wordAddress 0x81008 i.val) :=
  GroupedBalancedKeygenWotsPrepared67.wots_index s i

#print axioms prepared_header
#print axioms prepared_counter
#print axioms prepared_seed
#print axioms prepared_tree

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalPrepared67


/-! Direct67 keygen's selected WOTS chain, from the prepared seed to its endpoint slot. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalChain67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenLeafFunctionalPrepared67
open GroupedBalancedKeygenLeafFunctionalSelector67
open GroupedBalancedKeygenLeafFunctionalEndpoint67
open GroupedBalancedKeygenEndpointCopy67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image
private abbrev wots := GroupedBalancedKeygenWotsPrepared67.wotsState

private theorem word_ne_of_lt (n limit : Nat)
    (small : n < limit) (limitBound : limit < 2^64) :
    (BitVec.ofNat 64 n : Word) ≠ BitVec.ofNat 64 limit := by
  intro eq
  have h := congrArg BitVec.toNat eq
  simp [BitVec.toNat_ofNat] at h
  omega

theorem regular_from_entry_value (hash : Hash) (s : MachineState)
    (base tree n : Nat) (value : Reference.Digest)
    (pc : s.pc = 0x11d8) (small : n < 65) (baseBound : base < 256)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (index : s.getReg .x19 = BitVec.ofNat 64 n)
    (treeWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (seed : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64) :
    ∃ final,
      Trace hash image s 67 88 3 3 final ∧
      final.pc = 0x12d0 ∧
      final.getMem 0x81030 = s.getMem 0x81030 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80020 i.val) =
          (walk (GroupedBalancedUpperTree67.chainHash hash base tree
            ⟨n,by omega⟩) 0 3 value).extractLsb' (64*i.val) 64) := by
  let ready := wots s
  have first : Trace hash image s 41 41 0 0 ready :=
    (GroupedBalancedKeygenWotsPrepared67.wots_steps s pc).trace (hash := hash)
  have readyPC := GroupedBalancedKeygenWotsPrepared67.wots_pc s pc
  have readyIndex : ready.getReg .x19 = BitVec.ofNat 64 n :=
    (GroupedBalancedKeygenWotsFirstInput67.x19_wots s pc).trans index
  have not65 : ready.getReg .x19 ≠ 65#64 := by
    rw [readyIndex]
    exact word_ne_of_lt n 65 small (by decide)
  have not66 : ready.getReg .x19 ≠ 66#64 := by
    rw [readyIndex]
    exact word_ne_of_lt n 66 (by omega) (by decide)
  have readyHeader : ready.getMem 0x80000 =
      KeygenDomain.header 2 base 0 n 0 :=
    prepared_header s base n pc level counter
  have readyTree : ∀ i : Fin 3,
      ready.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    rw [prepared_tree s i]
    exact treeWords i
  have readySeed : ∀ i : Fin 2,
      ready.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64 := by
    intro i
    rw [prepared_seed s i]
    exact seed i
  obtain ⟨final,second,done,count,result⟩ :=
    normal_chain_value hash ready base tree ⟨n,by omega⟩ value
      readyPC not65 not66 baseBound readyHeader readyTree readySeed
  refine ⟨final,?_,done,?_,result⟩
  · simpa only [Nat.reduceAdd] using first.trans second
  · rw [count,prepared_counter]

theorem regular_step_endpoint (hash : Hash) (s : MachineState)
    (base tree n : Nat) (value : Reference.Digest)
    (pc : s.pc = 0x11d8) (small : n < 65) (baseBound : base < 256)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (index : s.getReg .x19 = BitVec.ofNat 64 n)
    (treeWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (seed : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64) :
    ∃ final,
      Trace hash image s 86 107 3 3 final ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80800 (2*n+i.val)) =
          (walk (GroupedBalancedUpperTree67.chainHash hash base tree
            ⟨n,by omega⟩) 0 3 value).extractLsb' (64*i.val) 64) := by
  obtain ⟨ready,first,readyPC,readyCounter,readyValue⟩ :=
    regular_from_entry_value hash s base tree n value pc small baseBound
      counter level index treeWords seed
  have readyWord : ready.getMem 0x81030 = BitVec.ofNat 64 n :=
    readyCounter.trans counter
  obtain ⟨safe,safeNext⟩ := address_safe ready n (by omega) readyWord
  let final := copyState ready
  have second : Trace hash image ready 19 19 0 0 final :=
    (copy_steps ready readyPC safe safeNext).trace (hash := hash)
  refine ⟨final,?_,?_⟩
  · simpa only [Nat.reduceAdd] using first.trans second
  · exact copy_endpoint_words ready n (by omega) readyWord
      (walk (GroupedBalancedUpperTree67.chainHash hash base tree
        ⟨n,by omega⟩) 0 3 value) readyValue

theorem special65_step_endpoint (hash : Hash) (s : MachineState)
    (base tree : Nat) (value : Reference.Digest)
    (pc : s.pc = 0x11d8) (baseBound : base < 256)
    (counter : s.getMem 0x81030 = 65#64)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (index : s.getReg .x19 = 65#64)
    (treeWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (seed : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64) :
    ∃ final,
      Trace hash image s 105 161 8 8 final ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80800 (2*65+i.val)) =
          (walk (GroupedBalancedUpperTree67.chainHash hash base tree
            ⟨65,by decide⟩) 0 8 value).extractLsb' (64*i.val) 64) := by
  let prepared := wots s
  have first : Trace hash image s 41 41 0 0 prepared :=
    (GroupedBalancedKeygenWotsPrepared67.wots_steps s pc).trace (hash := hash)
  have preparedPC := GroupedBalancedKeygenWotsPrepared67.wots_pc s pc
  have preparedIndex : prepared.getReg .x19 = 65#64 :=
    (GroupedBalancedKeygenWotsFirstInput67.x19_wots s pc).trans index
  have preparedHeader : prepared.getMem 0x80000 =
      KeygenDomain.header 2 base 0 65 0 :=
    prepared_header s base 65 pc level counter
  have preparedTree : ∀ i : Fin 3,
      prepared.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    rw [prepared_tree s i]
    exact treeWords i
  have preparedSeed : ∀ i : Fin 2,
      prepared.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64 := by
    intro i
    rw [prepared_seed s i]
    exact seed i
  obtain ⟨ready,second,readyPC,readyCounter,readyValue⟩ :=
    special65_chain_value hash prepared base tree value preparedPC
      preparedIndex baseBound preparedHeader preparedTree preparedSeed
  have readyWord : ready.getMem 0x81030 = 65#64 := by
    rw [readyCounter,prepared_counter]
    exact counter
  obtain ⟨safe,safeNext⟩ := address_safe ready 65 (by decide) readyWord
  let final := copyState ready
  have third : Trace hash image ready 19 19 0 0 final :=
    (copy_steps ready readyPC safe safeNext).trace (hash := hash)
  refine ⟨final,?_,?_⟩
  · simpa only [Nat.reduceAdd] using (first.trans second).trans third
  · exact copy_endpoint_words ready 65 (by decide) readyWord
      (walk (GroupedBalancedUpperTree67.chainHash hash base tree
        ⟨65,by decide⟩) 0 8 value) readyValue

theorem special66_step_endpoint (hash : Hash) (s : MachineState)
    (base tree : Nat) (value : Reference.Digest)
    (pc : s.pc = 0x11d8) (baseBound : base < 256)
    (counter : s.getMem 0x81030 = 66#64)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (index : s.getReg .x19 = 66#64)
    (treeWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (seed : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64) :
    ∃ final,
      Trace hash image s 114 184 10 10 final ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80800 (2*66+i.val)) =
          (walk (GroupedBalancedUpperTree67.chainHash hash base tree
            ⟨66,by decide⟩) 0 10 value).extractLsb' (64*i.val) 64) := by
  let prepared := wots s
  have first : Trace hash image s 41 41 0 0 prepared :=
    (GroupedBalancedKeygenWotsPrepared67.wots_steps s pc).trace (hash := hash)
  have preparedPC := GroupedBalancedKeygenWotsPrepared67.wots_pc s pc
  have preparedIndex : prepared.getReg .x19 = 66#64 :=
    (GroupedBalancedKeygenWotsFirstInput67.x19_wots s pc).trans index
  have preparedHeader : prepared.getMem 0x80000 =
      KeygenDomain.header 2 base 0 66 0 :=
    prepared_header s base 66 pc level counter
  have preparedTree : ∀ i : Fin 3,
      prepared.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    rw [prepared_tree s i]
    exact treeWords i
  have preparedSeed : ∀ i : Fin 2,
      prepared.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64 := by
    intro i
    rw [prepared_seed s i]
    exact seed i
  obtain ⟨ready,second,readyPC,readyCounter,readyValue⟩ :=
    special66_chain_value hash prepared base tree value preparedPC
      preparedIndex baseBound preparedHeader preparedTree preparedSeed
  have readyWord : ready.getMem 0x81030 = 66#64 := by
    rw [readyCounter,prepared_counter]
    exact counter
  obtain ⟨safe,safeNext⟩ := address_safe ready 66 (by decide) readyWord
  let final := copyState ready
  have third : Trace hash image ready 19 19 0 0 final :=
    (copy_steps ready readyPC safe safeNext).trace (hash := hash)
  refine ⟨final,?_,?_⟩
  · simpa only [Nat.reduceAdd] using (first.trans second).trans third
  · exact copy_endpoint_words ready 66 (by decide) readyWord
      (walk (GroupedBalancedUpperTree67.chainHash hash base tree
        ⟨66,by decide⟩) 0 10 value) readyValue

#print axioms regular_from_entry_value
#print axioms regular_step_endpoint
#print axioms special65_step_endpoint
#print axioms special66_step_endpoint

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalChain67
