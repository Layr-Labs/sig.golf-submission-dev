import SigGolfCandidate.Hypertree.SignIndexRefine
import SigGolfCandidate.Hypertree.SecurityRandomOracle
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH5Entry67

/-! The verifier's first query uses the reference tag-five serialization. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyPrefixIndex67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem h5_query_of_bytes (q : MachineState) (message : Message)
    (randomizer : Bytes 32)
    (source : q.getReg .x10 = 0x80000)
    (length : q.getReg .x11 = 896)
    (header : ∀ i, i < 32 →
      q.getByte (BitVec.ofNat 64 (0x80000+i)) =
        if i = 0 then 5 else 0)
    (zero : ∀ i, i < 16 →
      q.getByte (BitVec.ofNat 64 (0x80020+i)) = 0)
    (messageBytes : ∀ i, i < 32 →
      q.getByte (BitVec.ofNat 64 (0x80030+i)) =
        message.extractLsb' (8*i) 8)
    (randomizerBytes : ∀ i, i < 32 →
      q.getByte (BitVec.ofNat 64 (0x80050+i)) =
        randomizer.extractLsb' (8*i) 8) :
    hashInput q = SecurityRandomOracle.indexInput message randomizer := by
  have query : hashInput q =
      Reference.packed (Signing.indexPayload message randomizer) := by
    apply Serialization.hashInput_of_list q 0x80000
      (Signing.indexPayload message randomizer)
    · exact source
    · rw [length, Signing.indexPayload_length]
      rfl
    · intro i hi
      have bound : i < 112 := by simpa using hi
      rw [Signing.indexPayload_byte message randomizer ⟨i,bound⟩]
      dsimp only
      by_cases z : i = 0
      · simpa [z] using header i (by omega)
      by_cases h32 : i < 32
      · simpa [z,h32] using header i h32
      by_cases h48 : i < 48
      · have b := zero (i-32) (by omega)
        have pos : 0x80020+(i-32) = 0x80000+i := by omega
        rw [pos] at b
        simpa [z,h32,h48] using b
      by_cases h80 : i < 80
      · have b := messageBytes (i-48) (by omega)
        have pos : 0x80030+(i-48) = 0x80000+i := by omega
        rw [pos] at b
        simpa [z,h32,h48,h80] using b
      · have b := randomizerBytes (i-80) (by omega)
        have pos : 0x80050+(i-80) = 0x80000+i := by omega
        rw [pos] at b
        simpa [z,h32,h48,h80] using b
  simpa [SecurityRandomOracle.indexInput,
    SecurityRandomOracle.addressedInput,Signing.indexPayload,
    Reference.packed] using query

theorem h5_setup_header (s : MachineState) :
    (GroupedBalancedVerifyH5Entry67.setupState s).getMem 0x80000 = 5 ∧
    (GroupedBalancedVerifyH5Entry67.setupState s).getMem 0x80008 = 0 ∧
    (GroupedBalancedVerifyH5Entry67.setupState s).getMem 0x80010 = 0 ∧
    (GroupedBalancedVerifyH5Entry67.setupState s).getMem 0x80018 = 0 := by
  simp [GroupedBalancedVerifyH5Entry67.setupState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem h5_setup_mem_other (s : MachineState) (a : Word)
    (h0 : a ≠ 0x80000) (h8 : a ≠ 0x80008)
    (h16 : a ≠ 0x80010) (h24 : a ≠ 0x80018) :
    (GroupedBalancedVerifyH5Entry67.setupState s).getMem a = s.getMem a := by
  simp [GroupedBalancedVerifyH5Entry67.setupState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  split_ifs <;> simp_all

theorem h5_setup_byte_after_header (s : MachineState)
    (base i : Nat) (aligned : base % 8 = 0)
    (above : 0x80020 ≤ base) (bound : base+i < 2^64) :
    (GroupedBalancedVerifyH5Entry67.setupState s).getByte
      (BitVec.ofNat 64 (base+i)) =
      s.getByte (BitVec.ofNat 64 (base+i)) := by
  let a := Signing.wordAddress base (i/8)
  have addr : a.toNat = base+8*(i/8) := by
    simp only [a,Signing.wordAddress,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : base+8*(i/8)<2^64)]
  have other (n : Nat) (small : n < 0x80020) :
      a ≠ BitVec.ofNat 64 n := by
    intro eq
    have h := congrArg BitVec.toNat eq
    rw [addr,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : n < 2^64)] at h
    omega
  rw [Signing.getByte_word (GroupedBalancedVerifyH5Entry67.setupState s)
      base i aligned bound,
    Signing.getByte_word s base i aligned bound]
  rw [h5_setup_mem_other s a (other 0x80000 (by decide))
    (other 0x80008 (by decide)) (other 0x80010 (by decide))
    (other 0x80018 (by decide))]

theorem h5_setup_header_bytes (s : MachineState) :
    ∀ i, i < 32 →
      (GroupedBalancedVerifyH5Entry67.setupState s).getByte
        (BitVec.ofNat 64 (0x80000+i)) =
          if i = 0 then 5 else 0 := by
  intro i hi
  obtain ⟨h0,h8,h16,h24⟩ := h5_setup_header s
  have words : ∀ j, j < 4 →
      (GroupedBalancedVerifyH5Entry67.setupState s).getMem
        (Signing.wordAddress 0x80000 j) =
          if j = 0 then 5 else 0 := by
    intro j hj
    interval_cases j
    · change (GroupedBalancedVerifyH5Entry67.setupState s).getMem
        0x80000 = 5
      exact h0
    · change (GroupedBalancedVerifyH5Entry67.setupState s).getMem
        0x80008 = 0
      exact h8
    · change (GroupedBalancedVerifyH5Entry67.setupState s).getMem
        0x80010 = 0
      exact h16
    · change (GroupedBalancedVerifyH5Entry67.setupState s).getMem
        0x80018 = 0
      exact h24
  rw [Signing.getByte_word
    (GroupedBalancedVerifyH5Entry67.setupState s)
    0x80000 i (by decide) (by omega)]
  rw [words (i/8) (by omega)]
  interval_cases i <;> decide +revert

private theorem second_copy_code :
    Keygen.CopyCode GroupedBalancedVerifyImage67Fast2Byte.image
      0x10a0 := by
  unfold Keygen.CopyCode GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

theorem second_copy_frame (s : MachineState)
    (pc : s.pc = 0x108c) :
    ∃ final,
      OrdinarySteps GroupedBalancedVerifyImage67Fast2Byte.image
        s 29 final ∧
      final.pc = 0x10b8 ∧
      (∀ j, j < 4 →
        final.getMem (Signing.wordAddress 0x80050 j) =
          s.getMem (Signing.wordAddress 0x2c700 j)) ∧
      (∀ a : Word,
        (∀ j, j < 4 → a ≠ Signing.wordAddress 0x80050 j) →
          final.getMem a = s.getMem a) := by
  let setup := GroupedBalancedVerifySecondCopy67.setupState s
  have first := GroupedBalancedVerifySecondCopy67.setup_steps s pc
  obtain ⟨src,dst,count⟩ := GroupedBalancedVerifySecondCopy67.setup_regs s
  have inv : Keygen.CopyInvariant 0x10a0 0x2c700 0x80050 4 4
      setup := by
    simp [Keygen.CopyInvariant,setup,
      GroupedBalancedVerifySecondCopy67.setup_pc s pc,
      src,dst,count]
  obtain ⟨final,copyRun,done,words,frame,_,_⟩ :=
    Keygen.copy_all_frame
      GroupedBalancedVerifyImage67Fast2Byte.image
      0x10a0 second_copy_code 0x2c700 0x80050 4 setup inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_,_,endPC,_,_,_⟩ := done
  refine ⟨final,?_,by simpa using endPC,?_,?_⟩
  · simpa only [Nat.reduceAdd] using
      Keygen.ordinary_trans GroupedBalancedVerifyImage67Fast2Byte.image
        s setup final 5 24 first copyRun
  · intro j hj
    rw [words j hj]
    exact GroupedBalancedVerifySecondCopy67.setup_mem s _
  · intro a outside
    rw [frame a outside]
    exact GroupedBalancedVerifySecondCopy67.setup_mem s a

theorem verify_setup_zero (s : MachineState) :
    (GroupedBalancedVerifySetup67.setupState s).getMem 0x80020 = 0 ∧
    (GroupedBalancedVerifySetup67.setupState s).getMem 0x80028 = 0 := by
  simp [GroupedBalancedVerifySetup67.setupState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem verify_setup_mem_other (s : MachineState) (a : Word)
    (h48 : a ≠ 0x81048) (h20 : a ≠ 0x80020)
    (h28 : a ≠ 0x80028) :
    (GroupedBalancedVerifySetup67.setupState s).getMem a = s.getMem a := by
  simp [GroupedBalancedVerifySetup67.setupState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  split_ifs <;> simp_all

private theorem address_small (base j : Nat) (hb : base ≤ 0x80050)
    (hj : j < 4) : base + 8*j < 2^64 := by
  calc
    base + 8*j < 0x80070 := by omega
    _ < 2^64 := by decide

theorem h5_query_words (hash : Hash) (initial : MachineState)
    (pc : initial.pc = 0x1000) :
    ∃ query,
      Trace hash GroupedBalancedVerifyImage67Fast2Byte.image
        initial 104 104 0 0 query ∧
      query.pc = 0x1110 ∧
      query.getReg .x5 = 1 ∧
      query.getReg .x10 = 0x80000 ∧
      query.getReg .x11 = 896 ∧
      query.getReg .x12 = 0x80300 ∧
      (∀ i, i < 32 →
        query.getByte (BitVec.ofNat 64 (0x80000+i)) =
          if i = 0 then 5 else 0) ∧
      query.getMem 0x80020 = 0 ∧
      query.getMem 0x80028 = 0 ∧
      (∀ j, j < 4 →
        query.getMem (Signing.wordAddress 0x80030 j) =
          initial.getMem (Signing.wordAddress 0 j)) ∧
      (∀ j, j < 4 →
        query.getMem (Signing.wordAddress 0x80050 j) =
          initial.getMem (Signing.wordAddress 0x2c700 j)) ∧
      query.getMem 0x81048 = 0x2c720 := by
  let entered := GroupedBalancedVerifyEntry67.entryState initial
  have entryRun := GroupedBalancedVerifyEntry67.entry_steps initial pc
  let setup := GroupedBalancedVerifySetup67.setupState entered
  have setupRun := GroupedBalancedVerifySetup67.setup_steps entered
    (GroupedBalancedVerifyEntry67.entry_pc initial pc)
  obtain ⟨src,dst,count⟩ := GroupedBalancedVerifySetup67.setup_regs entered
  obtain ⟨first,firstRun,firstPc,firstWords,firstFrame,_⟩ :=
    GroupedBalancedVerifyFirstCopy67.first_copy setup
      (GroupedBalancedVerifySetup67.setup_pc entered
        (GroupedBalancedVerifyEntry67.entry_pc initial pc))
      src dst count
  obtain ⟨second,secondRun,secondPc,secondWords,secondFrame⟩ :=
    second_copy_frame first firstPc
  let query := GroupedBalancedVerifyH5Entry67.setupState second
  have queryRun := GroupedBalancedVerifyH5Entry67.setup_steps second secondPc
  obtain ⟨queryService,querySrc,queryLen,queryDst⟩ :=
    GroupedBalancedVerifyH5Entry67.setup_regs second
  have outsideFirst (a : Word)
      (ha : a.toNat < 0x80030 ∨ 0x80050 ≤ a.toNat) :
      first.getMem a = setup.getMem a := by
    apply firstFrame
    intro j hj eq
    have hn := congrArg BitVec.toNat eq
    have hv : (Signing.wordAddress 0x80030 j).toNat =
        0x80030+8*j := by
      simp [Signing.wordAddress,BitVec.toNat_ofNat]
      exact address_small 0x80030 j (by decide) hj
    rw [hv] at hn
    rcases ha with lo | hi <;> omega
  have outsideSecond (a : Word)
      (ha : a.toNat < 0x80050 ∨ 0x80070 ≤ a.toNat) :
      second.getMem a = first.getMem a := by
    apply secondFrame
    intro j hj eq
    have hn := congrArg BitVec.toNat eq
    have hv : (Signing.wordAddress 0x80050 j).toNat =
        0x80050+8*j := by
      simp [Signing.wordAddress,BitVec.toNat_ofNat]
      exact address_small 0x80050 j (by decide) hj
    rw [hv] at hn
    rcases ha with lo | hi <;> omega
  have headerOther (a : Word) (ha : 0x80020 ≤ a.toNat) :
      query.getMem a = second.getMem a := by
    apply h5_setup_mem_other second a
    all_goals
      intro eq
      have hn := congrArg BitVec.toNat eq
      simp at hn
      omega
  refine ⟨query,?_,GroupedBalancedVerifyH5Entry67.setup_pc second secondPc,
    queryService,querySrc,queryLen,queryDst,
    h5_setup_header_bytes second,?_,?_,?_,?_,?_⟩
  · have all := (((entryRun.trace (hash := hash)).trans setupRun.trace).trans
      firstRun.trace).trans (secondRun.trace.trans queryRun.trace)
    simpa only [Nat.reduceAdd] using all
  · rw [headerOther 0x80020 (by decide),
      outsideSecond 0x80020 (Or.inl (by decide)),
      outsideFirst 0x80020 (Or.inl (by decide))]
    exact (verify_setup_zero entered).1
  · rw [headerOther 0x80028 (by decide),
      outsideSecond 0x80028 (Or.inl (by decide)),
      outsideFirst 0x80028 (Or.inl (by decide))]
    exact (verify_setup_zero entered).2
  · intro j hj
    let a := Signing.wordAddress 0x80030 j
    let b := Signing.wordAddress 0 j
    have aa : a.toNat = 0x80030+8*j := by
      simp [a,Signing.wordAddress,BitVec.toNat_ofNat]
      exact address_small 0x80030 j (by decide) hj
    have bb : b.toNat = 8*j := by
      simp [b,Signing.wordAddress,BitVec.toNat_ofNat]
      simpa using address_small 0 j (by decide) hj
    calc
      query.getMem a = second.getMem a := headerOther a (by omega)
      _ = first.getMem a := outsideSecond a (Or.inl (by omega))
      _ = setup.getMem b := firstWords j hj
      _ = entered.getMem b := verify_setup_mem_other entered b
        (by intro e; have h := congrArg BitVec.toNat e; simp [bb] at h; omega)
        (by intro e; have h := congrArg BitVec.toNat e; simp [bb] at h; omega)
        (by intro e; have h := congrArg BitVec.toNat e; simp [bb] at h; omega)
      _ = initial.getMem b := GroupedBalancedVerifyEntry67.entry_mem_other
        initial b
        (by intro e; have h := congrArg BitVec.toNat e; simp [bb] at h; omega)
        (by intro e; have h := congrArg BitVec.toNat e; simp [bb] at h; omega)
        (by intro e; have h := congrArg BitVec.toNat e; simp [bb] at h; omega)
  · intro j hj
    let a := Signing.wordAddress 0x80050 j
    let b := Signing.wordAddress 0x2c700 j
    have aa : a.toNat = 0x80050+8*j := by
      simp [a,Signing.wordAddress,BitVec.toNat_ofNat]
      exact address_small 0x80050 j (by decide) hj
    have bb : b.toNat = 0x2c700+8*j := by
      simp [b,Signing.wordAddress,BitVec.toNat_ofNat]
      exact address_small 0x2c700 j (by decide) hj
    calc
      query.getMem a = second.getMem a := headerOther a (by omega)
      _ = first.getMem b := secondWords j hj
      _ = setup.getMem b := outsideFirst b (Or.inl (by omega))
      _ = entered.getMem b := verify_setup_mem_other entered b
        (by intro e; have h := congrArg BitVec.toNat e; simp [bb] at h; omega)
        (by intro e; have h := congrArg BitVec.toNat e; simp [bb] at h; omega)
        (by intro e; have h := congrArg BitVec.toNat e; simp [bb] at h; omega)
      _ = initial.getMem b := GroupedBalancedVerifyEntry67.entry_mem_other
        initial b
        (by intro e; have h := congrArg BitVec.toNat e; simp [bb] at h; omega)
        (by intro e; have h := congrArg BitVec.toNat e; simp [bb] at h; omega)
        (by intro e; have h := congrArg BitVec.toNat e; simp [bb] at h; omega)
  · exact (GroupedBalancedVerifyH5Entry67.setup_pointer second).trans
      ((secondFrame 0x81048 (by intro i hi; interval_cases i <;> decide)).trans
        ((firstFrame 0x81048 (by intro i hi; interval_cases i <;> decide)).trans
          (GroupedBalancedVerifySetup67.setup_pointer entered)))

theorem h5_query_refines (hash : Hash) (initial : MachineState)
    (message : Message) (randomizer : Bytes 32)
    (pc : initial.pc = 0x1000)
    (messageBytes : ∀ i, i < 32 →
      initial.getByte (BitVec.ofNat 64 i) =
        message.extractLsb' (8*i) 8)
    (randomizerBytes : ∀ i, i < 32 →
      initial.getByte (BitVec.ofNat 64 (0x2c700+i)) =
        randomizer.extractLsb' (8*i) 8) :
    ∃ query,
      Trace hash GroupedBalancedVerifyImage67Fast2Byte.image
        initial 104 104 0 0 query ∧
      query.pc = 0x1110 ∧
      query.getReg .x5 = 1 ∧
      query.getReg .x10 = 0x80000 ∧
      query.getReg .x11 = 896 ∧
      query.getReg .x12 = 0x80300 ∧
      hashInput query = SecurityRandomOracle.indexInput message randomizer ∧
      query.getMem 0x81048 = 0x2c720 := by
  obtain ⟨query,run,queryPC,service,src,len,dst,header,zero0,zero8,
    msgWords,randWords,pointer⟩ :=
    h5_query_words hash initial pc
  have zero : ∀ i, i < 16 →
      query.getByte (BitVec.ofNat 64 (0x80020+i)) = 0 := by
    intro i hi
    rw [Signing.getByte_word query 0x80020 i (by decide) (by omega)]
    by_cases h : i < 8
    · rw [show i/8=0 by omega]
      change extractByte (query.getMem 0x80020) (i%8) = 0
      rw [zero0]
      simp [extractByte]
    · rw [show i/8=1 by omega]
      change extractByte (query.getMem 0x80028) (i%8) = 0
      rw [zero8]
      simp [extractByte]
  have messageCopied : ∀ i, i < 32 →
      query.getByte (BitVec.ofNat 64 (0x80030+i)) =
        message.extractLsb' (8*i) 8 := by
    intro i hi
    rw [Signing.getByte_word query 0x80030 i (by decide) (by omega),
      msgWords (i/8) (by omega)]
    have old := Signing.getByte_word initial 0 i (by decide) (by omega)
    simp only [Nat.zero_add] at old
    have value := messageBytes i hi
    rw [old] at value
    exact value
  have randomizerCopied : ∀ i, i < 32 →
      query.getByte (BitVec.ofNat 64 (0x80050+i)) =
        randomizer.extractLsb' (8*i) 8 := by
    intro i hi
    rw [Signing.getByte_word query 0x80050 i (by decide) (by omega),
      randWords (i/8) (by omega)]
    rw [← Signing.getByte_word initial 0x2c700 i (by decide) (by omega)]
    exact randomizerBytes i hi
  exact ⟨query,run,queryPC,service,src,len,dst,
    h5_query_of_bytes query message randomizer src len header zero
      messageCopied randomizerCopied,pointer⟩

#print axioms h5_query_refines
#print axioms h5_query_words
#print axioms second_copy_frame
#print axioms h5_query_of_bytes
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyPrefixIndex67
