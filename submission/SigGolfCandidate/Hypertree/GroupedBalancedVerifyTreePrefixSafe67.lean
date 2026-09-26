import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeStart67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeHighFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyStackGlobal67

/-! Preserve the decoder tables and stack register through the verifier prefix. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreePrefixSafe67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyTreeHighFrame67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67Byte.submission
private abbrev Low := GroupedBalancedVerifyStackGlobal67.LowFrame
private theorem low_ne (a : Word) (low : a.toNat < 0x80000)
    (b : Nat) (bound : 0x80000 ≤ b) (small : b < 2^64) :
    a ≠ BitVec.ofNat 64 b :=
  GroupedBalancedVerifyStackGlobal67.low_ne a low b bound small

private theorem high_ne (a : Word) (ha : 0x90000 ≤ a.toNat)
    (b : Nat) (hb : b < 0x90000) : a ≠ BitVec.ofNat 64 b := by
  intro eq
  have hn := congrArg BitVec.toNat eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : b < 2^64)] at hn
  omega

theorem entry_safe (s : MachineState) :
    SafeFrame s (GroupedBalancedVerifyEntry67.entryState s) := by
  constructor
  · intro a ha
    exact GroupedBalancedVerifyEntry67.entry_mem_other s a
      (high_ne a ha 0x81000 (by decide))
      (high_ne a ha 0x81030 (by decide))
      (high_ne a ha 0x81038 (by decide))
  · exact GroupedBalancedVerifyEntry67.entry_sp s

theorem entry_low (s : MachineState) :
    GroupedBalancedVerifyStackGlobal67.LowFrame s
      (GroupedBalancedVerifyEntry67.entryState s) := by
  intro a low
  exact GroupedBalancedVerifyEntry67.entry_mem_other s a
    (GroupedBalancedVerifyStackGlobal67.low_ne a low 0x81000 (by decide) (by decide))
    (GroupedBalancedVerifyStackGlobal67.low_ne a low 0x81030 (by decide) (by decide))
    (GroupedBalancedVerifyStackGlobal67.low_ne a low 0x81038 (by decide) (by decide))

theorem setup_safe (s : MachineState) :
    SafeFrame s (GroupedBalancedVerifySetup67.setupState s) := by
  constructor
  · intro a ha
    have h48 := high_ne a ha 0x81048 (by decide)
    have h20 := high_ne a ha 0x80020 (by decide)
    have h28 := high_ne a ha 0x80028 (by decide)
    simp [GroupedBalancedVerifySetup67.setupState,execInstrBr,signExtend12,
      h48,h20,h28,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,MachineState.getMem_setMem_eq,
      MachineState.getMem_setMem_ne]
  · simp [GroupedBalancedVerifySetup67.setupState,execInstrBr,
      MachineState.getReg_setReg_ne]

theorem setup_low (s : MachineState) :
    GroupedBalancedVerifyStackGlobal67.LowFrame s
      (GroupedBalancedVerifySetup67.setupState s) := by
  intro a low
  have h48 := GroupedBalancedVerifyStackGlobal67.low_ne a low 0x81048 (by decide) (by decide)
  have h20 := GroupedBalancedVerifyStackGlobal67.low_ne a low 0x80020 (by decide) (by decide)
  have h28 := GroupedBalancedVerifyStackGlobal67.low_ne a low 0x80028 (by decide) (by decide)
  simp [GroupedBalancedVerifySetup67.setupState,execInstrBr,signExtend12,
    h48,h20,h28,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,MachineState.getMem_setMem_eq,
    MachineState.getMem_setMem_ne]

theorem setup_base (s : MachineState) :
    (GroupedBalancedVerifySetup67.setupState s).getMem 0x81000 =
      s.getMem 0x81000 := by
  simp [GroupedBalancedVerifySetup67.setupState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem first_copy_safe (s final : MachineState)
    (pc : s.pc = 0x1074)
    (src : s.getReg .x6 = 0)
    (dst : s.getReg .x7 = 0x80030)
    (count : s.getReg .x10 = 4)
    (run : OrdinarySteps image s 24 final) :
    SafeFrame s final := by
  obtain ⟨other,otherRun,_,_,frame,sp⟩ :=
    GroupedBalancedVerifyFirstCopy67.first_copy s pc src dst count
  have eq := Keygen.ordinary_deterministic run otherRun
  subst other
  constructor
  · intro a ha
    apply frame a
    intro i hi
    simpa [Signing.wordAddress] using
      high_ne a ha (0x80030+8*i) (by omega)
  · exact sp

theorem first_copy_low (s final : MachineState)
    (pc : s.pc = 0x1074)
    (src : s.getReg .x6 = 0)
    (dst : s.getReg .x7 = 0x80030)
    (count : s.getReg .x10 = 4)
    (run : OrdinarySteps image s 24 final) :
    GroupedBalancedVerifyStackGlobal67.LowFrame s final := by
  obtain ⟨other,otherRun,_,_,frame,_⟩ :=
    GroupedBalancedVerifyFirstCopy67.first_copy s pc src dst count
  have eq := Keygen.ordinary_deterministic run otherRun
  subst other
  intro a low
  apply frame a
  intro i hi
  simpa [Signing.wordAddress] using
    GroupedBalancedVerifyStackGlobal67.low_ne a low (0x80030+8*i) (by omega) (by omega)

theorem first_copy_base (s final : MachineState)
    (pc : s.pc = 0x1074)
    (src : s.getReg .x6 = 0)
    (dst : s.getReg .x7 = 0x80030)
    (count : s.getReg .x10 = 4)
    (run : OrdinarySteps image s 24 final) :
    final.getMem 0x81000 = s.getMem 0x81000 := by
  obtain ⟨other,otherRun,_,_,frame,_⟩ :=
    GroupedBalancedVerifyFirstCopy67.first_copy s pc src dst count
  have eq := Keygen.ordinary_deterministic run otherRun
  subst other
  exact frame 0x81000 (by intro i hi; interval_cases i <;> decide)

theorem loaded_first_safe (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial final,
      initialState program .verify input = some initial ∧
      Trace hash image initial 53 53 0 0 final ∧
      final.pc = 0x108c ∧
      SafeFrame initial final ∧
      final.getMem 0x81000 = 0 ∧
      GroupedBalancedVerifyStackGlobal67.LowFrame initial final := by
  obtain ⟨initial,loaded,initialPC⟩ := initialState_exists program
    GroupedBalancedProgram67Byte.admissible .verify input
  let entry := GroupedBalancedVerifyEntry67.entryState initial
  let setup := GroupedBalancedVerifySetup67.setupState entry
  have entryRun := GroupedBalancedVerifyEntry67.entry_steps initial initialPC
  have entryPC := GroupedBalancedVerifyEntry67.entry_pc initial initialPC
  have setupRun := GroupedBalancedVerifySetup67.setup_steps entry entryPC
  have setupPC := GroupedBalancedVerifySetup67.setup_pc entry entryPC
  obtain ⟨src,dst,count⟩ := GroupedBalancedVerifySetup67.setup_regs entry
  obtain ⟨final,copyRun,finalPC,_,_,_⟩ :=
    GroupedBalancedVerifyFirstCopy67.first_copy setup setupPC src dst count
  refine ⟨initial,final,loaded,?_,finalPC,?_,?_,?_⟩
  · have run := (entryRun.trace (hash := hash)).trans
      (setupRun.trace.trans copyRun.trace)
    simpa only [Nat.reduceAdd] using run
  · exact safe_trans (safe_trans (entry_safe initial) (setup_safe entry))
      (first_copy_safe setup final setupPC src dst count copyRun)
  · rw [first_copy_base setup final setupPC src dst count copyRun,
      setup_base]
    exact (GroupedBalancedVerifyEntry67.entry_words initial).1
  · exact (entry_low initial).trans
      ((setup_low entry).trans
        (first_copy_low setup final setupPC src dst count copyRun))

private theorem second_copy_code : Keygen.CopyCode image 0x10a0 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

theorem second_stage (s : MachineState) (pc : s.pc = 0x108c) :
    ∃ final, OrdinarySteps image s 29 final ∧ final.pc = 0x10b8 ∧
      SafeFrame s final ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      Low s final := by
  let setup := GroupedBalancedVerifySecondCopy67.setupState s
  have setupRun := GroupedBalancedVerifySecondCopy67.setup_steps s pc
  have setupPC := GroupedBalancedVerifySecondCopy67.setup_pc s pc
  obtain ⟨src,dst,count⟩ := GroupedBalancedVerifySecondCopy67.setup_regs s
  have inv : Keygen.CopyInvariant 0x10a0 0x2c700 0x80050 4 4 setup := by
    simp [Keygen.CopyInvariant,setup,setupPC,src,dst,count]
  obtain ⟨final,copyRun,done,_,frame,_,sp⟩ :=
    Keygen.copy_all_frame image 0x10a0 second_copy_code 0x2c700 0x80050 4 setup inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_,_,endPC,_,_,_⟩ := done
  refine ⟨final,?_,by simpa using endPC,⟨?_,?_⟩,?_,?_⟩
  · have run := Keygen.ordinary_trans image s setup final 5 24 setupRun copyRun
    simpa only [Nat.reduceAdd] using run
  · intro a ha
    rw [frame a (by
      intro i hi
      simpa [Signing.wordAddress] using
        high_ne a ha (0x80050+8*i) (by omega))]
    exact GroupedBalancedVerifySecondCopy67.setup_mem s a
  · have setupSp : setup.getReg .x2 = s.getReg .x2 := by
      simp [setup,GroupedBalancedVerifySecondCopy67.setupState,execInstrBr,
        MachineState.getReg_setReg_ne]
    exact sp.trans setupSp
  · rw [frame 0x81000 (by intro i hi; interval_cases i <;> decide)]
    exact GroupedBalancedVerifySecondCopy67.setup_mem s 0x81000
  · intro a low
    rw [frame a (by
      intro i hi
      simpa [Signing.wordAddress] using
        low_ne a low (0x80050+8*i) (by omega) (by omega))]
    exact GroupedBalancedVerifySecondCopy67.setup_mem s a

theorem loaded_second_safe (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial final,
      initialState program .verify input = some initial ∧
      Trace hash image initial 82 82 0 0 final ∧
      final.pc = 0x10b8 ∧
      SafeFrame initial final ∧
      final.getMem 0x81048 = 0x2c720 ∧
      final.getMem 0x81000 = 0 ∧
      Low initial final := by
  obtain ⟨initial,before,loaded,firstRun,firstPC,firstSafe,firstBase,firstLow⟩ :=
    loaded_first_safe hash input
  obtain ⟨final,secondRun,secondPC,secondSafe,secondBase,secondLow⟩ :=
    second_stage before firstPC
  have all : Trace hash image initial 82 82 0 0 final := by
    simpa only [Nat.reduceAdd] using firstRun.trans secondRun.trace
  obtain ⟨otherInitial,other,otherLoaded,otherRun,_,otherPointer⟩ :=
    GroupedBalancedVerifySecondCopy67.from_loaded hash input
  have initialEq : otherInitial = initial := by
    rw [loaded] at otherLoaded
    exact Option.some.inj otherLoaded.symm
  subst otherInitial
  have finalEq : other = final := Trace.deterministic otherRun all
  subst other
  exact ⟨initial,final,loaded,all,secondPC,safe_trans firstSafe secondSafe,
    otherPointer,secondBase.trans firstBase,firstLow.trans secondLow⟩

theorem h5_entry_safe (s : MachineState) :
    SafeFrame s (GroupedBalancedVerifyH5Entry67.setupState s) := by
  constructor
  · intro a ha
    simp [GroupedBalancedVerifyH5Entry67.setupState,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
    split_ifs with e1 e2 e3 e4
    all_goals
      try { have hn := congrArg BitVec.toNat e1; simp at hn; omega }
      try { have hn := congrArg BitVec.toNat e2; simp at hn; omega }
      try { have hn := congrArg BitVec.toNat e3; simp at hn; omega }
      try { have hn := congrArg BitVec.toNat e4; simp at hn; omega }
      try rfl
  · simp [GroupedBalancedVerifyH5Entry67.setupState,execInstrBr,
      MachineState.getReg_setReg_ne]

theorem h5_entry_low (s : MachineState) :
    Low s (GroupedBalancedVerifyH5Entry67.setupState s) := by
  intro a low
  have h00 := low_ne a low 0x80000 (by decide) (by decide)
  have h08 := low_ne a low 0x80008 (by decide) (by decide)
  have h10 := low_ne a low 0x80010 (by decide) (by decide)
  have h18 := low_ne a low 0x80018 (by decide) (by decide)
  simp [GroupedBalancedVerifyH5Entry67.setupState,execInstrBr,signExtend12,
    h00,h08,h10,h18,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,MachineState.getMem_setMem_ne]

theorem h5_entry_base (s : MachineState) :
    (GroupedBalancedVerifyH5Entry67.setupState s).getMem 0x81000 =
      s.getMem 0x81000 := by
  simp [GroupedBalancedVerifyH5Entry67.setupState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem hash_safe (s : MachineState) (answer : BitVec 256)
    (dest : s.getReg .x12 = 0x80300) :
    SafeFrame s (writeHash s answer) := by
  constructor
  · intro a ha
    simp [writeHash,dest]
    split_ifs with e1 e2 e3 e4
    all_goals
      try { have hn := congrArg BitVec.toNat e1; simp at hn; omega }
      try { have hn := congrArg BitVec.toNat e2; simp at hn; omega }
      try { have hn := congrArg BitVec.toNat e3; simp at hn; omega }
      try { have hn := congrArg BitVec.toNat e4; simp at hn; omega }
      try rfl
  · simp [writeHash]

theorem hash_low (s : MachineState) (answer : BitVec 256)
    (dest : s.getReg .x12 = 0x80300) :
    Low s (writeHash s answer) := by
  intro a low
  apply Signing.hash_answer_frame s answer dest a
  intro i
  fin_cases i <;> simp only [Signing.wordAddress] <;>
    apply low_ne a low <;> decide

theorem loaded_h5_query_safe (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial query,
      initialState program .verify input = some initial ∧
      Trace hash image initial 104 104 0 0 query ∧
      query.pc = 0x1110 ∧
      query.getReg .x5 = 1 ∧
      query.getReg .x10 = 0x80000 ∧
      query.getReg .x11 = 896 ∧
      query.getReg .x12 = 0x80300 ∧
      query.getMem 0x81048 = 0x2c720 ∧
      SafeFrame initial query ∧
      query.getMem 0x81000 = 0 ∧
      Low initial query := by
  obtain ⟨initial,before,loaded,beforeRun,beforePC,beforeSafe,pointer,base,
    beforeLow⟩ :=
    loaded_second_safe hash input
  let query := GroupedBalancedVerifyH5Entry67.setupState before
  have entryRun := GroupedBalancedVerifyH5Entry67.setup_steps before beforePC
  obtain ⟨service,src,len,dst⟩ := GroupedBalancedVerifyH5Entry67.setup_regs before
  refine ⟨initial,query,loaded,?_,
    GroupedBalancedVerifyH5Entry67.setup_pc before beforePC,
    service,src,len,dst,
    (GroupedBalancedVerifyH5Entry67.setup_pointer before).trans pointer,
    safe_trans beforeSafe (h5_entry_safe before),
    (h5_entry_base before).trans base,
    beforeLow.trans (h5_entry_low before)⟩
  simpa only [Nat.reduceAdd] using beforeRun.trans entryRun.trace

private theorem h5_hash_code : Keygen.instructionAt image 0x1110 = some (.base .ECALL) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

private theorem h5_copy_code : Keygen.CopyCode image 0x1128 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

theorem h5_copy_safe (s : MachineState) (pc : s.pc = 0x1114) :
    ∃ final, OrdinarySteps image s 17 final ∧ final.pc = 0x1140 ∧
      SafeFrame s final ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      Low s final := by
  let setup := GroupedBalancedVerifyH5Output67.copySetup s
  have setupRun := GroupedBalancedVerifyH5Output67.setup_steps s pc
  have setupPC := GroupedBalancedVerifyH5Output67.setup_pc s pc
  obtain ⟨src,dst,count⟩ := GroupedBalancedVerifyH5Output67.setup_regs s
  have inv : Keygen.CopyInvariant 0x1128 0x80300 0x81008 2 2 setup := by
    simp [Keygen.CopyInvariant,setup,setupPC,src,dst,count]
  obtain ⟨final,copyRun,done,_,frame,_,sp⟩ :=
    Keygen.copy_all_frame image 0x1128 h5_copy_code 0x80300 0x81008 2 setup inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_,_,endPC,_,_,_⟩ := done
  refine ⟨final,?_,by simpa using endPC,⟨?_,?_⟩,?_,?_⟩
  · have run := Keygen.ordinary_trans image s setup final 5 12 setupRun copyRun
    simpa only [Nat.reduceAdd] using run
  · intro a ha
    rw [frame a (by
      intro i hi
      simpa [Signing.wordAddress] using
        high_ne a ha (0x81008+8*i) (by omega))]
    exact GroupedBalancedVerifyH5Output67.setup_mem s a
  · have setupSp : setup.getReg .x2 = s.getReg .x2 := by
      simp [setup,GroupedBalancedVerifyH5Output67.copySetup,execInstrBr,
        MachineState.getReg_setReg_ne]
    exact sp.trans setupSp
  · rw [frame 0x81000 (by intro i hi; interval_cases i <;> decide)]
    exact GroupedBalancedVerifyH5Output67.setup_mem s 0x81000
  · intro a low
    rw [frame a (by
      intro i hi
      simpa [Signing.wordAddress] using
        low_ne a low (0x81008+8*i) (by omega) (by omega))]
    exact GroupedBalancedVerifyH5Output67.setup_mem s a

theorem loaded_h5_output_safe (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial final,
      initialState program .verify input = some initial ∧
      Trace hash image initial 122 137 1 2 final ∧
      final.pc = 0x1140 ∧
      SafeFrame initial final ∧
      final.getMem 0x81048 = 0x2c720 ∧
      final.getMem 0x81000 = 0 ∧
      Low initial final := by
  obtain ⟨initial,query,loaded,queryRun,queryPC,service,src,len,dst,_,
    querySafe,queryBase,queryLow⟩ :=
    loaded_h5_query_safe hash input
  have valid : hashArgumentsValid query = true :=
    Keygen.hash_arguments query 896 src (by simpa using len) dst (by decide)
  have hlen : (hashInput query).1 = 896 := by
    simp [hashInput,len,BitVec.toNat_ofNat]
  have hcomp : compressions (hashInput query).1 = 2 := by
    rw [hlen]
    decide
  let answer := hash (hashInput query)
  let afterHash := writeHash query answer
  have hashRun : Trace hash image query 1 16 1 2 afterHash := by
    have fetched : fetch image query = some (.base .ECALL) := by
      simpa only [Keygen.fetch_at,queryPC] using h5_hash_code
    have raw := Trace.hash query afterHash 0 0 0 0 fetched service valid
      (Trace.refl afterHash)
    simpa [hcomp,afterHash] using raw
  have afterPC : afterHash.pc = 0x1114 := by
    simpa [afterHash,answer,Keygen.hash_pc,queryPC] using
      Keygen.hash_pc query answer
  obtain ⟨final,copyRun,finalPC,copySafe,copyBase,copyLow⟩ :=
    h5_copy_safe afterHash afterPC
  have all : Trace hash image initial 122 137 1 2 final := by
    simpa only [Nat.reduceAdd] using queryRun.trans (hashRun.trans copyRun.trace)
  obtain ⟨otherInitial,_,other,otherLoaded,otherRun,_,_,otherPointer⟩ :=
    GroupedBalancedVerifyH5Output67.loaded_output hash input
  have initialEq : otherInitial = initial := by
    rw [loaded] at otherLoaded
    exact Option.some.inj otherLoaded.symm
  subst otherInitial
  have finalEq : other = final := Trace.deterministic otherRun all
  subst other
  have hashBase : afterHash.getMem 0x81000 = query.getMem 0x81000 :=
    Signing.hash_answer_frame query answer dst 0x81000
      (by intro i; fin_cases i <;> decide)
  exact ⟨initial,final,loaded,all,finalPC,
    safe_trans (safe_trans querySafe (hash_safe query answer dst)) copySafe,
    otherPointer,copyBase.trans (hashBase.trans queryBase),
    queryLow.trans ((hash_low query answer dst).trans copyLow)⟩

theorem prelude_safe (s : MachineState) :
    SafeFrame s (GroupedBalancedVerifyH2Prelude67.preludeState s) := by
  constructor
  · intro a ha
    have h18 := high_ne a ha 0x81018 (by decide)
    have h510 := high_ne a ha 0x80510 (by decide)
    have h518 := high_ne a ha 0x80518 (by decide)
    simp [GroupedBalancedVerifyH2Prelude67.preludeState,execInstrBr,signExtend12,
      h18,h510,h518,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  · simp [GroupedBalancedVerifyH2Prelude67.preludeState,execInstrBr,
      MachineState.getReg_setReg_ne]

theorem prelude_low (s : MachineState) :
    Low s (GroupedBalancedVerifyH2Prelude67.preludeState s) := by
  intro a low
  have h18 := low_ne a low 0x81018 (by decide) (by decide)
  have h510 := low_ne a low 0x80510 (by decide) (by decide)
  have h518 := low_ne a low 0x80518 (by decide) (by decide)
  simp [GroupedBalancedVerifyH2Prelude67.preludeState,execInstrBr,signExtend12,
    h18,h510,h518,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,MachineState.getMem_setMem_ne]

theorem prelude_base (s : MachineState) :
    (GroupedBalancedVerifyH2Prelude67.preludeState s).getMem 0x81000 =
      s.getMem 0x81000 := by
  simp [GroupedBalancedVerifyH2Prelude67.preludeState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem loaded_h2_prelude_safe (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial final,
      initialState program .verify input = some initial ∧
      Trace hash image initial 139 154 1 2 final ∧
      final.pc = 0x1184 ∧
      SafeFrame initial final ∧
      final.getMem 0x81048 = 0x2c720 ∧
      final.getMem 0x81000 = 0 ∧
      Low initial final := by
  obtain ⟨initial,before,loaded,run,pc,safe,pointer,base,beforeLow⟩ :=
    loaded_h5_output_safe hash input
  let final := GroupedBalancedVerifyH2Prelude67.preludeState before
  have preludeRun := GroupedBalancedVerifyH2Prelude67.prelude_steps before pc pointer
  obtain ⟨_,_,ptr⟩ := GroupedBalancedVerifyH2Prelude67.prelude_sibling before pointer
  refine ⟨initial,final,loaded,?_,
    GroupedBalancedVerifyH2Prelude67.prelude_pc before pc,
    safe_trans safe (prelude_safe before),ptr,
    (prelude_base before).trans base,
    beforeLow.trans (prelude_low before)⟩
  simpa only [Nat.reduceAdd] using run.trans preludeRun.trace

private theorem h2_copy_setup_code : Keygen.CopySetupCode image 0x1184 0x510 0x20 2 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopySetupCode
  decide

private theorem h2_copy_code : Keygen.CopyCode image 0x1198 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

theorem h2_input_copy_safe (s : MachineState) (pc : s.pc = 0x1184) :
    ∃ final, OrdinarySteps image s 17 final ∧ final.pc = 0x11b0 ∧
      SafeFrame s final ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      Low s final := by
  obtain ⟨final,run,endPC,_,_,sp,frame⟩ :=
    Keygen.copy_two image 0x1184 0x510 0x20 0x80510 0x80020
      h2_copy_setup_code h2_copy_code (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) s pc
  refine ⟨final,run,by simpa using endPC,⟨?_,sp⟩,?_,?_⟩
  · intro a ha
    exact frame a (by
      intro i
      simpa [Signing.wordAddress] using
        high_ne a ha (0x80020+8*i.val) (by omega))
  · exact frame 0x81000 (by intro i; fin_cases i <;> decide)
  · intro a low
    exact frame a (by
      intro i
      simpa [Signing.wordAddress] using
        low_ne a low (0x80020+8*i.val) (by omega) (by omega))

theorem loaded_h2_copy_safe (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial final,
      initialState program .verify input = some initial ∧
      Trace hash image initial 156 171 1 2 final ∧
      final.pc = 0x11b0 ∧
      SafeFrame initial final ∧
      final.getMem 0x81048 = 0x2c720 ∧
      final.getMem 0x81000 = 0 ∧
      Low initial final := by
  obtain ⟨initial,before,loaded,run,pc,safe,_,base,beforeLow⟩ :=
    loaded_h2_prelude_safe hash input
  obtain ⟨final,copyRun,finalPC,copySafe,copyBase,copyLow⟩ :=
    h2_input_copy_safe before pc
  have all : Trace hash image initial 156 171 1 2 final := by
    simpa only [Nat.reduceAdd] using run.trans copyRun.trace
  obtain ⟨otherInitial,_,other,otherLoaded,otherRun,_,_,_,otherPointer⟩ :=
    GroupedBalancedVerifyH2InputCopy67.loaded_copy hash input
  have initialEq : otherInitial = initial := by
    rw [loaded] at otherLoaded
    exact Option.some.inj otherLoaded.symm
  subst otherInitial
  have finalEq : other = final := Trace.deterministic otherRun all
  subst other
  exact ⟨initial,final,loaded,all,finalPC,safe_trans safe copySafe,
    otherPointer,copyBase.trans base,beforeLow.trans copyLow⟩

theorem h2_entry_safe (s : MachineState) :
    SafeFrame s (GroupedBalancedVerifyH2Entry67.setupState s) := by
  constructor
  · intro a ha
    have h00 := high_ne a ha 0x80000 (by decide)
    have h08 := high_ne a ha 0x80008 (by decide)
    have h10 := high_ne a ha 0x80010 (by decide)
    have h18 := high_ne a ha 0x80018 (by decide)
    simp [GroupedBalancedVerifyH2Entry67.setupState,execInstrBr,signExtend12,
      h00,h08,h10,h18,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  · simp [GroupedBalancedVerifyH2Entry67.setupState,execInstrBr,
      MachineState.getReg_setReg_ne]

theorem h2_entry_low (s : MachineState) :
    Low s (GroupedBalancedVerifyH2Entry67.setupState s) := by
  intro a low
  have h00 := low_ne a low 0x80000 (by decide) (by decide)
  have h08 := low_ne a low 0x80008 (by decide) (by decide)
  have h10 := low_ne a low 0x80010 (by decide) (by decide)
  have h18 := low_ne a low 0x80018 (by decide) (by decide)
  simp [GroupedBalancedVerifyH2Entry67.setupState,execInstrBr,signExtend12,
    h00,h08,h10,h18,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,MachineState.getMem_setMem_ne]

theorem h2_entry_base (s : MachineState) :
    (GroupedBalancedVerifyH2Entry67.setupState s).getMem 0x81000 =
      s.getMem 0x81000 := by
  simp [GroupedBalancedVerifyH2Entry67.setupState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem loaded_h2_query_safe (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial query,
      initialState program .verify input = some initial ∧
      Trace hash image initial 189 204 1 2 query ∧
      query.pc = 0x1234 ∧
      query.getReg .x5 = 1 ∧
      query.getReg .x10 = 0x80000 ∧
      query.getReg .x11 = 384 ∧
      query.getReg .x12 = 0x80300 ∧
      SafeFrame initial query ∧
      query.getMem 0x81000 = 0 ∧
      Low initial query := by
  obtain ⟨initial,before,loaded,run,pc,safe,_,base,beforeLow⟩ :=
    loaded_h2_copy_safe hash input
  let query := GroupedBalancedVerifyH2Entry67.setupState before
  have setupRun := GroupedBalancedVerifyH2Entry67.setup_steps before pc
  obtain ⟨service,src,len,dst⟩ := GroupedBalancedVerifyH2Entry67.setup_regs before
  refine ⟨initial,query,loaded,?_,
    GroupedBalancedVerifyH2Entry67.setup_pc before pc,
    service,src,len,dst,safe_trans safe (h2_entry_safe before),
    (h2_entry_base before).trans base,
    beforeLow.trans (h2_entry_low before)⟩
  simpa only [Nat.reduceAdd] using run.trans setupRun.trace

private theorem h2_hash_code : Keygen.instructionAt image 0x1234 = some (.base .ECALL) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

private theorem h2_answer_setup_code : Keygen.CopySetupCode image 0x1238 0x300 0x500 2 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopySetupCode
  decide

private theorem h2_answer_copy_code : Keygen.CopyCode image 0x124c := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

theorem h2_answer_copy_safe (s : MachineState) (pc : s.pc = 0x1238) :
    ∃ final, OrdinarySteps image s 17 final ∧ final.pc = 0x1264 ∧
      SafeFrame s final ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      Low s final := by
  obtain ⟨final,run,endPC,_,_,sp,frame⟩ :=
    Keygen.copy_two image 0x1238 0x300 0x500 0x80300 0x80500
      h2_answer_setup_code h2_answer_copy_code (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) s pc
  refine ⟨final,run,by simpa using endPC,⟨?_,sp⟩,?_,?_⟩
  · intro a ha
    exact frame a (by
      intro i
      simpa [Signing.wordAddress] using
        high_ne a ha (0x80500+8*i.val) (by omega))
  · exact frame 0x81000 (by intro i; fin_cases i <;> decide)
  · intro a low
    exact frame a (by
      intro i
      simpa [Signing.wordAddress] using
        low_ne a low (0x80500+8*i.val) (by omega) (by omega))

theorem loaded_h2_output_safe (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial final,
      initialState program .verify input = some initial ∧
      Trace hash image initial 207 229 2 3 final ∧
      final.pc = 0x1264 ∧
      SafeFrame initial final ∧
      final.getMem 0x81048 = 0x2c720 ∧
      final.getMem 0x81000 = 0 ∧
      Low initial final := by
  obtain ⟨initial,query,loaded,run,pc,service,src,len,dst,safe,base,
    queryLow⟩ :=
    loaded_h2_query_safe hash input
  have valid : hashArgumentsValid query = true :=
    Keygen.hash_arguments query 384 src (by simpa using len) dst (by decide)
  have hlen : (hashInput query).1 = 384 := by
    simp [hashInput,len,BitVec.toNat_ofNat]
  have hcomp : compressions (hashInput query).1 = 1 := by
    rw [hlen]
    decide
  let answer := hash (hashInput query)
  let afterHash := writeHash query answer
  have hashRun : Trace hash image query 1 8 1 1 afterHash := by
    have fetched : fetch image query = some (.base .ECALL) := by
      simpa only [Keygen.fetch_at,pc] using h2_hash_code
    have raw := Trace.hash query afterHash 0 0 0 0 fetched service valid
      (Trace.refl afterHash)
    simpa [hcomp,afterHash] using raw
  have afterPC : afterHash.pc = 0x1238 := by
    simpa [afterHash,answer,Keygen.hash_pc,pc] using
      Keygen.hash_pc query answer
  obtain ⟨final,copyRun,finalPC,copySafe,copyBase,copyLow⟩ :=
    h2_answer_copy_safe afterHash afterPC
  have all : Trace hash image initial 207 229 2 3 final := by
    simpa only [Nat.reduceAdd] using run.trans (hashRun.trans copyRun.trace)
  obtain ⟨otherInitial,_,other,otherLoaded,otherRun,_,_,otherPointer⟩ :=
    GroupedBalancedVerifyH2Loaded67.loaded_output hash input
  have initialEq : otherInitial = initial := by
    rw [loaded] at otherLoaded
    exact Option.some.inj otherLoaded.symm
  subst otherInitial
  have finalEq : other = final := Trace.deterministic otherRun all
  subst other
  have hashBase : afterHash.getMem 0x81000 = query.getMem 0x81000 :=
    Signing.hash_answer_frame query answer dst 0x81000
      (by intro i; fin_cases i <;> decide)
  exact ⟨initial,final,loaded,all,finalPC,
    safe_trans (safe_trans safe (hash_safe query answer dst)) copySafe,
    otherPointer,copyBase.trans (hashBase.trans base),
    queryLow.trans ((hash_low query answer dst).trans copyLow)⟩

theorem tree_start_safe (s : MachineState) :
    SafeFrame s (GroupedBalancedVerifyTreeStart67.startState s) := by
  constructor
  · intro a ha
    have h48 := high_ne a ha 0x81048 (by decide)
    have h50 := high_ne a ha 0x81050 (by decide)
    simp [GroupedBalancedVerifyTreeStart67.startState,execInstrBr,signExtend12,
      h48,h50,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  · simp [GroupedBalancedVerifyTreeStart67.startState,execInstrBr,
      MachineState.getReg_setReg_ne]

theorem tree_start_low (s : MachineState) :
    Low s (GroupedBalancedVerifyTreeStart67.startState s) := by
  intro a low
  have h48 := low_ne a low 0x81048 (by decide) (by decide)
  have h50 := low_ne a low 0x81050 (by decide) (by decide)
  simp [GroupedBalancedVerifyTreeStart67.startState,execInstrBr,signExtend12,
    h48,h50,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,MachineState.getMem_setMem_ne]

theorem tree_start_base (s : MachineState) :
    (GroupedBalancedVerifyTreeStart67.startState s).getMem 0x81000 =
      s.getMem 0x81000 := by
  simp [GroupedBalancedVerifyTreeStart67.startState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem loaded_tree_start_safe (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial final,
      initialState program .verify input = some initial ∧
      Trace hash image initial 218 240 2 3 final ∧
      final.pc = 0x1290 ∧
      SafeFrame initial final ∧
      final.getMem 0x81048 = 0x2c730 ∧
      final.getMem 0x81050 = 0 ∧
      final.getMem 0x81000 = 0 ∧
      Low initial final := by
  obtain ⟨initial,before,loaded,run,pc,safe,pointer,base,beforeLow⟩ :=
    loaded_h2_output_safe hash input
  have startRun := GroupedBalancedVerifyTreeStart67.start_steps before pc
  obtain ⟨ptr,count⟩ := GroupedBalancedVerifyTreeStart67.start_controls before pointer
  refine ⟨initial,GroupedBalancedVerifyTreeStart67.startState before,
    loaded,?_,GroupedBalancedVerifyTreeStart67.start_pc before pc,
    safe_trans safe (tree_start_safe before),ptr,count,
    (tree_start_base before).trans base,
    beforeLow.trans (tree_start_low before)⟩
  simpa only [Nat.reduceAdd] using run.trans startRun.trace

end SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreePrefixSafe67
