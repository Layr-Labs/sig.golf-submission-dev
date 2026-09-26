import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsAfterSeed67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenOddSeed67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenEvenSeedRun67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenCacheTick67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsSeed67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsFullChain67. -/
section
/-! Both H1 seed paths preserve the two high tree-address words. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsSeed67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenRootControlsTick67
open GroupedBalancedKeygenCacheTick67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image
private abbrev branch := GroupedBalancedKeygenBranch67.branchState

theorem odd_seed_control (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x1050)
    (odd : s.getMem 0x81030 &&& 1 ≠ 0)
    (trace : Trace hash image s 26 26 0 0 final) :
    ControlFrame s final ∧ LowFrame s final := by
  let selected := branch s
  have first := GroupedBalancedKeygenBranch67.branch_steps s pc
  have selectedPC := GroupedBalancedKeygenOddSeed67.branch_odd_pc s pc odd
  let jumped := GroupedBalancedKeygenOddSeed67.jumpState selected
  have second := GroupedBalancedKeygenOddSeed67.jump_steps selected selectedPC
  have jumpedPC := GroupedBalancedKeygenOddSeed67.jump_pc selected selectedPC
  have jumpedOdd : jumped.getReg .x19 &&& 1 ≠ 0 := by
    rw [GroupedBalancedKeygenOddSeed67.jump_x19,
      GroupedBalancedKeygenOddSeed67.branch_x19]
    exact odd
  let leafBranch := GroupedBalancedKeygenFirstLeaf67.branchState jumped
  have third := GroupedBalancedKeygenFirstLeaf67.branch_steps jumped jumpedPC
  have leafPC := GroupedBalancedKeygenOddSeed67.leaf_odd_pc jumped jumpedPC jumpedOdd
  let ready := GroupedBalancedKeygenOddSeed67.setupState leafBranch
  have fourth := GroupedBalancedKeygenOddSeed67.setup_steps leafBranch leafPC
  obtain ⟨readyPC,readySrc,readyDst,readyCount,_⟩ :=
    GroupedBalancedKeygenOddSeed67.setup_fields leafBranch leafPC
  have inv : Keygen.CopyInvariant 0x1190 0x80d10 0x80020 2 2 ready := by
    refine ⟨by decide,by decide,?_,readySrc,readyDst,readyCount⟩
    simpa [ready] using readyPC
  obtain ⟨copied,fifth,done,_,frame,_⟩ :=
    KeygenCopyX19.copy_all_x19 image 0x1190
      GroupedBalancedKeygenOddSeed67.copy_code
      0x80d10 0x80020 2 ready inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have copiedPC : copied.pc = 0x11a8 := by
    simpa [Keygen.CopyInvariant] using done.2.2.1
  let made := GroupedBalancedKeygenOddSeed67.finishState copied
  have sixth := GroupedBalancedKeygenOddSeed67.finish_steps copied copiedPC
  have path0 : OrdinarySteps image s 6 jumped :=
    Keygen.ordinary_trans image s selected jumped 5 1 first second
  have path1 : OrdinarySteps image s 8 leafBranch :=
    Keygen.ordinary_trans image s jumped leafBranch 6 2 path0 third
  have path2 : OrdinarySteps image s 13 ready :=
    Keygen.ordinary_trans image s leafBranch ready 8 5 path1 fourth
  have path3 : OrdinarySteps image s 25 copied :=
    Keygen.ordinary_trans image s ready copied 13 12 path2 fifth
  have path4 : OrdinarySteps image s 26 made :=
    Keygen.ordinary_trans image s copied made 25 1 path3 sixth
  have same : final = made := Trace.deterministic trace path4.trace
  rw [same]
  have one (a : Word) (ha : a = 0x81010 ∨ a = 0x81018) :
      made.getMem a = s.getMem a := by
    have outside : ∀ i, i < 2 → a ≠ Signing.wordAddress 0x80020 i := by
      intro i hi eq
      rcases ha with rfl | rfl
      · interval_cases i <;> simp [Signing.wordAddress] at eq
      · interval_cases i <;> simp [Signing.wordAddress] at eq
    rw [GroupedBalancedKeygenOddSeed67.finish_mem,
      frame a outside,
      GroupedBalancedKeygenOddSeed67.setup_mem,
      GroupedBalancedKeygenFirstLeaf67.branch_mem,
      GroupedBalancedKeygenOddSeed67.jump_mem,
      GroupedBalancedKeygenBranch67.branch_mem]
  refine ⟨⟨one 0x81010 (Or.inl rfl),one 0x81018 (Or.inr rfl)⟩,?_⟩
  intro a safeAddress
  have outside : ∀ i, i < 2 → a ≠ Signing.wordAddress 0x80020 i := by
    intro i hi
    simpa only [Signing.wordAddress] using
      protected_ne a safeAddress (0x80020+8*i)
        (by omega) (by omega) (by omega)
  rw [GroupedBalancedKeygenOddSeed67.finish_mem,
    frame a outside,
    GroupedBalancedKeygenOddSeed67.setup_mem,
    GroupedBalancedKeygenFirstLeaf67.branch_mem,
    GroupedBalancedKeygenOddSeed67.jump_mem,
    GroupedBalancedKeygenBranch67.branch_mem]

theorem even_copy_control (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x1174)
    (even : s.getReg .x19 &&& 1 = 0)
    (trace : OrdinarySteps image s 19 final) :
    ControlFrame s final ∧ LowFrame s final := by
  let selected := GroupedBalancedKeygenFirstLeaf67.branchState s
  have first := GroupedBalancedKeygenFirstLeaf67.branch_steps s pc
  have selectedPC := GroupedBalancedKeygenEvenSeedAny67.branch_even_pc s pc even
  let ready := GroupedBalancedKeygenFirstLeaf67.setupState selected
  have second := GroupedBalancedKeygenFirstLeaf67.setup_steps selected selectedPC
  obtain ⟨readyPC,readySrc,readyDst,readyCount,_⟩ :=
    GroupedBalancedKeygenFirstLeaf67.setup_fields selected selectedPC
  have inv : Keygen.CopyInvariant 0x11c0 0x80d00 0x80020 2 2 ready := by
    refine ⟨by decide,by decide,?_,readySrc,readyDst,readyCount⟩
    simpa [ready] using readyPC
  obtain ⟨made,third,_,_,frame,_⟩ :=
    KeygenCopyX19.copy_all_x19 image 0x11c0
      GroupedBalancedKeygenFirstLeaf67.copy_code
      0x80d00 0x80020 2 ready inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have path : OrdinarySteps image s 19 made := by
    have early : OrdinarySteps image s 7 ready :=
      Keygen.ordinary_trans image s selected ready 2 5 first second
    simpa only [Nat.reduceMul,Nat.reduceAdd] using
      Keygen.ordinary_trans image s ready made 7 (6*2) early third
  have same : final = made := by
    exact Trace.deterministic (trace.trace (hash := hash))
      (path.trace (hash := hash))
  rw [same]
  have one (a : Word) (ha : a = 0x81010 ∨ a = 0x81018) :
      made.getMem a = s.getMem a := by
    have outside : ∀ i, i < 2 → a ≠ Signing.wordAddress 0x80020 i := by
      intro i hi eq
      rcases ha with rfl | rfl
      · interval_cases i <;> simp [Signing.wordAddress] at eq
      · interval_cases i <;> simp [Signing.wordAddress] at eq
    rw [frame a outside,
      GroupedBalancedKeygenFirstLeaf67.setup_mem,
      GroupedBalancedKeygenFirstLeaf67.branch_mem]
  refine ⟨⟨one 0x81010 (Or.inl rfl),one 0x81018 (Or.inr rfl)⟩,?_⟩
  intro a safeAddress
  have outside : ∀ i, i < 2 → a ≠ Signing.wordAddress 0x80020 i := by
    intro i hi
    simpa only [Signing.wordAddress] using
      protected_ne a safeAddress (0x80020+8*i)
        (by omega) (by omega) (by omega)
  rw [frame a outside,
    GroupedBalancedKeygenFirstLeaf67.setup_mem,
    GroupedBalancedKeygenFirstLeaf67.branch_mem]

theorem even_seed_control (hash : Hash) (s final : MachineState) (n : Nat)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n)
    (even : s.getMem 0x81030 &&& 1 = 0)
    (level : s.getMem 0x81000 = 156)
    (trace : Trace hash image s 127 134 1 1 final) :
    ControlFrame s final ∧ LowFrame s final := by
  let selected := branch s
  have first := GroupedBalancedKeygenBranch67.branch_steps s pc
  have selectedPC := GroupedBalancedKeygenEvenSeedRun67.branch_even_pc s pc even
  let copiedSecret := GroupedBalancedKeygenSecretCopy67.prepareState selected
  obtain ⟨copied,second,copiedPC,_,copyFrame,copiedX19⟩ :=
    GroupedBalancedKeygenSecretCopy67.secret_copy_frame selected selectedPC
  have copiedLevel : copied.getMem 0x81000 = 156 := by
    rw [copyFrame 0x81000 (by intro i hi; interval_cases i <;> decide),
      GroupedBalancedKeygenSecretCopy67.prepare_mem_other selected 0x81000 (by decide),
      GroupedBalancedKeygenBranch67.branch_mem]
    exact level
  let ready := GroupedBalancedKeygenFirstHash67.preHashState copied
  have third : OrdinarySteps image copied 38 ready := by
    simpa only [image,GroupedBalancedKeygenFirstHash67.image,ready] using
      GroupedBalancedKeygenFirstHash67.pre_hash_steps_any
        copied copiedPC copiedLevel
  have readyPC := GroupedBalancedKeygenFirstHashFields67.pre_hash_pc copied copiedPC
  obtain ⟨service,source,bits,destination⟩ :=
    GroupedBalancedKeygenFirstHashFields67.pre_hash_regs copied
  have code : fetch image ready = some (.base .ECALL) := by
    have hc : Keygen.instructionAt image 0x1138 = some (.base .ECALL) := by
      unfold image GroupedBalancedKeygenImage67.image
      decide
    change Keygen.instructionAt image ready.pc = some (.base .ECALL)
    rw [readyPC]
    exact hc
  let hashed := writeHash ready (hash (hashInput ready))
  have fourth : Trace hash image ready 1 8 1 1 hashed :=
    KeygenDomain.secret_hash_trace image hash ready code
      service source bits destination
  have hashedPC : hashed.pc = 0x113c := by
    change ready.pc + 4 = 0x113c
    rw [show ready.pc = 0x1138 from readyPC]
    decide
  obtain ⟨cached,fifth,cachedPC,_,cacheFrame,cachedX19⟩ :=
    GroupedBalancedKeygenStoreSeed67.copy_seed hashed hashedPC
  have cachedIndex : cached.getReg .x19 = BitVec.ofNat 64 n := by
    rw [cachedX19,Keygen.hash_registers,
      GroupedBalancedKeygenFirstHashFields67.pre_hash_x19,copiedX19,
      GroupedBalancedKeygenOddSeed67.branch_x19,counter]
  have cachedEven : cached.getReg .x19 &&& 1 = 0 := by
    rw [cachedIndex,← counter]
    exact even
  obtain ⟨made,sixth,_,_,_,_,_,_⟩ :=
    GroupedBalancedKeygenEvenSeedAny67.even_seed_copy
      cached cachedPC cachedEven
  have path0 : Trace hash image s 37 37 0 0 copied := by
    simpa only [image,GroupedBalancedKeygenBranch67.image,
      GroupedBalancedKeygenSecretCopy67.image,Nat.reduceAdd] using
      (first.trace (hash := hash)).trans (second.trace (hash := hash))
  have path1 : Trace hash image s 75 75 0 0 ready := by
    simpa only [Nat.reduceAdd] using path0.trans (third.trace (hash := hash))
  have path2 : Trace hash image s 76 83 1 1 hashed := by
    simpa only [Nat.reduceAdd] using path1.trans fourth
  have path3 : Trace hash image s 108 115 1 1 cached := by
    simpa only [image,GroupedBalancedKeygenStoreSeed67.image,
      Nat.reduceAdd] using path2.trans (fifth.trace (hash := hash))
  have total : Trace hash image s 127 134 1 1 made := by
    simpa only [Nat.reduceAdd] using
      path3.trans (sixth.trace (hash := hash))
  have same : final = made := Trace.deterministic trace total
  rw [same]
  have copiedOne (a : Word) (ha : a = 0x81010 ∨ a = 0x81018) :
      copied.getMem a = s.getMem a := by
    rw [copyFrame a (by
      intro i hi eq
      rcases ha with rfl | rfl
      · interval_cases i <;> simp [Signing.wordAddress] at eq
      · interval_cases i <;> simp [Signing.wordAddress] at eq),
      GroupedBalancedKeygenSecretCopy67.prepare_mem_other selected a (by
        rcases ha with rfl | rfl <;> decide),
      GroupedBalancedKeygenBranch67.branch_mem]
  have readyOne (a : Word) (ha : a = 0x81010 ∨ a = 0x81018) :
      ready.getMem a = copied.getMem a := by
    rcases ha with rfl | rfl <;>
      simp [ready,GroupedBalancedKeygenFirstHashMemory67.pre_hash_mem]
  have hashedOne (a : Word) (ha : a = 0x81010 ∨ a = 0x81018) :
      hashed.getMem a = ready.getMem a := by
    apply Signing.hash_answer_frame ready (hash (hashInput ready)) destination
    intro i eq
    rcases ha with rfl | rfl <;> fin_cases i <;>
      simp [Signing.wordAddress] at eq
  have cachedOne (a : Word) (ha : a = 0x81010 ∨ a = 0x81018) :
      cached.getMem a = hashed.getMem a := by
    rw [cacheFrame a (by
      intro i hi eq
      rcases ha with rfl | rfl
      · interval_cases i <;> simp [Signing.wordAddress] at eq
      · interval_cases i <;> simp [Signing.wordAddress] at eq),
      GroupedBalancedKeygenStoreSeed67.setup_mem_other hashed a (by
        rcases ha with rfl | rfl <;> decide)]
  have one (a : Word) (ha : a = 0x81010 ∨ a = 0x81018)
      (finish : made.getMem a = cached.getMem a) :
      made.getMem a = s.getMem a :=
    finish.trans ((cachedOne a ha).trans
      ((hashedOne a ha).trans ((readyOne a ha).trans (copiedOne a ha))))
  have last := even_copy_control hash cached made cachedPC cachedEven sixth
  refine ⟨⟨one 0x81010 (Or.inl rfl) last.1.1,
    one 0x81018 (Or.inr rfl) last.1.2⟩,?_⟩
  intro a safeAddress
  have copiedSafe : copied.getMem a = s.getMem a := by
    rw [copyFrame a (by
      intro i hi
      simpa only [Signing.wordAddress] using
        protected_ne a safeAddress (0x80020+8*i)
          (by omega) (by omega) (by omega)),
      GroupedBalancedKeygenSecretCopy67.prepare_mem_other selected a (by
        exact protected_ne a safeAddress 0x81030
          (by decide) (by decide) (by decide)),
      GroupedBalancedKeygenBranch67.branch_mem]
  have readySafe : ready.getMem a = copied.getMem a := by
    have ne0 : a ≠ (0x80000 : Word) := protected_ne a safeAddress 0x80000
      (by decide) (by decide) (by decide)
    have ne1 : a ≠ (0x80008 : Word) := protected_ne a safeAddress 0x80008
      (by decide) (by decide) (by decide)
    have ne2 : a ≠ (0x80010 : Word) := protected_ne a safeAddress 0x80010
      (by decide) (by decide) (by decide)
    have ne3 : a ≠ (0x80018 : Word) := protected_ne a safeAddress 0x80018
      (by decide) (by decide) (by decide)
    simp only [ready,GroupedBalancedKeygenFirstHashMemory67.pre_hash_mem,
      if_neg ne3,if_neg ne2,if_neg ne1,if_neg ne0]
  have hashedSafe : hashed.getMem a = ready.getMem a := by
    apply Signing.hash_answer_frame ready (hash (hashInput ready)) destination
    intro i
    simpa only [Signing.wordAddress] using
      protected_ne a safeAddress (0x80300+8*i.val)
        (by omega) (by have := i.isLt; omega)
        (by have := i.isLt; omega)
  have cachedSafe : cached.getMem a = hashed.getMem a := by
    rw [cacheFrame a (by
      intro i hi
      simpa only [Signing.wordAddress] using
        protected_ne a safeAddress (0x80d00+8*i)
          (by omega) (by omega) (by omega)),
      GroupedBalancedKeygenStoreSeed67.setup_mem_other hashed a (by
        exact protected_ne a safeAddress 0x81030
          (by decide) (by decide) (by decide))]
  exact (last.2 a safeAddress).trans
    (cachedSafe.trans (hashedSafe.trans (readySafe.trans copiedSafe)))

#print axioms odd_seed_control
#print axioms even_seed_control
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsSeed67

end

/-! Both keygen H1 paths followed by H2 preserve the high address words. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsFullChain67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenRootControlsTick67
open GroupedBalancedKeygenRootControlsAfterSeed67
open GroupedBalancedKeygenRootControlsSeed67
open GroupedBalancedKeygenCacheTick67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem regular_even_control (hash : Hash) (s final : MachineState) (n : Nat)
    (pc : s.pc = 0x1050) (small : n < 65)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n)
    (even : s.getMem 0x81030 &&& 1 = 0)
    (level : s.getMem 0x81000 = 156)
    (trace : Trace hash image s 213 241 4 4 final) :
    ControlFrame s final ∧ LowFrame s final := by
  obtain ⟨ready,seedTrace,readyPC,readyIndex,readyCounter,_,_⟩ :=
    GroupedBalancedKeygenEvenSeedRun67.even_seed_from_entry
      hash s n pc counter even level
  have seedFrames := even_seed_control hash s ready n pc counter even level seedTrace
  have full : Trace hash image s (127+86) (134+107) (1+3) (1+3) final := by
    simpa only [Nat.reduceAdd] using trace
  exact ⟨regular_after_seed hash s ready final n 127 134 1 1 small
      seedTrace seedFrames.1 readyPC readyCounter readyIndex full,
    regular_after_seed_low hash s ready final n 127 134 1 1 small
      seedTrace seedFrames.2 readyPC readyCounter readyIndex full⟩

theorem regular_odd_control (hash : Hash) (s final : MachineState) (n : Nat)
    (pc : s.pc = 0x1050) (small : n < 65)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n)
    (odd : s.getMem 0x81030 &&& 1 ≠ 0)
    (trace : Trace hash image s 112 133 3 3 final) :
    ControlFrame s final ∧ LowFrame s final := by
  obtain ⟨ready,seedTrace,readyPC,readyIndex,readyCounter,_,_⟩ :=
    GroupedBalancedKeygenOddSeed67.odd_seed_from_entry hash s pc odd
  have seedFrames := odd_seed_control hash s ready pc odd seedTrace
  have full : Trace hash image s (26+86) (26+107) (0+3) (0+3) final := by
    simpa only [Nat.reduceAdd] using trace
  exact ⟨regular_after_seed hash s ready final n 26 26 0 0 small
      seedTrace seedFrames.1 readyPC (readyCounter.trans counter)
      (readyIndex.trans counter) full,
    regular_after_seed_low hash s ready final n 26 26 0 0 small
      seedTrace seedFrames.2 readyPC (readyCounter.trans counter)
      (readyIndex.trans counter) full⟩

theorem special65_control (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 65#64)
    (odd : s.getMem 0x81030 &&& 1 ≠ 0)
    (trace : Trace hash image s 131 187 8 8 final) :
    ControlFrame s final ∧ LowFrame s final := by
  obtain ⟨ready,seedTrace,readyPC,readyIndex,readyCounter,_,_⟩ :=
    GroupedBalancedKeygenOddSeed67.odd_seed_from_entry hash s pc odd
  have seedFrames := odd_seed_control hash s ready pc odd seedTrace
  have full : Trace hash image s (26+105) (26+161) (0+8) (0+8) final := by
    simpa only [Nat.reduceAdd] using trace
  exact ⟨special65_after_seed hash s ready final 26 26 0 0
      seedTrace seedFrames.1 readyPC (readyCounter.trans counter)
      (readyIndex.trans counter) full,
    special65_after_seed_low hash s ready final 26 26 0 0
      seedTrace seedFrames.2 readyPC (readyCounter.trans counter)
      (readyIndex.trans counter) full⟩

theorem special66_control (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 66#64)
    (even : s.getMem 0x81030 &&& 1 = 0)
    (level : s.getMem 0x81000 = 156)
    (trace : Trace hash image s 241 318 11 11 final) :
    ControlFrame s final ∧ LowFrame s final := by
  obtain ⟨ready,seedTrace,readyPC,readyIndex,readyCounter,_,_⟩ :=
    GroupedBalancedKeygenEvenSeedRun67.even_seed_from_entry
      hash s 66 pc counter even level
  have seedFrames := even_seed_control hash s ready 66 pc counter even level seedTrace
  have full : Trace hash image s (127+114) (134+184) (1+10) (1+10) final := by
    simpa only [Nat.reduceAdd] using trace
  exact ⟨special66_after_seed hash s ready final 127 134 1 1
      seedTrace seedFrames.1 readyPC readyCounter readyIndex full,
    special66_after_seed_low hash s ready final 127 134 1 1
      seedTrace seedFrames.2 readyPC readyCounter readyIndex full⟩

#print axioms regular_even_control
#print axioms regular_odd_control
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsFullChain67
