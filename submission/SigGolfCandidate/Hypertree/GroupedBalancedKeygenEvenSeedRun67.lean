import SigGolfCandidate.Hypertree.GroupedBalancedKeygenOddSeed67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstHashFields67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenStoreSeed67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenEvenSeedAny67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenEvenSeedRun67. -/
section
/-! The even-chain seed copy works at every even direct67 chain index. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenEvenSeedAny67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image
private abbrev branch := GroupedBalancedKeygenFirstLeaf67.branchState
private abbrev setup := GroupedBalancedKeygenFirstLeaf67.setupState

theorem branch_even_pc (s : MachineState) (pc : s.pc = 0x1174)
    (even : s.getReg .x19 &&& 1 = 0) :
    (branch s).pc = 0x11ac := by
  simp [branch,GroupedBalancedKeygenFirstLeaf67.branchState,
    execInstrBr,signExtend12,signExtend13,pc,even,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact even

theorem even_seed_copy (s : MachineState) (pc : s.pc = 0x1174)
    (even : s.getReg .x19 &&& 1 = 0) :
    ∃ final, OrdinarySteps image s 19 final ∧
      final.pc = 0x11d8 ∧
      final.getReg .x19 = s.getReg .x19 ∧
      final.getMem 0x81030 = s.getMem 0x81030 ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      final.getMem 0x81008 = s.getMem 0x81008 ∧
      (∀ i, i < 2 → final.getMem (Signing.wordAddress 0x80020 i) =
        s.getMem (Signing.wordAddress 0x80d00 i)) := by
  let selected := branch s
  have first := GroupedBalancedKeygenFirstLeaf67.branch_steps s pc
  have selectedPC := branch_even_pc s pc even
  let ready := setup selected
  have second := GroupedBalancedKeygenFirstLeaf67.setup_steps selected selectedPC
  obtain ⟨readyPC,readySrc,readyDst,readyCount,readyX19⟩ :=
    GroupedBalancedKeygenFirstLeaf67.setup_fields selected selectedPC
  have inv : Keygen.CopyInvariant 0x11c0 0x80d00 0x80020 2 2 ready := by
    refine ⟨by decide,by decide,?_,readySrc,readyDst,readyCount⟩
    simpa [ready] using readyPC
  obtain ⟨final,third,done,words,frame,copyX19⟩ :=
    KeygenCopyX19.copy_all_x19 image 0x11c0
      GroupedBalancedKeygenFirstLeaf67.copy_code
      0x80d00 0x80020 2 ready inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have finalPC : final.pc = 0x11d8 := by
    simpa [Keygen.CopyInvariant] using done.2.2.1
  have finalX19 : final.getReg .x19 = s.getReg .x19 := by
    rw [copyX19,readyX19,GroupedBalancedKeygenOddSeed67.leaf_x19]
  have finalCounter : final.getMem 0x81030 = s.getMem 0x81030 := by
    rw [frame 0x81030 (by intro i hi; interval_cases i <;> decide),
      GroupedBalancedKeygenFirstLeaf67.setup_mem,
      GroupedBalancedKeygenFirstLeaf67.branch_mem]
  have finalLevel : final.getMem 0x81000 = s.getMem 0x81000 := by
    rw [frame 0x81000 (by intro i hi; interval_cases i <;> decide),
      GroupedBalancedKeygenFirstLeaf67.setup_mem,
      GroupedBalancedKeygenFirstLeaf67.branch_mem]
  have finalLeaf : final.getMem 0x81008 = s.getMem 0x81008 := by
    rw [frame 0x81008 (by intro i hi; interval_cases i <;> decide),
      GroupedBalancedKeygenFirstLeaf67.setup_mem,
      GroupedBalancedKeygenFirstLeaf67.branch_mem]
  have finalWords (i : Nat) (hi : i < 2) :
      final.getMem (Signing.wordAddress 0x80020 i) =
        s.getMem (Signing.wordAddress 0x80d00 i) := by
    rw [words i hi,GroupedBalancedKeygenFirstLeaf67.setup_mem,
      GroupedBalancedKeygenFirstLeaf67.branch_mem]
  have path := Keygen.ordinary_trans image s selected ready 2 5 first second
  refine ⟨final,?_,finalPC,finalX19,finalCounter,finalLevel,finalLeaf,finalWords⟩
  simpa only [Nat.reduceMul,Nat.reduceAdd] using
    Keygen.ordinary_trans image s ready final 7 (6*2) path third

#print axioms branch_even_pc
#print axioms even_seed_copy

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenEvenSeedAny67

end

/-! Uniform H1 plus paired-seed path for every even direct67 keygen chain. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenEvenSeedRun67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image
private abbrev branch := GroupedBalancedKeygenBranch67.branchState

theorem branch_even_pc (s : MachineState) (pc : s.pc = 0x1050)
    (even : s.getMem 0x81030 &&& 1 = 0) :
    (branch s).pc = 0x1068 := by
  simp [branch,GroupedBalancedKeygenBranch67.branchState,
    execInstrBr,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact even

theorem even_seed_from_entry (hash : Hash) (s : MachineState) (n : Nat)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n)
    (even : s.getMem 0x81030 &&& 1 = 0)
    (level : s.getMem 0x81000 = 156) :
    ∃ final,
      Trace hash image s 127 134 1 1 final ∧
      final.pc = 0x11d8 ∧
      final.getReg .x19 = BitVec.ofNat 64 n ∧
      final.getMem 0x81030 = BitVec.ofNat 64 n ∧
      final.getMem 0x81000 = 156 ∧
      final.getMem 0x81008 = s.getMem 0x81008 := by
  let selected := branch s
  have first := GroupedBalancedKeygenBranch67.branch_steps s pc
  have selectedPC := branch_even_pc s pc even
  have selectedX19 := GroupedBalancedKeygenOddSeed67.branch_x19 s
  let copiedSecret := GroupedBalancedKeygenSecretCopy67.prepareState selected
  obtain ⟨copied,second,copiedPC,_,copyFrame,copiedX19⟩ :=
    GroupedBalancedKeygenSecretCopy67.secret_copy_frame selected selectedPC
  have copiedLevel : copied.getMem 0x81000 = 156 := by
    rw [copyFrame 0x81000 (by intro i hi; interval_cases i <;> decide),
      GroupedBalancedKeygenSecretCopy67.prepare_mem_other selected 0x81000 (by decide),
      GroupedBalancedKeygenBranch67.branch_mem]
    exact level
  have copiedLeaf : copied.getMem 0x81008 = s.getMem 0x81008 := by
    rw [copyFrame 0x81008 (by intro i hi; interval_cases i <;> decide),
      GroupedBalancedKeygenSecretCopy67.prepare_mem_other selected 0x81008 (by decide),
      GroupedBalancedKeygenBranch67.branch_mem]
  let ready := GroupedBalancedKeygenFirstHash67.preHashState copied
  have readyLevel : ready.getMem 0x81000 = 156 := by
    simpa [ready,GroupedBalancedKeygenFirstHashMemory67.pre_hash_mem]
      using copiedLevel
  have readyLeaf : ready.getMem 0x81008 = s.getMem 0x81008 := by
    rw [GroupedBalancedKeygenFirstHashMemory67.pre_hash_mem]
    exact copiedLeaf
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
  have hashedLevel : hashed.getMem 0x81000 = 156 := by
    rw [Signing.hash_answer_frame ready (hash (hashInput ready))
      destination 0x81000 (by intro i; fin_cases i <;> decide)]
    exact readyLevel
  have hashedLeaf : hashed.getMem 0x81008 = s.getMem 0x81008 := by
    rw [Signing.hash_answer_frame ready (hash (hashInput ready))
      destination 0x81008 (by intro i; fin_cases i <;> decide)]
    exact readyLeaf
  have fourth : Trace hash image ready 1 8 1 1 hashed :=
    KeygenDomain.secret_hash_trace image hash ready code
      service source bits destination
  have hashedPC : hashed.pc = 0x113c := by
    change ready.pc + 4 = 0x113c
    rw [show ready.pc = 0x1138 from readyPC]
    decide
  obtain ⟨cached,fifth,cachedPC,_,cacheFrame,cachedX19⟩ :=
    GroupedBalancedKeygenStoreSeed67.copy_seed hashed hashedPC
  have cachedLevel : cached.getMem 0x81000 = 156 := by
    rw [cacheFrame 0x81000 (by intro i hi; interval_cases i <;> decide),
      GroupedBalancedKeygenStoreSeed67.setup_mem_other hashed 0x81000 (by decide)]
    exact hashedLevel
  have cachedLeaf : cached.getMem 0x81008 = s.getMem 0x81008 := by
    rw [cacheFrame 0x81008 (by intro i hi; interval_cases i <;> decide),
      GroupedBalancedKeygenStoreSeed67.setup_mem_other hashed 0x81008 (by decide)]
    exact hashedLeaf
  have cachedIndex : cached.getReg .x19 = BitVec.ofNat 64 n := by
    rw [cachedX19,Keygen.hash_registers,
      GroupedBalancedKeygenFirstHashFields67.pre_hash_x19,copiedX19,
      selectedX19,counter]
  have cachedCounter : cached.getMem 0x81030 = BitVec.ofNat 64 n := by
    rw [cacheFrame 0x81030 (by intro i hi; interval_cases i <;> decide)]
    rw [GroupedBalancedKeygenStoreSeed67.setup_counter,
      ← cachedX19]
    exact cachedIndex
  have cachedEven : cached.getReg .x19 &&& 1 = 0 := by
    rw [cachedIndex,← counter]
    exact even
  obtain ⟨final,sixth,finalPC,finalIndex,finalCounter,finalLevel,finalLeaf,_⟩ :=
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
  have total : Trace hash image s 127 134 1 1 final := by
    simpa only [Nat.reduceAdd] using
      path3.trans (sixth.trace (hash := hash))
  exact ⟨final,total,finalPC,
    finalIndex.trans cachedIndex,finalCounter.trans cachedCounter,
    finalLevel.trans cachedLevel,finalLeaf.trans cachedLeaf⟩

#print axioms branch_even_pc
#print axioms even_seed_from_entry

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenEvenSeedRun67
