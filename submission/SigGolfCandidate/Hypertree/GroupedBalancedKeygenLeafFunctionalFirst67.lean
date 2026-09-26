import SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalTick67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsChainRun67
import SigGolfCandidate.TraceDeterminism

/-! The first direct67 WOTS H2 query enters the common tick loop. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalFirst67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenWotsChainRun67
open GroupedBalancedKeygenWotsHashPrelude67
open GroupedBalancedKeygenWotsLoopAdvance67
open GroupedBalancedKeygenLeafFunctionalTick67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem first_end_value (hash : Hash) (s : MachineState)
    (base tree : Nat) (chain : GroupedBalancedChecksum67.Chain)
    (value : Reference.Digest)
    (pc : s.pc = 0x12a8)
    (stepZero : s.getReg .x21 = 0)
    (header : s.getMem 0x80000 =
      KeygenDomain.header 2 base 0 chain.val 0)
    (treeWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (valueWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64)
    (baseBound : base < 256) :
    ∀ i : Fin 2,
      (firstEnd hash s).getMem (Signing.wordAddress 0x80020 i.val) =
        (GroupedBalancedUpperTree67.chainHash hash base tree chain 0 value).extractLsb'
          (64*i.val) 64 := by
  have stagedHeader : replaceByte (s.getMem 0x80000) 4
      ((s.getReg .x21).truncate 8) =
        KeygenDomain.header 2 base 0 chain.val 0 := by
    rw [header,stepZero]
    have trunc : (0 : Word).truncate 8 = BitVec.ofNat 8 0 := by decide
    rw [trunc]
    exact GroupedBalancedByteFastSuffixData67.header_step_replace
      base chain.val 0 0 baseBound
      (by have := chain.isLt; omega) (by decide) (by decide)
  intro i
  rw [firstEnd,advance_mem]
  have result := GroupedBalancedKeygenWotsGenericAnswer67.first_answer
    hash s base tree chain.val value pc stagedHeader treeWords valueWords i
  simpa only [GroupedBalancedUpperTree67.chainHash] using result

theorem first_end_header (hash : Hash) (s : MachineState)
    (base chain : Nat) (pc : s.pc = 0x12a8)
    (stepZero : s.getReg .x21 = 0)
    (header : s.getMem 0x80000 =
      KeygenDomain.header 2 base 0 chain 0)
    (baseBound : base < 256) (chainBound : chain < 256) :
    (firstEnd hash s).getMem 0x80000 =
      KeygenDomain.header 2 base 0 chain 0 := by
  have dst := (prelude_fields s pc).2.2.2.2.1
  rw [firstEnd,advance_mem]
  rw [GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_frame
    (preludeState s) (hash (hashInput (preludeState s))) dst 0x80000
    (by intro i; fin_cases i <;> decide)]
  rw [prelude_mem s 0x80000,if_pos rfl,header,stepZero]
  have trunc : (0 : Word).truncate 8 = BitVec.ofNat 8 0 := by decide
  rw [trunc]
  exact GroupedBalancedByteFastSuffixData67.header_step_replace
    base chain 0 0 baseBound chainBound (by decide) (by decide)

theorem first_end_tree (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x12a8) (i : Fin 3) :
    (firstEnd hash s).getMem
      (Signing.wordAddress 0x80008 i.val) =
        s.getMem (Signing.wordAddress 0x80008 i.val) := by
  have dst := (prelude_fields s pc).2.2.2.2.1
  rw [firstEnd,advance_mem]
  rw [GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_frame
    (preludeState s) (hash (hashInput (preludeState s))) dst _
    (by intro j; fin_cases i <;> fin_cases j <;> decide)]
  rw [prelude_mem s _,if_neg (by fin_cases i <;> decide)]

theorem post_selector_value (hash : Hash) (s : MachineState)
    (base tree maxStep : Nat)
    (chain : GroupedBalancedChecksum67.Chain)
    (value : Reference.Digest)
    (pc : s.pc = 0x12a8)
    (lower : 2 ≤ maxStep) (upper : maxStep ≤ 10)
    (baseBound : base < 256)
    (maxReg : s.getReg .x20 = BitVec.ofNat 64 maxStep)
    (zero : s.getReg .x21 = 0)
    (header : s.getMem 0x80000 =
      KeygenDomain.header 2 base 0 chain.val 0)
    (treeWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (valueWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64) :
    ∃ final,
      Trace hash image s (4*maxStep+6) (11*maxStep+6)
        maxStep maxStep final ∧
      final.pc = 0x12d0 ∧
      final.getMem 0x81030 = s.getMem 0x81030 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80020 i.val) =
          (walk (GroupedBalancedUpperTree67.chainHash hash base tree chain)
            0 maxStep value).extractLsb' (64*i.val) 64) := by
  let prepared := preludeState s
  let hashed := writeHash prepared (hash (hashInput prepared))
  let next := firstEnd hash s
  obtain ⟨readyPC,service,source,bits,destination,_,readyMax,readyZero⟩ :=
    prelude_fields s pc
  have first : Trace hash image s 8 15 1 1 hashed := by
    simpa only [image,GroupedBalancedKeygenWotsFirstHash67.image,
      hashed,prepared] using
      GroupedBalancedKeygenWotsFirstHash67.hash_call hash s pc
  have hashedPC : hashed.pc = 0x12c8 := by
    simp [hashed,prepared,writeHash,readyPC]
  have second : Trace hash image hashed 2 2 0 0 next := by
    simpa only [image,GroupedBalancedKeygenWotsLoopAdvance67.image,
      next,firstEnd] using
      (advance_steps hashed hashedPC).trace (hash := hash)
  have before : Trace hash image s 10 17 1 1 next := by
    simpa only [Nat.reduceAdd] using first.trans second
  have regs := advance_fields hashed hashedPC
  have hashedReg (r : Reg) : hashed.getReg r = prepared.getReg r := by
    simp [hashed,writeHash,MachineState.getReg_setPC]
  have nextReg (r : Reg) (different : r ≠ .x21) :
      next.getReg r = prepared.getReg r := by
    change (advanceState hashed).getReg r = prepared.getReg r
    rw [advance_reg_stable hashed r different,hashedReg]
  have nextStep : next.getReg .x21 = BitVec.ofNat 64 1 := by
    change (advanceState hashed).getReg .x21 = BitVec.ofNat 64 1
    rw [regs.2.1,hashedReg .x21,readyZero,zero]
    decide
  have nextMax : next.getReg .x20 = BitVec.ofNat 64 maxStep := by
    rw [nextReg .x20 (by decide),readyMax,maxReg]
  have nextPC : next.pc = 0x12c0 := by
    have ne : (1 : Word) ≠ BitVec.ofNat 64 maxStep := by
      intro eq
      have h := congrArg BitVec.toNat eq
      simp [BitVec.toNat_ofNat] at h
      omega
    calc
      next.pc =
          (if hashed.getReg .x21 + 1 ≠ hashed.getReg .x20
            then 0x12c0 else 0x12d0) := regs.1
      _ = (if (0 : Word) + 1 ≠ BitVec.ofNat 64 maxStep
            then 0x12c0 else 0x12d0) := by
        rw [hashedReg .x21,hashedReg .x20,
          readyZero,readyMax,zero,maxReg]
      _ = 0x12c0 := by
        have plus : (0 : Word) + 1 = 1 := by decide
        rw [plus]
        exact if_pos ne
  let v1 := GroupedBalancedUpperTree67.chainHash hash base tree chain 0 value
  have nextData : LoopData next base tree chain 1 maxStep v1 := by
    refine ⟨nextPC,nextStep,nextMax,?_,?_,?_,?_,?_,?_,?_⟩
    · exact (nextReg .x5 (by decide)).trans service
    · exact (nextReg .x10 (by decide)).trans source
    · exact (nextReg .x11 (by decide)).trans bits
    · exact (nextReg .x12 (by decide)).trans destination
    · exact ⟨0,by decide,
        first_end_header hash s base chain.val pc zero header
          baseBound (by have := chain.isLt; omega)⟩
    · intro i
      rw [first_end_tree hash s pc i]
      exact treeWords i
    · exact first_end_value hash s base tree chain value pc zero
        header treeWords valueWords baseBound
  have countEq : 1 + (maxStep-1) = maxStep := by omega
  obtain ⟨final,rest,done,result⟩ :=
    run_data hash base tree chain (maxStep-1) next 1 v1
      baseBound (by omega) (by simpa only [countEq] using upper)
      (by simpa only [countEq] using nextData)
  have whole : Trace hash image s (4*maxStep+6) (11*maxStep+6)
      maxStep maxStep final := by
    have full := before.trans rest
    convert full using 1 <;> omega
  obtain ⟨other,otherTrace,otherRest⟩ :=
    post_selector hash s maxStep pc lower upper maxReg zero
  have same : final = other := Trace.deterministic whole otherTrace
  refine ⟨final,whole,done,?_,?_⟩
  · rw [same]
    exact otherRest.2.2.2.1
  · intro i
    have walkEq :
        walk (GroupedBalancedUpperTree67.chainHash hash base tree chain)
          0 maxStep value =
        walk (GroupedBalancedUpperTree67.chainHash hash base tree chain)
          1 (maxStep-1) v1 := by
      calc
        walk (GroupedBalancedUpperTree67.chainHash hash base tree chain)
            0 maxStep value =
          walk (GroupedBalancedUpperTree67.chainHash hash base tree chain)
            0 (1+(maxStep-1)) value := by rw [countEq]
        _ = _ := by
          rw [Nat.add_comm 1 (maxStep-1)]
          rfl
    simpa only [walkEq] using result i

#print axioms first_end_value
#print axioms first_end_header
#print axioms first_end_tree
#print axioms post_selector_value

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalFirst67
