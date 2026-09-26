import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperInitialCapture67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Prepared67


/-! Exact low witness-memory effect of the zero-step capture. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureWitnessInitial67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private noncomputable abbrev result := GroupedBalancedSignUpperInitialCapture67.captureResult
private abbrev selector := GroupedBalancedSignUpperCaptureSelector67.selectorState
private abbrev digit := GroupedBalancedSignUpperCaptureDigit67.digitState

def target (s : MachineState) : Word :=
  GroupedBalancedSignUpperCaptureWrite67.pointer (digit (selector s))

noncomputable def expectedMem (s : MachineState) (a : Word) : Word := by
  classical
  exact if s.getMem 0x810e0 = s.getMem 0x810e8 ∧
      GroupedBalancedSignUpperCaptureCompose67.DigitMatches s then
    if a = target s + 8 then s.getMem 0x80028
    else if a = target s then s.getMem 0x80020
    else s.getMem a
  else s.getMem a

theorem capture_mem (s : MachineState) (a : Word) :
    (result s).getMem a = expectedMem s a := by
  classical
  by_cases selected : s.getMem 0x810e0 = s.getMem 0x810e8
  · by_cases matched : GroupedBalancedSignUpperCaptureCompose67.DigitMatches s
    · change s.getMem 528608#64 = s.getMem 528616#64 at selected
      simp [expectedMem,selected,matched]
      simp [result,GroupedBalancedSignUpperInitialCapture67.captureResult,
        selected,matched,target,
        GroupedBalancedSignUpperCaptureWrite67.write_mem,
        GroupedBalancedSignUpperCaptureDigit67.digit_frame,
        GroupedBalancedSignUpperCaptureSelector67.selector_frame,
        execInstrBr]
      rfl
    · change s.getMem 528608#64 = s.getMem 528616#64 at selected
      simp [expectedMem,selected,matched]
      simp [result,GroupedBalancedSignUpperInitialCapture67.captureResult,
        selected,matched,
        GroupedBalancedSignUpperCaptureDigit67.digit_frame,
        GroupedBalancedSignUpperCaptureSelector67.selector_frame,
        execInstrBr]
  · change s.getMem 528608#64 ≠ s.getMem 528616#64 at selected
    simp [expectedMem,selected]
    simp [result,GroupedBalancedSignUpperInitialCapture67.captureResult,
      selected,GroupedBalancedSignUpperCaptureSelector67.selector_frame,
      execInstrBr]

#print axioms capture_mem
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureWitnessInitial67


/-! Functional state after H2 setup and the optional zero-step witness capture. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2StartData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree GroupedBalancedUpperTree67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
noncomputable section
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev Data := GroupedBalancedSignUpperH2Invariant67.Data
private abbrev layout := GroupedBalancedSignUpperH2Layout67.prepared

structure Entry (s : MachineState) (base leaf witnessBase : Nat)
    (chain : ChainMixed) (seed : Reference.Digest) : Prop where
  pc : s.pc = 0x18e8
  tree : s.getMem 0x81000 = BitVec.ofNat 64 base
  address : ∀ j : Fin 3,
    s.getMem (Signing.wordAddress 0x81008 j.val) =
      (BitVec.ofNat 192 leaf).extractLsb' (64*j.val) 64
  counter : s.getMem 0x81030 = BitVec.ofNat 64 chain.val
  chainReg : s.getReg .x19 = BitVec.ofNat 64 chain.val
  witness : s.getMem 0x810f0 = BitVec.ofNat 64 witnessBase
  seedWords : ∀ j : Fin 2,
    s.getMem (Signing.wordAddress 0x80020 j.val) =
      seed.extractLsb' (64*j.val) 64

theorem prepared_state (s : MachineState) (base leaf witnessBase : Nat)
    (chain : ChainMixed) (seed : Reference.Digest)
    (entry : Entry s base leaf witnessBase chain seed) :
    ∃ ready : MachineState,
      OrdinarySteps image s
        (47 + GroupedBalancedSignUpperMaxChoice67.stepsFor
          (BitVec.ofNat 64 chain.val)) ready ∧
      ready.pc = 0x19d0 ∧
      ready.getReg .x5 = 1 ∧
      ready.getReg .x10 = 0x80000 ∧
      ready.getReg .x11 = 384 ∧
      ready.getReg .x12 = 0x80020 ∧
      ready.getReg .x19 = BitVec.ofNat 64 chain.val ∧
      ready.getReg .x20 = BitVec.ofNat 64 (maxDigit chain) ∧
      ready.getReg .x21 = 0 ∧
      ready.getReg .x2 = s.getReg .x2 ∧
      ready.getMem 0x80000 = KeygenDomain.header 2 base 0 chain.val 0 ∧
      (∀ j : Fin 3,
        ready.getMem (Signing.wordAddress 0x80008 j.val) =
          (BitVec.ofNat 192 leaf).extractLsb' (64*j.val) 64) ∧
      (∀ j : Fin 2,
        ready.getMem (Signing.wordAddress 0x80020 j.val) =
          seed.extractLsb' (64*j.val) 64) ∧
      ready.getMem 0x81030 = BitVec.ofNat 64 chain.val ∧
      ready.getMem 0x810f0 = BitVec.ofNat 64 witnessBase ∧
      (∀ a : Word, 0x80600 ≤ a.toNat → a ≠ 0x81038 →
        ready.getMem a = s.getMem a) ∧
      (∀ j : Fin 4,
        ready.getMem (Signing.wordAddress 0x20 j.val) =
          s.getMem (Signing.wordAddress 0x20 j.val)) ∧
      (∀ a : Word, a.toNat < 0x80000 → ready.getMem a = s.getMem a) := by
  obtain ⟨ready,path,pc,max,step,chainReg,source,bits,dst,service,stack,mem⟩ :=
    GroupedBalancedSignUpperH2Prepared67.prepare s entry.pc
  refine ⟨ready,by simpa only [entry.chainReg] using path,pc,service,
    source,bits,dst,chainReg.trans entry.chainReg,?_,step,stack,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [max,entry.chainReg]
    exact GroupedBalancedSignUpperMaxChoice67.max_for_chain chain
  · rw [mem]
    exact GroupedBalancedSignUpperH2Layout67.prepared_header s base chain.val
      entry.tree entry.counter
  · intro j
    rw [mem]
    exact GroupedBalancedSignUpperH2Layout67.prepared_index s leaf entry.address j
  · intro j
    rw [mem]
    exact GroupedBalancedSignUpperH2Layout67.prepared_value s seed entry.seedWords j
  · rw [mem]
    exact GroupedBalancedSignUpperH2Layout67.prepared_high_frame s 0x81030
      (by decide) (by decide) |>.trans entry.counter
  · rw [mem]
    exact GroupedBalancedSignUpperH2Layout67.prepared_high_frame s 0x810f0
      (by decide) (by decide) |>.trans entry.witness
  · intro a high notStep
    rw [mem]
    exact GroupedBalancedSignUpperH2Layout67.prepared_high_frame s a high notStep
  · intro j
    rw [mem]
    exact GroupedBalancedSignUpperH2Layout67.prepared_key_frame s j
  · intro a low
    rw [mem]
    exact GroupedBalancedSignUpperH2Layout67.prepared_low_frame s a low

theorem captured_state (hash : Hash) (s : MachineState)
    (base leaf witnessBase : Nat) (chain : ChainMixed)
    (seed : Reference.Digest)
    (entry : Entry s base leaf witnessBase chain seed)
    (witnessLower : 0x20060 ≤ witnessBase)
    (witnessBound : witnessBase + 16*chain.val + 16 ≤ 0x80000)
    (aligned : witnessBase % 8 = 0) :
    ∃ (n : Nat) (captured : MachineState),
      n ≤ 26 ∧
      OrdinarySteps image s
        (47 + GroupedBalancedSignUpperMaxChoice67.stepsFor
          (BitVec.ofNat 64 chain.val) + n) captured ∧
      captured.pc = 0x1a38 ∧
      Data hash captured base leaf witnessBase chain 0 seed ∧
      captured.getReg .x2 = s.getReg .x2 ∧
      (∀ a : Word, 0x80600 ≤ a.toNat → a ≠ 0x81038 →
        captured.getMem a = s.getMem a) ∧
      (∀ j : Fin 4,
        captured.getMem (Signing.wordAddress 0x20 j.val) =
          s.getMem (Signing.wordAddress 0x20 j.val)) ∧
      (∀ a : Word, a.toNat < 0x80000 →
        a ≠ Signing.wordAddress (witnessBase+16*chain.val) 0 →
        a ≠ Signing.wordAddress (witnessBase+16*chain.val) 1 →
        captured.getMem a = s.getMem a) ∧
      (∃ ready : MachineState,
        OrdinarySteps image s
          (47 + GroupedBalancedSignUpperMaxChoice67.stepsFor
            (BitVec.ofNat 64 chain.val)) ready ∧
        captured=GroupedBalancedSignUpperInitialCapture67.captureResult ready ∧
        ready.getReg .x21=0 ∧
        ready.getMem 0x81030=BitVec.ofNat 64 chain.val ∧
        ready.getMem 0x810f0=BitVec.ofNat 64 witnessBase ∧
        (∀ j : Fin 2, ready.getMem (Signing.wordAddress 0x80020 j.val)=
          seed.extractLsb' (64*j.val) 64) ∧
        (∀ a : Word, 0x80600≤a.toNat → a≠0x81038 →
          ready.getMem a=s.getMem a)) := by
  obtain ⟨ready,prep,readyPc,service,source,bits,destination,chainReg,
    maxReg,stepReg,stack,header,index,value,counter,witness,frame,keyFrame,
    lowFrame⟩ :=
    prepared_state s base leaf witnessBase chain seed entry
  obtain ⟨safeDigit,safeWitness,safeWitnessNext,low0,low1⟩ :=
    GroupedBalancedSignUpperInitialCapture67.safe ready witnessBase
      chain.val witness counter chain.isLt witnessBound aligned
  obtain ⟨n,captured,cap,nBound,capPc,capFrame,capEq⟩ :=
    GroupedBalancedSignUpperInitialCapture67.capture_any ready readyPc
      safeDigit safeWitness safeWitnessNext low0 low1
  have regs := GroupedBalancedSignUpperInitialCapture67.capture_regs ready
  have full := Keygen.ordinary_trans image s ready captured
    (47 + GroupedBalancedSignUpperMaxChoice67.stepsFor
      (BitVec.ofNat 64 chain.val)) n prep cap
  refine ⟨n,captured,nBound,by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using full,
    capPc,?_,?_,?_,?_,?_,?_⟩
  · refine {
      service := ?_, source := ?_, bits := ?_, destination := ?_,
      chainReg := ?_, maxReg := ?_, stepReg := ?_,
      headerCarry := ?_, index := ?_, value := ?_,
      counter := ?_, witness := ?_ }
    · rw [capEq,regs.1]; exact service
    · rw [capEq,regs.2.1]; exact source
    · rw [capEq,regs.2.2.1]; exact bits
    · rw [capEq,regs.2.2.2.1]; exact destination
    · rw [capEq,regs.2.2.2.2.1]; exact chainReg
    · rw [capEq,regs.2.2.2.2.2.1]; exact maxReg
    · rw [capEq,regs.2.2.2.2.2.2]; exact stepReg
    · refine ⟨0,by decide,?_⟩
      rw [capFrame 0x80000 (by decide)]
      exact header
    · intro j
      rw [capFrame _ (by fin_cases j <;> decide)]
      exact index j
    · intro j
      rw [capFrame _ (by fin_cases j <;> decide)]
      simpa [walk] using value j
    · rw [capFrame 0x81030 (by decide)]
      exact counter
    · rw [capFrame 0x810f0 (by decide)]
      exact witness
  · rw [capEq,GroupedBalancedSignUpperInitialCapture67.capture_stack,stack]
  · intro a high notStep
    rw [capFrame a (by omega)]
    exact frame a high notStep
  · intro j
    let a := Signing.wordAddress 0x20 j.val
    have aSmall : a.toNat < 0x100 := by fin_cases j <;> decide
    have targetNat :
        (GroupedBalancedSignUpperCaptureWitnessInitial67.target ready).toNat =
          witnessBase + 16*chain.val := by
      exact GroupedBalancedSignUpperInitialCapture67.pointer_nat ready
        witnessBase chain.val witness counter chain.isLt witnessBound
    have targetNextNat :
        (GroupedBalancedSignUpperCaptureWitnessInitial67.target ready + 8).toNat =
          witnessBase + 16*chain.val + 8 := by
      rw [BitVec.toNat_add,targetNat]
      change (witnessBase+16*chain.val+8) % 2^64 = _
      rw [Nat.mod_eq_of_lt (by omega : witnessBase+16*chain.val+8 < 2^64)]
    have ne0 : a ≠ GroupedBalancedSignUpperCaptureWitnessInitial67.target ready := by
      intro eq
      have he := congrArg BitVec.toNat eq
      rw [targetNat] at he
      omega
    have ne1 : a ≠ GroupedBalancedSignUpperCaptureWitnessInitial67.target ready + 8 := by
      intro eq
      have he := congrArg BitVec.toNat eq
      rw [targetNextNat] at he
      omega
    change Signing.wordAddress 0x20 j.val ≠
      GroupedBalancedSignUpperCaptureWitnessInitial67.target ready at ne0
    change Signing.wordAddress 0x20 j.val ≠
      GroupedBalancedSignUpperCaptureWitnessInitial67.target ready + 8 at ne1
    rw [capEq,GroupedBalancedSignUpperCaptureWitnessInitial67.capture_mem]
    unfold GroupedBalancedSignUpperCaptureWitnessInitial67.expectedMem
    split_ifs with e
    all_goals first
      | exact False.elim (ne1 e)
      | exact False.elim (ne0 e)
      | exact keyFrame j
  · intro a low ne0 ne1
    have hn := GroupedBalancedSignUpperInitialCapture67.pointer_nat ready
      witnessBase chain.val witness counter chain.isLt witnessBound
    have hn' : (GroupedBalancedSignUpperCaptureWitnessInitial67.target ready).toNat =
        witnessBase+16*chain.val := by
      simpa only [GroupedBalancedSignUpperCaptureWitnessInitial67.target] using hn
    have target0 : GroupedBalancedSignUpperCaptureWitnessInitial67.target ready =
        Signing.wordAddress (witnessBase+16*chain.val) 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [hn']
      change witnessBase+16*chain.val =
        (BitVec.ofNat 64 (witnessBase+16*chain.val)).toNat
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have target1 : GroupedBalancedSignUpperCaptureWitnessInitial67.target ready + 8 =
        Signing.wordAddress (witnessBase+16*chain.val) 1 := by
      rw [target0]
      simp [Signing.wordAddress,BitVec.ofNat_add]
    rw [capEq,GroupedBalancedSignUpperCaptureWitnessInitial67.capture_mem]
    unfold GroupedBalancedSignUpperCaptureWitnessInitial67.expectedMem
    rw [target1,target0]
    split_ifs with e
    all_goals first
      | exact False.elim (ne1 e)
      | exact False.elim (ne0 e)
      | exact lowFrame a low
  · exact ⟨ready,prep,capEq,stepReg,counter,witness,value,frame⟩

#print axioms prepared_state
end
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2StartData67
