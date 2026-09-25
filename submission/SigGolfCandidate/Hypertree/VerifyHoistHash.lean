import SigGolfCandidate.Hypertree.VerifyHoistWord
import SigGolfCandidate.Hypertree.VerifyHoistPrepare

namespace SigGolfCandidate.Hypertree.Verifying.Hoist
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen Signing
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false

def TickCode (image : Image) : Prop :=
  instructionAt image 0x1934 = some (.base .ECALL) ∧
  instructionAt image 0x1938 = some (.base (.ADDI .x30 .x30 1)) ∧
  instructionAt image 0x193c = some (.base (.SB .x10 .x30 4)) ∧
  instructionAt image 0x1940 = some (.base (.BNE .x30 .x31 (-12)))

structure LoopData (s : MachineState) (level tree : Nat) (side : Bool)
    (chain : Reference.Chain) (step : Nat) (value : Reference.Digest) : Prop where
  headerEq : s.getMem 0x80000 = KeygenDomain.header 2 level (Reference.sideNumber side) chain.val step
  indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x80008 i.val) =
    (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64
  valueEq : ∀ i : Fin 2, s.getMem (wordAddress 0x80020 i.val) =
    value.extractLsb' (64*i.val) 64
  srcEq : s.getReg .x10 = 0x80000
  lenEq : s.getReg .x11 = 384
  dstEq : s.getReg .x12 = 0x80020
  serviceEq : s.getReg .x5 = 1
  chainReg : s.getReg .x6 = BitVec.ofNat 64 chain.val
  baseReg : s.getReg .x28 = 0x80000
  stepReg : s.getReg .x30 = BitVec.ofNat 64 step
  sevenReg : s.getReg .x31 = 7

def tickState (hash : Hash) (s : MachineState) : MachineState :=
  let s := writeHash s (hash (hashInput s))
  let s := execInstrBr s (.ADDI .x30 .x30 1)
  let s := execInstrBr s (.SB .x10 .x30 4)
  execInstrBr s (.BNE .x30 .x31 (-12))

theorem tick_regs (hash : Hash) (s : MachineState) (r : Reg)
    (hr : r ≠ .x30) :
    (tickState hash s).getReg r = s.getReg r := by
  simp [tickState, execInstrBr, MachineState.setByte,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr), Keygen.hash_registers]

theorem tick_step_reg (hash : Hash) (s : MachineState) :
    (tickState hash s).getReg .x30 = s.getReg .x30 + 1 := by
  simp [tickState, execInstrBr, MachineState.setByte,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    Keygen.hash_registers, signExtend12]

theorem tick_pc (hash : Hash) (s : MachineState) (step : Nat)
    (pc : s.pc = 0x1934) (stepReg : s.getReg .x30 = BitVec.ofNat 64 step)
    (sevenReg : s.getReg .x31 = 7) (small : step < 7) :
    (tickState hash s).pc = if step+1 = 7 then 0x1944 else 0x1934 := by
  unfold tickState
  simp [execInstrBr, Keygen.hash_registers, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, signExtend12, signExtend13, pc, stepReg, sevenReg]
  have hp : (writeHash s (hash (hashInput s))).pc = 0x1938 := by
    rw [Keygen.hash_pc, pc]
    decide
  rw [hp]
  interval_cases step <;> decide

theorem tick_mem (hash : Hash) (s : MachineState) (a : Word)
    (source : s.getReg .x10 = 0x80000) (dst : s.getReg .x12 = 0x80020) :
    (tickState hash s).getMem a =
      if a = 0x80000 then
        replaceByte (s.getMem a) 4 ((s.getReg .x30 + 1).truncate 8)
      else (writeHash s (hash (hashInput s))).getMem a := by
  have hs : (writeHash s (hash (hashInput s))).getReg .x10 = 0x80000 := by
    rw [Keygen.hash_registers]
    exact source
  by_cases h : a = 0x80000
  · subst a
    simp [tickState,execInstrBr,signExtend12,MachineState.setByte,
      Expansion.mem_setMem,source,hs,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,writeHash,dst,MachineState.writeWords,
      alignToDword,byteOffset]
  · simp [tickState,execInstrBr,signExtend12,MachineState.setByte,
      Expansion.mem_setMem,source,hs,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,alignToDword,byteOffset]
    split_ifs <;> simp_all

theorem tick_block (image : Image) (hash : Hash) (code : TickCode image)
    (s : MachineState) (pc : s.pc = 0x1934)
    (service : s.getReg .x5 = 1)
    (src : s.getReg .x10 = 0x80000)
    (len : s.getReg .x11 = 384)
    (dst : s.getReg .x12 = 0x80020) :
    Trace hash image s 4 11 1 1 (tickState hash s) := by
  obtain ⟨c0,c1,c2,c3⟩ := code
  let hashed := writeHash s (hash (hashInput s))
  let s1 := execInstrBr hashed (.ADDI .x30 .x30 1)
  let s2 := execInstrBr s1 (.SB .x10 .x30 4)
  have hf : fetch image s = some (.base .ECALL) := by
    simpa only [fetch_at,pc] using c0
  have valid : hashArgumentsValid s = true := by
    simp [hashArgumentsValid,src,len,dst,accessValid,rangeValid,MEMORY_BYTES]
  have hlen : (hashInput s).1 = 384 := by simp [hashInput,len]
  have hashedPC : hashed.pc = 0x1938 := by
    simp [hashed,Keygen.hash_pc,pc]
  have ordinary : OrdinarySteps image hashed 3 (tickState hash s) := by
    apply OrdinarySteps.step hashed s1 _ (.base (.ADDI .x30 .x30 1)) 2
    · simpa only [fetch_at,hashedPC] using c1
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.SB .x10 .x30 4)) 1
    · have hp : s1.pc = 0x193c := by simp [s1,execInstrBr,hashedPC]
      simpa only [fetch_at,hp] using c2
    · have hs : s1.getReg .x10 = 0x80000 := by
        simp [s1,execInstrBr,MachineState.getReg_setReg_ne]
        rw [Keygen.hash_registers]
        exact src
      simp [s2,ordinaryStep,memoryArgumentsValid,execInstrBr,hs,
        signExtend12,accessValid,rangeValid,MEMORY_BYTES]
    apply OrdinarySteps.step s2 (tickState hash s) _ (.base (.BNE .x30 .x31 (-12))) 0
    · have hp : s2.pc = 0x1940 := by
        simp [s1,s2,execInstrBr,hashedPC,BitVec.add_assoc]
      simpa only [fetch_at,hp] using c3
    · rfl
    exact OrdinarySteps.refl _
  have ht : Trace hash image s 1 8 1 1 hashed := by
    simpa [hashed,hlen,compressions] using
      Trace.hash s hashed 0 0 0 0 hf service valid (Trace.refl hashed)
  simpa [Nat.add_assoc] using ht.trans ordinary.trace

theorem hash_word (s : MachineState) (answer : BitVec 256)
    (dst : s.getReg .x12 = 0x80020) (i : Fin 2) :
    (writeHash s answer).getMem (wordAddress 0x80020 i.val) =
      answer.extractLsb' (64*i.val) 64 := by
  fin_cases i <;> simp [writeHash,dst,wordAddress,MachineState.writeWords]

theorem hash_frame (s : MachineState) (answer : BitVec 256)
    (dst : s.getReg .x12 = 0x80020) (a : Word)
    (outside : ∀ i : Fin 4, a ≠ wordAddress 0x80020 i.val) :
    (writeHash s answer).getMem a = s.getMem a := by
  have h0 : a ≠ 0x80020 := outside 0
  have h1 : a ≠ 0x80028 := outside 1
  have h2 : a ≠ 0x80030 := outside 2
  have h3 : a ≠ 0x80038 := outside 3
  simp only [writeHash,MachineState.getMem_setPC,dst,MachineState.writeWords,
    Expansion.mem_setMem]
  change (if a = 0x80038 then _ else if a = 0x80030 then _ else
    if a = 0x80028 then _ else if a = 0x80020 then _ else s.getMem a) = s.getMem a
  rw [if_neg h3,if_neg h2,if_neg h1,if_neg h0]

theorem hash_answer (hash : Hash) (s : MachineState) (level tree step : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (data : LoopData s level tree side chain step value) :
    hash (hashInput s) =
      Reference.query hash 2 level tree (Reference.sideNumber side) chain.val step (bytes value) := by
  have words := KeygenDomain.words_of_layout s
    (KeygenDomain.header 2 level (Reference.sideNumber side) chain.val step) tree value
    data.headerEq data.indexEq data.valueEq
  rw [KeygenDomain.query_eq s _ tree value data.srcEq data.lenEq words]
  rfl

def OutsideTick (a : Word) : Prop :=
  a ≠ 0x80000 ∧ (∀ i : Fin 4, a ≠ wordAddress 0x80020 i.val)

theorem tick_frame (hash : Hash) (s : MachineState) (a : Word)
    (src : s.getReg .x10 = 0x80000) (dst : s.getReg .x12 = 0x80020)
    (outside : OutsideTick a) :
    (tickState hash s).getMem a = s.getMem a := by
  rw [tick_mem hash s a src dst,if_neg outside.1]
  exact hash_frame s _ dst a outside.2

theorem tick_data (hash : Hash) (s : MachineState) (level tree step : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (small : step < 7)
    (levelBound : level < 256)
    (data : LoopData s level tree side chain step value) :
    LoopData (tickState hash s) level tree side chain (step+1)
      (Reference.chainHash hash level tree side chain step value) := by
  constructor
  · have hstep := header_step_replace level (Reference.sideNumber side) chain.val step
        levelBound (by cases side <;> decide) (by have := chain.isLt; omega) (by omega)
    have htrunc : ((BitVec.ofNat 64 step + 1 : Word).truncate 8) =
        BitVec.ofNat 8 (step+1) := by
      change ((BitVec.ofNat 64 step + BitVec.ofNat 64 1).truncate 8) = _
      rw [← BitVec.ofNat_add,BitVec.truncate_eq_setWidth,
        BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64)]
    rw [tick_mem hash s 0x80000 data.srcEq data.dstEq,if_pos rfl,
      data.headerEq,data.stepReg]
    rw [htrunc]
    exact hstep
  · intro i
    rw [tick_frame hash s _ data.srcEq data.dstEq (by
      unfold OutsideTick
      fin_cases i <;> decide)]
    exact data.indexEq i
  · intro i
    rw [tick_mem hash s _ data.srcEq data.dstEq,
      if_neg (by fin_cases i <;> decide),
      hash_word s _ data.dstEq i, hash_answer hash s level tree step side chain value data]
    let result := Reference.query hash 2 level tree (Reference.sideNumber side) chain.val step (bytes value)
    change result.extractLsb' (64*i.val) 64 = (result.extractLsb' 0 128).extractLsb' (64*i.val) 64
    fin_cases i <;> ext j hj <;> simp (disch := omega)
  · exact (tick_regs hash s .x10 (by decide)).trans data.srcEq
  · exact (tick_regs hash s .x11 (by decide)).trans data.lenEq
  · exact (tick_regs hash s .x12 (by decide)).trans data.dstEq
  · exact (tick_regs hash s .x5 (by decide)).trans data.serviceEq
  · exact (tick_regs hash s .x6 (by decide)).trans data.chainReg
  · exact (tick_regs hash s .x28 (by decide)).trans data.baseReg
  · rw [tick_step_reg,data.stepReg]
    exact (BitVec.ofNat_add step 1).symm
  · exact (tick_regs hash s .x31 (by decide)).trans data.sevenReg

end SigGolfCandidate.Hypertree.Verifying.Hoist
