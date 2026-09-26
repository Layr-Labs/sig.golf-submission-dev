import SigGolfCandidate.Hypertree.GroupedBalancedSignIndexPrefix67
import SigGolfCandidate.Hypertree.KeygenCopyFrame
import SigGolfCandidate.TraceDeterminism

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignIndexStack67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

theorem prepare_sp (s ready : MachineState) (pc : s.pc = 0x10d8)
    (trace : OrdinarySteps image s 81 ready) :
    ready.getReg .x2 = s.getReg .x2 := by
  let slot := GroupedBalancedSignIndexPrepare67.slotCopyState s
  have slotSteps := GroupedBalancedSignIndexPrepare67.slotCopyState_block s pc
  have slotPc : slot.pc = 0x10f8 := by
    simp [slot,GroupedBalancedSignIndexPrepare67.slotCopyState_pc,pc]
  let msgSetup := GroupedBalancedSignIndexPrepare67.indexMessageCopyState slot
  have msgSetupSteps := GroupedBalancedSignIndexPrepare67.indexMessageCopyState_block slot slotPc
  have msgCode : Keygen.CopyCode image 0x1108 := by decide
  obtain ⟨msg,msgLoop,msgInv,_,_,_,msgSp⟩ := Keygen.copy_all_frame image 0x1108
    msgCode 0 0x80030 4 msgSetup
    (GroupedBalancedSignIndexPrepare67.indexMessageCopyState_invariant slot slotPc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have msgPc : msg.pc = 0x1120 := by simpa [Keygen.CopyInvariant] using msgInv.2.2.1
  let randSetup := GroupedBalancedSignIndexPrepare67.inputRandomizerCopyState msg
  have randSetupSteps := GroupedBalancedSignIndexPrepare67.inputRandomizerCopyState_block msg msgPc
  have randCode : Keygen.CopyCode image 0x1134 := by decide
  obtain ⟨rand,randLoop,randInv,_,_,_,randSp⟩ := Keygen.copy_all_frame image 0x1134
    randCode 0x20060 0x80050 4 randSetup
    (GroupedBalancedSignIndexPrepare67.inputRandomizerCopyState_invariant msg msgPc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have randPc : rand.pc = 0x114c := by simpa [Keygen.CopyInvariant] using randInv.2.2.1
  let header := GroupedBalancedSignIndexPrepare67.indexHeaderState rand
  have headerSteps := GroupedBalancedSignIndexPrepare67.indexHeaderState_block rand randPc
  have constructed : OrdinarySteps image s 81 header := by
    simpa only [show 8+4+24+5+24+16=81 by decide] using
      Keygen.ordinary_trans image s slot header 8 73 slotSteps
        (Keygen.ordinary_trans image slot msgSetup header 4 69 msgSetupSteps
          (Keygen.ordinary_trans image msgSetup msg header 24 45 msgLoop
            (Keygen.ordinary_trans image msg randSetup header 5 40 randSetupSteps
              (Keygen.ordinary_trans image randSetup rand header 24 16 randLoop headerSteps))))
  have same := Keygen.ordinary_deterministic trace constructed
  rw [same]
  have slotSp : slot.getReg .x2 = s.getReg .x2 := by
    simp [slot,GroupedBalancedSignIndexPrepare67.slotCopyState,
      execInstrBr,MachineState.getReg_setReg_ne]
  have msgSetupSp : msgSetup.getReg .x2 = slot.getReg .x2 := by
    simp [msgSetup,GroupedBalancedSignIndexPrepare67.indexMessageCopyState,
      execInstrBr,MachineState.getReg_setReg_ne]
  have randSetupSp : randSetup.getReg .x2 = msg.getReg .x2 := by
    simp [randSetup,GroupedBalancedSignIndexPrepare67.inputRandomizerCopyState,
      execInstrBr,MachineState.getReg_setReg_ne]
  have headerSp : header.getReg .x2 = rand.getReg .x2 := by
    simp [header,GroupedBalancedSignIndexPrepare67.indexHeaderState,
      execInstrBr,MachineState.getReg_setReg_ne]
  exact headerSp.trans (randSp.trans (randSetupSp.trans
    (msgSp.trans (msgSetupSp.trans slotSp))))

theorem query_sp (hash : Hash) (s final : MachineState) (pc : s.pc = 0x118c)
    (trace : Trace hash image s 7 22 1 2 final) :
    final.getReg .x2 = s.getReg .x2 := by
  let ready := GroupedBalancedSignIndexHash67.indexHashState s
  have readySp : ready.getReg .x2 = s.getReg .x2 := by
    simp [ready,GroupedBalancedSignIndexHash67.indexHashState,
      execInstrBr,MachineState.getReg_setReg_ne]
  have readyPc : ready.pc = 0x11a4 := by
    simp [ready,GroupedBalancedSignIndexHash67.indexHashState_pc,pc]
  obtain ⟨service,src,len,dst⟩ :=
    GroupedBalancedSignIndexHash67.indexHashState_regs s
  have fetchCall : fetch image ready = some (.base .ECALL) := by
    simp only [fetch,readyPc]; decide
  have valid : hashArgumentsValid ready = true :=
    Keygen.hash_arguments ready 896 src len dst (by decide)
  have length : (hashInput ready).1 = 896 := by simp [hashInput,ready,len]
  let hashed := writeHash ready (hash (hashInput ready))
  have call : Trace hash image ready 1 16 1 2 hashed := by
    simpa [length,compressions,hashed] using
      Trace.hash ready hashed 0 0 0 0 fetchCall service valid (Trace.refl hashed)
  have constructed : Trace hash image s 7 22 1 2 hashed := by
    simpa [GroupedBalancedSignIndexHash67.image,image] using
      (GroupedBalancedSignIndexHash67.indexHashState_block s pc).trace.trans call
  have same := Trace.deterministic trace constructed
  rw [same]
  exact (Keygen.hash_registers ready (hash (hashInput ready)) .x2).trans readySp

theorem index_sp (hash : Hash) (s final : MachineState) (pc : s.pc = 0x10d8)
    (trace : Trace hash image s 88 103 1 2 final) :
    final.getReg .x2 = s.getReg .x2 := by
  obtain ⟨ready,prepared,readyPc,_,_⟩ :=
    GroupedBalancedSignIndexPrepare67.index_prepare s pc
  let after := writeHash (GroupedBalancedSignIndexHash67.indexHashState ready)
    (hash (hashInput (GroupedBalancedSignIndexHash67.indexHashState ready)))
  have queried : Trace hash image ready 7 22 1 2 after := by
    let hs := GroupedBalancedSignIndexHash67.indexHashState ready
    have hsPc : hs.pc = 0x11a4 := by
      simp [hs,GroupedBalancedSignIndexHash67.indexHashState_pc,readyPc]
    obtain ⟨service,src,len,dst⟩ :=
      GroupedBalancedSignIndexHash67.indexHashState_regs ready
    have fetchCall : fetch image hs = some (.base .ECALL) := by
      simp only [fetch,hsPc]; decide
    have valid : hashArgumentsValid hs = true :=
      Keygen.hash_arguments hs 896 src len dst (by decide)
    have length : (hashInput hs).1 = 896 := by simp [hashInput,hs,len]
    have call : Trace hash image hs 1 16 1 2 after := by
      simpa [length,compressions,after,hs] using
        Trace.hash hs after 0 0 0 0 fetchCall service valid (Trace.refl after)
    simpa [GroupedBalancedSignIndexHash67.image,image] using
      (GroupedBalancedSignIndexHash67.indexHashState_block ready readyPc).trace.trans call
  have constructed : Trace hash image s 88 103 1 2 after :=
    prepared.trace.trans queried
  have same := Trace.deterministic trace constructed
  rw [same]
  exact (query_sp hash ready after readyPc queried).trans
    (prepare_sp s ready pc prepared)

theorem index_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x10d8) :
    ∃ after : MachineState, Trace hash image s 88 103 1 2 after := by
  obtain ⟨ready,prepared,readyPc,_,_⟩ :=
    GroupedBalancedSignIndexPrepare67.index_prepare s pc
  let hs := GroupedBalancedSignIndexHash67.indexHashState ready
  have hsPc : hs.pc = 0x11a4 := by
    simp [hs,GroupedBalancedSignIndexHash67.indexHashState_pc,readyPc]
  obtain ⟨service,src,len,dst⟩ :=
    GroupedBalancedSignIndexHash67.indexHashState_regs ready
  have fetchCall : fetch image hs = some (.base .ECALL) := by
    simp only [fetch,hsPc]; decide
  have valid : hashArgumentsValid hs = true :=
    Keygen.hash_arguments hs 896 src len dst (by decide)
  have length : (hashInput hs).1 = 896 := by simp [hashInput,hs,len]
  let after := writeHash hs (hash (hashInput hs))
  have call : Trace hash image hs 1 16 1 2 after := by
    simpa [length,compressions,after] using
      Trace.hash hs after 0 0 0 0 fetchCall service valid (Trace.refl after)
  have query : Trace hash image ready 7 22 1 2 after := by
    simpa [GroupedBalancedSignIndexHash67.image,image] using
      (GroupedBalancedSignIndexHash67.indexHashState_block ready readyPc).trace.trans call
  exact ⟨after,prepared.trace.trans query⟩

#print axioms index_sp
#print axioms index_trace
end SigGolfCandidate.Hypertree.GroupedBalancedSignIndexStack67
