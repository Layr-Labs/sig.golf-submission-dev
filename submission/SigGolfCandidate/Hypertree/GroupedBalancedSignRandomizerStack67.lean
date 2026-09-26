import SigGolfCandidate.Hypertree.GroupedBalancedSignRandomizerLoaded67
import SigGolfCandidate.Hypertree.KeygenCopyFrame
import SigGolfCandidate.TraceDeterminism

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignRandomizerStack67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

theorem prepare_sp (s ready : MachineState) (pc : s.pc = 0x1000)
    (trace : OrdinarySteps image s 72 ready) :
    ready.getReg .x2 = s.getReg .x2 := by
  let initialized := GroupedBalancedSignPrepare67.initializeState s
  have initSteps := GroupedBalancedSignPrepare67.initializeState_block s pc
  have skCode : Keygen.CopyCode image 0x1010 := by decide
  obtain ⟨sk,skLoop,skInv,_,_,_,skSp⟩ := Keygen.copy_all_frame image 0x1010
    skCode 0x20 0x80020 4 initialized
    (GroupedBalancedSignPrepare67.initializeState_invariant s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have skPc : sk.pc = 0x1028 := by simpa [Keygen.CopyInvariant] using skInv.2.2.1
  let messageSetup := GroupedBalancedSignPrepare67.messageCopyState sk
  have messageSteps := GroupedBalancedSignPrepare67.messageCopyState_block sk skPc
  have msgCode : Keygen.CopyCode image 0x1038 := by decide
  obtain ⟨msg,msgLoop,msgInv,_,_,_,msgSp⟩ := Keygen.copy_all_frame image 0x1038
    msgCode 0 0x80040 4 messageSetup
    (GroupedBalancedSignPrepare67.messageCopyState_invariant sk skPc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have msgPc : msg.pc = 0x1050 := by simpa [Keygen.CopyInvariant] using msgInv.2.2.1
  let header := GroupedBalancedSignPrepare67.randomizerHeaderState msg
  have headerSteps := GroupedBalancedSignPrepare67.randomizerHeaderState_block msg msgPc
  have constructed : OrdinarySteps image s 72 header := by
    simpa only [show 4+24+4+24+16=72 by decide] using
      Keygen.ordinary_trans image s initialized header 4 68 initSteps
        (Keygen.ordinary_trans image initialized sk header 24 44 skLoop
          (Keygen.ordinary_trans image sk messageSetup header 4 40 messageSteps
            (Keygen.ordinary_trans image messageSetup msg header 24 16 msgLoop headerSteps)))
  have same := Keygen.ordinary_deterministic trace constructed
  rw [same]
  have initSp : initialized.getReg .x2 = s.getReg .x2 := by
    simp [initialized,GroupedBalancedSignPrepare67.initializeState,
      execInstrBr,MachineState.getReg_setReg_ne]
  have messageSp : messageSetup.getReg .x2 = sk.getReg .x2 := by
    simp [messageSetup,GroupedBalancedSignPrepare67.messageCopyState,
      execInstrBr,MachineState.getReg_setReg_ne]
  have headerSp : header.getReg .x2 = msg.getReg .x2 := by
    simp [header,GroupedBalancedSignPrepare67.randomizerHeaderState,
      execInstrBr,MachineState.getReg_setReg_ne]
  exact headerSp.trans (msgSp.trans (messageSp.trans (skSp.trans initSp)))

theorem answer_copy_sp (s final : MachineState) (pc : s.pc = 0x10ac)
    (trace : OrdinarySteps image s 29 final) :
    final.getReg .x2 = s.getReg .x2 := by
  let begun := GroupedBalancedSignRandomizer67.randomizerCopyState s
  obtain ⟨other,loop,_,_,_,_,sp⟩ := Keygen.copy_all_frame image 0x10c0
    GroupedBalancedSignRandomizer67.randomizer_copy_code 0x80300 0x20060 4 begun
    (GroupedBalancedSignRandomizer67.randomizerCopyState_invariant s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have setup := GroupedBalancedSignRandomizer67.randomizerCopyState_block s pc
  have constructed : OrdinarySteps image s 29 other := by
    simpa only [show 5+24=29 by decide] using
      Keygen.ordinary_trans image s begun other 5 24 setup loop
  have same := Keygen.ordinary_deterministic trace constructed
  rw [same,sp]
  simp [begun,GroupedBalancedSignRandomizer67.randomizerCopyState,
    execInstrBr,MachineState.getReg_setReg_ne]

theorem query_sp (hash : Hash) (s final : MachineState) (pc : s.pc = 0x1090)
    (trace : Trace hash image s 36 51 1 2 final) :
    final.getReg .x2 = s.getReg .x2 := by
  let ready := GroupedBalancedSignRandomizer67.randomizerHashState s
  have readyPc : ready.pc = 0x10a8 := by
    simp [ready,GroupedBalancedSignRandomizer67.randomizerHashState_pc,pc]
  obtain ⟨service,src,len,dst⟩ :=
    GroupedBalancedSignRandomizer67.randomizerHashState_regs s
  have fetchCall : fetch image ready = some (.base .ECALL) := by
    simp only [fetch,readyPc]; decide
  have valid : hashArgumentsValid ready = true :=
    Keygen.hash_arguments ready 768 src len dst
      (by decide)
  have length : (hashInput ready).1 = 768 := by simp [hashInput,ready,len]
  let answer := hash (hashInput ready)
  let hashed := writeHash ready answer
  have hashedPc : hashed.pc = 0x10ac := by
    simp [hashed,Keygen.hash_pc,readyPc]
  obtain ⟨copied,copyTrace,_,_⟩ :=
    GroupedBalancedSignRandomizer67.randomizer_copy hashed hashedPc
  have call : Trace hash image ready 1 16 1 2 hashed := by
    simpa [length,compressions,hashed,answer] using
      Trace.hash ready hashed 0 0 0 0 fetchCall service valid
        (Trace.refl hashed)
  have constructed : Trace hash image s 36 51 1 2 copied := by
    simpa [image,GroupedBalancedSignRandomizer67.image] using
      ((GroupedBalancedSignRandomizer67.randomizerHashState_block s pc).trace.trans
        call).trans copyTrace.trace
  have same := Trace.deterministic trace constructed
  rw [same]
  have readySp : ready.getReg .x2 = s.getReg .x2 := by
    simp [ready,GroupedBalancedSignRandomizer67.randomizerHashState,
      execInstrBr,MachineState.getReg_setReg_ne]
  exact (answer_copy_sp hashed copied hashedPc copyTrace).trans
    ((Keygen.hash_registers ready answer .x2).trans readySp)

theorem entry_sp (hash : Hash) (s final : MachineState) (pc : s.pc = 0x1000)
    (trace : Trace hash image s 108 123 1 2 final) :
    final.getReg .x2 = s.getReg .x2 := by
  obtain ⟨ready,prepared,readyPc,_,_⟩ :=
    GroupedBalancedSignPrepare67.randomizer_prepare s pc
  obtain ⟨other,queried,_,_⟩ :=
    GroupedBalancedSignRandomizer67.randomizer_trace hash ready readyPc
  have constructed : Trace hash image s 108 123 1 2 other :=
    prepared.trace.trans queried
  have same := Trace.deterministic trace constructed
  rw [same]
  exact (query_sp hash ready other readyPc queried).trans
    (prepare_sp s ready pc prepared)

#print axioms entry_sp
end SigGolfCandidate.Hypertree.GroupedBalancedSignRandomizerStack67
