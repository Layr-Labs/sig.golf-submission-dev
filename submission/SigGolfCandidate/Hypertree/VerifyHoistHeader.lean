import SigGolfCandidate.Hypertree.SignEncodeFinish
import SigGolfCandidate.Hypertree.KeygenBlocks

namespace SigGolfCandidate.Hypertree.Verifying.Hoist
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Signing Keygen
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

@[simp] theorem byte_setReg (s : MachineState) (r : Reg) (v a : Word) :
    (s.setReg r v).getByte a = s.getByte a := by
  simp [MachineState.getByte]

attribute [local simp] Signing.getByte_setByte

-- The branch from 0x190c falls through here for chains 1..45. The HASH
-- source and length registers (x10 = 0x80000, x11 = 384) are carried from the
-- previous chain, so only the chain and step bytes are written.
def PartialCode (image : Image) : Prop :=
  instructionAt image 0x1910 = some (.base (.SB .x10 .x6 3)) ∧
  instructionAt image 0x1914 = some (.base (.SB .x10 .x30 4)) ∧
  instructionAt image 0x1918 = some (.base (.JAL .x0 24))

def partialState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.SB .x10 .x6 3)
  let s := execInstrBr s (.SB .x10 .x30 4)
  execInstrBr s (.JAL .x0 24)

theorem partial_block (image : Image) (code : PartialCode image)
    (s : MachineState) (pc : s.pc = 0x1910) (src : s.getReg .x10 = 0x80000) :
    OrdinarySteps image s 3 (partialState s) := by
  obtain ⟨c0,c1,c2⟩ := code
  let s1 := execInstrBr s (.SB .x10 .x6 3)
  let s2 := execInstrBr s1 (.SB .x10 .x30 4)
  let s3 := execInstrBr s2 (.JAL .x0 24)
  apply OrdinarySteps.step s s1 _ (.base (.SB .x10 .x6 3)) 2
  · have hp : s.pc = 0x1910 := pc
    simpa only [fetch_at, hp] using c0
  · simp [s1,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,src,
      accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s1 s2 _ (.base (.SB .x10 .x30 4)) 1
  · have hp : s1.pc = 0x1914 := by simp [s1,execInstrBr,pc]
    simpa only [fetch_at,hp] using c1
  · simp [s1,s2,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,MachineState.setByte,src,
      accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s2 s3 _ (.base (.JAL .x0 24)) 0
  · have hp : s2.pc = 0x1918 := by simp [s1,s2,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c2
  · rfl
  exact OrdinarySteps.refl _

theorem partial_pc (s : MachineState) (pc : s.pc = 0x1910) :
    (partialState s).pc = 0x1930 := by
  norm_num [partialState,execInstrBr,pc,BitVec.add_assoc,signExtend21]
  decide

theorem partial_regs (s : MachineState) :
    (partialState s).getReg .x5 = s.getReg .x5 ∧
    (partialState s).getReg .x10 = s.getReg .x10 ∧
    (partialState s).getReg .x11 = s.getReg .x11 ∧
    (partialState s).getReg .x12 = s.getReg .x12 ∧
    (partialState s).getReg .x30 = s.getReg .x30 ∧
    (partialState s).getReg .x31 = s.getReg .x31 := by
  simp [partialState,execInstrBr,signExtend12,MachineState.setByte,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem partial_byte (s : MachineState) (src : s.getReg .x10 = 0x80000) (a : Word) :
    (partialState s).getByte a =
      if a = 0x80004 then (s.getReg .x30).truncate 8
      else if a = 0x80003 then (s.getReg .x6).truncate 8
      else s.getByte a := by
  simp [partialState,execInstrBr,signExtend12,src,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

-- `template` is the state immediately after chain zero's full header build.
-- It remains a ghost value in the leaf induction. Every fixed header byte is
-- inherited from that state, while bytes 3/4 are the chain and step slots.
def HeaderCarry (s template : MachineState) : Prop :=
  (∀ a : Word, a ≠ 0x80003 → a ≠ 0x80004 →
    a.toNat < 0x80020 → a.toNat ≥ 0x80000 → s.getByte a = template.getByte a) ∧
  s.getReg .x5 = 1 ∧ s.getReg .x12 = 0x80020 ∧ s.getReg .x31 = 7

theorem partial_carry (s template : MachineState) (src : s.getReg .x10 = 0x80000)
    (h : HeaderCarry s template) :
    HeaderCarry (partialState s) template := by
  rcases h with ⟨fixed, service, destination, seven⟩
  obtain ⟨r5, _, _, r12, _, r31⟩ := partial_regs s
  refine ⟨?_, r5.trans service, r12.trans destination, r31.trans seven⟩
  intro a notChain notStep upper lower
  rw [partial_byte s src, if_neg notStep, if_neg notChain]
  exact fixed a notChain notStep upper lower

theorem partial_chain_byte (s : MachineState) (src : s.getReg .x10 = 0x80000) :
    (partialState s).getByte 0x80003 = (s.getReg .x6).truncate 8 := by
  rw [partial_byte s src, if_neg (by decide), if_pos rfl]

theorem partial_step_byte (s : MachineState) (src : s.getReg .x10 = 0x80000) :
    (partialState s).getByte 0x80004 = (s.getReg .x30).truncate 8 := by
  rw [partial_byte s src, if_pos rfl]

-- The template records the fixed bytes of the domain header and the three
-- tree words. The chain/step slots are intentionally unconstrained here.
def TemplateCanonical (template : MachineState) (level tree leaf : Nat) : Prop :=
  (∀ i : Fin 8, i.val ≠ 3 → i.val ≠ 4 →
    template.getByte (BitVec.ofNat 64 (0x80000+i.val)) =
      extractByte (BitVec.ofNat 64 (2+level*2^8+leaf*2^16)) i.val) ∧
  (∀ i : Fin 3, template.getMem (BitVec.ofNat 64 (0x80008+8*i.val)) =
    (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)

-- The leaf loop uses this conditional invariant. Its first chain builds the
-- full header and supplies the ghost template for all later chains.
def HeaderReady (s : MachineState) (level tree leaf next : Nat) : Prop :=
  next = 0 ∨ ∃ template, TemplateCanonical template level tree leaf ∧ HeaderCarry s template

end SigGolfCandidate.Hypertree.Verifying.Hoist
