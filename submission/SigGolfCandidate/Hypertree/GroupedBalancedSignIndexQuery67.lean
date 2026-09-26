import SigGolfCandidate.Hypertree.GroupedBalancedSignIndexPrepare67
import SigGolfCandidate.Hypertree.SignIndexRefine
import SigGolfCandidate.Hypertree.SecurityRandomOracle


namespace SigGolfCandidate.Hypertree.GroupedBalancedSignIndexHash67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
open SigGolfCandidate.Hypertree.Signing
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
def image : Image := GroupedBalancedSignImage67.image

def indexHashState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x10 0x80)
  let s := execInstrBr s (.ADDI .x10 .x10 0)
  let s := execInstrBr s (.ADDI .x11 .x0 896)
  let s := execInstrBr s (.LUI .x12 0x80)
  let s := execInstrBr s (.ADDI .x12 .x12 0x300)
  execInstrBr s (.ADDI .x5 .x0 1)

theorem indexHashState_block (s : MachineState) (pc : s.pc = 0x118c) :
    OrdinarySteps image s 6 (indexHashState s) := by
  let s1 := execInstrBr s (.LUI .x10 0x80)
  let s2 := execInstrBr s1 (.ADDI .x10 .x10 0)
  let s3 := execInstrBr s2 (.ADDI .x11 .x0 896)
  let s4 := execInstrBr s3 (.LUI .x12 0x80)
  let s5 := execInstrBr s4 (.ADDI .x12 .x12 0x300)
  let s6 := execInstrBr s5 (.ADDI .x5 .x0 1)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x10 0x80)) 5
  · have hp : s.pc = 0x118c := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x10 .x10 0)) 4
  · have hp : s1.pc = 0x1190 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x11 .x0 896)) 3
  · have hp : s2.pc = 0x1194 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x12 0x80)) 2
  · have hp : s3.pc = 0x1198 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x12 .x12 0x300)) 1
  · have hp : s4.pc = 0x119c := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x5 .x0 1)) 0
  · have hp : s5.pc = 0x11a0 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  exact OrdinarySteps.refl _


theorem indexHashState_regs (s : MachineState) :
    (indexHashState s).getReg .x5 = 1 ∧ (indexHashState s).getReg .x10 = 0x80000 ∧
    (indexHashState s).getReg .x11 = 896 ∧ (indexHashState s).getReg .x12 = 0x80300 := by
  simp [indexHashState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem indexHashState_pc (s : MachineState) : (indexHashState s).pc = s.pc + 24 := by
  simp [indexHashState, execInstrBr, BitVec.add_assoc]


end SigGolfCandidate.Hypertree.GroupedBalancedSignIndexHash67


/-! Exact tag5 query and the signer's second HASH instruction. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignIndexQuery67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def virtualZeroSlot (s : MachineState) : MachineState :=
  (s.setMem 0x50 0).setMem 0x58 0

theorem virtual_mem (s : MachineState) (a : Word)
    (h50 : a ≠ 0x50) (h58 : a ≠ 0x58) :
    (virtualZeroSlot s).getMem a = s.getMem a := by
  change a ≠ 80#64 at h50
  change a ≠ 88#64 at h58
  simp [virtualZeroSlot,h50,h58]

theorem virtual_zero_word (s : MachineState) (j : Fin 2) :
    (virtualZeroSlot s).getMem (Signing.wordAddress 0x50 j.val) = 0 := by
  fin_cases j <;> simp [virtualZeroSlot,Signing.wordAddress,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem virtual_zero_byte (s : MachineState) (i : Nat) (hi : i < 16) :
    (virtualZeroSlot s).getByte (BitVec.ofNat 64 (0x50+i)) = 0 := by
  rw [Signing.getByte_word (virtualZeroSlot s) 0x50 i
    (by decide) (by omega)]
  rw [virtual_zero_word s ⟨i/8,by omega⟩]
  simp [extractByte]

private theorem virtual_byte_frame (s : MachineState)
    (base i : Nat) (aligned : base % 8 = 0)
    (bound : base+i < 2^64)
    (low : base+8*(i/8) < 0x50 ∨ 0x58 < base+8*(i/8)) :
    (virtualZeroSlot s).getByte (BitVec.ofNat 64 (base+i)) =
      s.getByte (BitVec.ofNat 64 (base+i)) := by
  rw [Signing.getByte_word (virtualZeroSlot s) base i aligned bound,
    Signing.getByte_word s base i aligned bound]
  apply congrArg (fun w : Word => extractByte w (i%8))
  apply virtual_mem
  · intro eq
    have hn := congrArg BitVec.toNat eq
    have hv : (Signing.wordAddress base (i/8)).toNat =
        base+8*(i/8) := by
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : base+8*(i/8)<2^64)]
    have hc : (0x50 : Word).toNat = 0x50 := by decide
    rw [hv,hc] at hn
    omega
  · intro eq
    have hn := congrArg BitVec.toNat eq
    have hv : (Signing.wordAddress base (i/8)).toNat =
        base+8*(i/8) := by
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : base+8*(i/8)<2^64)]
    have hc : (0x58 : Word).toNat = 0x58 := by decide
    rw [hv,hc] at hn
    omega

theorem virtual_message_byte (s : MachineState) (i : Nat) (hi : i < 32) :
    (virtualZeroSlot s).getByte (BitVec.ofNat 64 i) =
      s.getByte (BitVec.ofNat 64 i) := by
  simpa using virtual_byte_frame s 0 i (by decide) (by omega)
    (Or.inl (by omega))

theorem virtual_randomizer_byte (s : MachineState) (i : Nat) (hi : i < 32) :
    (virtualZeroSlot s).getByte (BitVec.ofNat 64 (0x20060+i)) =
      s.getByte (BitVec.ofNat 64 (0x20060+i)) := by
  exact virtual_byte_frame s 0x20060 i (by decide) (by omega)
    (Or.inr (by omega))

theorem virtual_index_word (s : MachineState) (j : Fin 14) :
    GroupedBalancedSignIndexPrepare67.indexInputWord s j =
      Signing.indexInputWord (virtualZeroSlot s) j := by
  fin_cases j <;> simp [GroupedBalancedSignIndexPrepare67.indexInputWord,
    Signing.indexInputWord,virtualZeroSlot,Signing.wordAddress,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem index_query (original ready : MachineState)
    (message : Message) (r : Bytes 32)
    (hmessage : ∀ i, i < 32 → original.getByte
      (BitVec.ofNat 64 i) = message.extractLsb' (8*i) 8)
    (hr : ∀ i, i < 32 → original.getByte
      (BitVec.ofNat 64 (0x20060+i)) = r.extractLsb' (8*i) 8)
    (words : ∀ i : Fin 14,
      ready.getMem (Signing.wordAddress 0x80000 i.val) =
        GroupedBalancedSignIndexPrepare67.indexInputWord original i) :
    hashInput (GroupedBalancedSignIndexHash67.indexHashState ready) =
      SecurityRandomOracle.indexInput message r := by
  let zeroed := virtualZeroSlot original
  have oldWords : ∀ i : Fin 14,
      ready.getMem (Signing.wordAddress 0x80000 i.val) =
        Signing.indexInputWord zeroed i := by
    intro i
    rw [words i,virtual_index_word]
  have q := Signing.index_query zeroed ready message r
    (virtual_zero_byte original)
    (by intro i hi; rw [virtual_message_byte original i hi]; exact hmessage i hi)
    (by intro i hi; rw [virtual_randomizer_byte original i hi]; exact hr i hi)
    oldWords
  simpa [GroupedBalancedSignIndexHash67.indexHashState,
    Signing.indexHashState,SecurityRandomOracle.indexInput,
    SecurityRandomOracle.addressedInput,Signing.indexPayload,
    Reference.packed] using q

theorem index_hash_call (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x118c) :
    Trace hash GroupedBalancedSignImage67.image s 7 22 1 2
      (writeHash (GroupedBalancedSignIndexHash67.indexHashState s)
        (hash (hashInput (GroupedBalancedSignIndexHash67.indexHashState s)))) := by
  let ready := GroupedBalancedSignIndexHash67.indexHashState s
  have pre := GroupedBalancedSignIndexHash67.indexHashState_block s pc
  have fields := GroupedBalancedSignIndexHash67.indexHashState_regs s
  have done : ready.pc = 0x11a4 := by
    simp [ready,GroupedBalancedSignIndexHash67.indexHashState_pc,pc]
  have fetched : fetch GroupedBalancedSignImage67.image ready =
      some (.base .ECALL) := by
    simp only [Keygen.fetch_at,done]
    decide
  have valid : hashArgumentsValid ready = true :=
    Keygen.hash_arguments ready 896 fields.2.1 fields.2.2.1
      fields.2.2.2 (by decide)
  have len : (hashInput ready).1 = 896 := by
    simp [hashInput,ready,fields.2.2.1]
  have call : Trace hash GroupedBalancedSignImage67.image ready 1 16 1 2
      (writeHash ready (hash (hashInput ready))) := by
    simpa [len,compressions] using
      Trace.hash ready _ 0 0 0 0 fetched fields.1 valid
        (Trace.refl _)
  simpa only [ready,Nat.reduceAdd,
    GroupedBalancedSignIndexHash67.image] using
    (OrdinarySteps.trace (hash := hash) pre).trans call

#print axioms index_query
#print axioms index_hash_call

end SigGolfCandidate.Hypertree.GroupedBalancedSignIndexQuery67
