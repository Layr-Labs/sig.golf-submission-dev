import SigGolfCandidate.Hypertree.GroupedBalancedKeygenStoreSeed67

/-! The initial even top-tree leaf selects the first half of the H1 seed. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstLeaf67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def image : Image := GroupedBalancedKeygenImage67.image

def branchState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ANDI .x6 .x19 1)
  execInstrBr s (.BEQ .x6 .x0 52)

private theorem branch_code :
    Keygen.instructionAt image 0x1174 = some (.base (.ANDI .x6 .x19 1)) ∧
    Keygen.instructionAt image 0x1178 = some (.base (.BEQ .x6 .x0 52)) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide

theorem branch_steps (s : MachineState) (pc : s.pc = 0x1174) :
    OrdinarySteps image s 2 (branchState s) := by
  let s1 := execInstrBr s (.ANDI .x6 .x19 1)
  obtain ⟨c0,c1⟩ := branch_code
  apply OrdinarySteps.step s s1 _ (.base (.ANDI .x6 .x19 1)) 1
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 (branchState s) _ (.base (.BEQ .x6 .x0 52)) 0
  · have hp : s1.pc = 0x1178 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  exact OrdinarySteps.refl _

theorem branch_fields (s : MachineState) (pc : s.pc = 0x1174)
    (even : s.getReg .x19 = 0) :
    (branchState s).pc = 0x11ac ∧
    (branchState s).getReg .x19 = 0 := by
  simp [branchState,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    pc,even]

theorem branch_mem (s : MachineState) (a : Word) :
    (branchState s).getMem a = s.getMem a := by
  simp [branchState,execInstrBr]

def setupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x81)
  let s := execInstrBr s (.ADDI .x6 .x6 0xd00)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 32)
  execInstrBr s (.ADDI .x10 .x0 2)

private theorem setup_code :
    Keygen.instructionAt image 0x11ac = some (.base (.LUI .x6 0x81)) ∧
    Keygen.instructionAt image 0x11b0 = some (.base (.ADDI .x6 .x6 0xd00)) ∧
    Keygen.instructionAt image 0x11b4 = some (.base (.LUI .x7 0x80)) ∧
    Keygen.instructionAt image 0x11b8 = some (.base (.ADDI .x7 .x7 32)) ∧
    Keygen.instructionAt image 0x11bc = some (.base (.ADDI .x10 .x0 2)) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide

theorem setup_steps (s : MachineState) (pc : s.pc = 0x11ac) :
    OrdinarySteps image s 5 (setupState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x81)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0xd00)
  let s3 := execInstrBr s2 (.LUI .x7 0x80)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 32)
  obtain ⟨c0,c1,c2,c3,c4⟩ := setup_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x81)) 4
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0xd00)) 3
  · have hp : s1.pc = 0x11b0 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s2.pc = 0x11b4 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 32)) 1
  · have hp : s3.pc = 0x11b8 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 (setupState s) _ (.base (.ADDI .x10 .x0 2)) 0
  · have hp : s4.pc = 0x11bc := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem setup_fields (s : MachineState) (pc : s.pc = 0x11ac) :
    (setupState s).pc = 0x11c0 ∧
    (setupState s).getReg .x6 = 0x80d00 ∧
    (setupState s).getReg .x7 = 0x80020 ∧
    (setupState s).getReg .x10 = 2 ∧
    (setupState s).getReg .x19 = s.getReg .x19 := by
  simp [setupState,execInstrBr,signExtend12,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem setup_mem (s : MachineState) (a : Word) :
    (setupState s).getMem a = s.getMem a := by
  simp [setupState,execInstrBr]

theorem copy_code : Keygen.CopyCode image 0x11c0 := by
  unfold Keygen.CopyCode image GroupedBalancedKeygenImage67.image
  decide

theorem even_seed_copy (s : MachineState) (pc : s.pc = 0x1174)
    (even : s.getReg .x19 = 0) :
    ∃ final, OrdinarySteps image s 19 final ∧
      final.pc = 0x11d8 ∧
      final.getReg .x19 = 0 ∧
      (∀ i, i < 2 → final.getMem (Signing.wordAddress 0x80020 i) =
        s.getMem (Signing.wordAddress 0x80d00 i)) := by
  let branched := branchState s
  obtain ⟨bpc,bx19⟩ := branch_fields s pc even
  have first := branch_steps s pc
  let ready := setupState branched
  obtain ⟨readyPC,readySrc,readyDst,readyCount,readyX19⟩ :=
    setup_fields branched bpc
  have readyInv : Keygen.CopyInvariant 0x11c0 0x80d00 0x80020 2 2 ready := by
    refine ⟨by decide,by decide,?_,readySrc,readyDst,readyCount⟩
    simpa [ready] using readyPC
  obtain ⟨final,copied,done,words,_,copyX19⟩ :=
    KeygenCopyX19.copy_all_x19 image 0x11c0 copy_code
      0x80d00 0x80020 2 ready readyInv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have second := setup_steps branched bpc
  refine ⟨final,?_,?_,?_,?_⟩
  · have pre := Keygen.ordinary_trans image s branched ready 2 5 first second
    simpa only [Nat.reduceMul,Nat.reduceAdd] using
      Keygen.ordinary_trans image s ready final 7 (6*2) pre copied
  · simpa [Keygen.CopyInvariant] using done.2.2.1
  · rw [copyX19,readyX19]
    exact bx19
  · intro i hi
    rw [words i hi,setup_mem,branch_mem]

#print axioms even_seed_copy

theorem initial_even_seed (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1000) (secretKey : SecretKey)
    (secret : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    ∃ final, Trace hash image s 147 154 1 1 final ∧
      final.pc = 0x11d8 ∧ final.getReg .x19 = 0 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80020 i.val) =
          (Reference.query hash 1 156 0 0 0 0 (bytes secretKey)).extractLsb'
            (64*i.val) 64) := by
  obtain ⟨cached,first,cachedPC,cachedX19,cacheWords⟩ :=
    GroupedBalancedKeygenStoreSeed67.initial_seed_cache
      hash s pc secretKey secret
  obtain ⟨final,second,finalPC,finalX19,words⟩ :=
    even_seed_copy cached cachedPC cachedX19
  refine ⟨final,?_,finalPC,finalX19,?_⟩
  · simpa only [image,GroupedBalancedKeygenStoreSeed67.image,
      Nat.reduceAdd] using first.trans second.trace
  · intro i
    rw [words i i.isLt,cacheWords ⟨i.val,by have := i.isLt; omega⟩]

#print axioms initial_even_seed

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstLeaf67
