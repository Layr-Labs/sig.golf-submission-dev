import SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstHashFields67

/-! The first keygen hash's eight input words. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstHashMemory67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstHash67
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

theorem header_mem (s : MachineState) (a : Word) :
    (headerState s).getMem a =
      if a = 0x80000 then
        1 + (s.getMem 0x81000 <<< 8) + (s.getMem 0x81030 <<< 24)
      else s.getMem a := by
  simp [headerState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq, MachineState.getMem_setMem_ne]

theorem index0_mem (s : MachineState) (a : Word) :
    (index0State s).getMem a =
      if a = 0x80008 then s.getMem 0x81008 else s.getMem a := by
  simp [index0State, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq, MachineState.getMem_setMem_ne]

theorem index1_mem (s : MachineState) (a : Word) :
    (index1State s).getMem a =
      if a = 0x80010 then s.getMem 0x81010 else s.getMem a := by
  simp [index1State, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq, MachineState.getMem_setMem_ne]

theorem index2_mem (s : MachineState) (a : Word) :
    (index2State s).getMem a =
      if a = 0x80018 then s.getMem 0x81018 else s.getMem a := by
  simp [index2State, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq, MachineState.getMem_setMem_ne]

theorem regs_mem (s : MachineState) (a : Word) :
    (regsState s).getMem a = s.getMem a := by
  simp [regsState, execInstrBr]

theorem pre_hash_mem (s : MachineState) (a : Word) :
    (preHashState s).getMem a =
      if a = 0x80018 then s.getMem 0x81018 else
      if a = 0x80010 then s.getMem 0x81010 else
      if a = 0x80008 then s.getMem 0x81008 else
      if a = 0x80000 then
        1 + (s.getMem 0x81000 <<< 8) + (s.getMem 0x81030 <<< 24)
      else s.getMem a := by
  simp only [preHashState, regs_mem, index2_mem, index1_mem,
    index0_mem, header_mem]
  split_ifs <;> simp_all

#print axioms pre_hash_mem

theorem first_hash_input_words (s : MachineState) (secretKey : SecretKey)
    (level : s.getMem 0x81000 = 156)
    (tree : s.getMem 0x81030 = 0)
    (index0 : s.getMem 0x81008 = 0)
    (index1 : s.getMem 0x81010 = 0)
    (index2 : s.getMem 0x81018 = 0)
    (secret : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 8,
      (preHashState s).getMem (Signing.wordAddress 0x80000 i.val) =
        KeygenDomain.secretInputWord (KeygenDomain.header 1 156 0 0 0)
          0 secretKey i := by
  apply KeygenDomain.secret_words_of_layout
  · simp only [pre_hash_mem, if_false, if_true]
    rw [level, tree]
    simp [KeygenDomain.header]
  · intro i
    fin_cases i
    · simpa [pre_hash_mem, Signing.wordAddress] using index0
    · simpa [pre_hash_mem, Signing.wordAddress] using index1
    · simpa [pre_hash_mem, Signing.wordAddress] using index2
  · intro i
    rw [pre_hash_mem]
    have h := secret i
    fin_cases i <;> simpa [Signing.wordAddress] using h

#print axioms first_hash_input_words

theorem first_hash_input (s : MachineState) (secretKey : SecretKey)
    (level : s.getMem 0x81000 = 156)
    (tree : s.getMem 0x81030 = 0)
    (index0 : s.getMem 0x81008 = 0)
    (index1 : s.getMem 0x81010 = 0)
    (index2 : s.getMem 0x81018 = 0)
    (secret : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    hashInput (preHashState s) = Reference.packed
      (KeygenDomain.secretPayload (KeygenDomain.header 1 156 0 0 0) 0 secretKey) := by
  obtain ⟨_, source, bits, _⟩ :=
    GroupedBalancedKeygenFirstHashFields67.pre_hash_regs s
  exact KeygenDomain.secret_query_eq (preHashState s)
    (KeygenDomain.header 1 156 0 0 0) 0 secretKey source bits
    (first_hash_input_words s secretKey level tree index0 index1 index2 secret)

theorem first_hash_query (hash : Hash) (s : MachineState)
    (secretKey : SecretKey)
    (level : s.getMem 0x81000 = 156)
    (tree : s.getMem 0x81030 = 0)
    (index0 : s.getMem 0x81008 = 0)
    (index1 : s.getMem 0x81010 = 0)
    (index2 : s.getMem 0x81018 = 0)
    (secret : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    hash (hashInput (preHashState s)) =
      Reference.query hash 1 156 0 0 0 0 (bytes secretKey) := by
  rw [first_hash_input s secretKey level tree index0 index1 index2 secret]
  rfl

#print axioms first_hash_query

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstHashMemory67
