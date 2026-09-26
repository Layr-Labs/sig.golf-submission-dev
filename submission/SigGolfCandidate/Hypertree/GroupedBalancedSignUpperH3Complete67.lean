import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3Store67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafAdvanceData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3Query67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3StoreData67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3Complete67. -/
section
/-! Data preserved by the upper leaf store, whose memory writes match the bottom leaf store. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3StoreData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

theorem same_memory (s : MachineState) (a : Word) :
    (GroupedBalancedSignUpperH3Store67.advanceState s).getMem a =
      (GroupedBalancedSignBottomLeafAdvance67.advanceState s).getMem a := by
  simp [GroupedBalancedSignUpperH3Store67.advanceState,
    GroupedBalancedSignBottomLeafAdvance67.advanceState,
    execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

private theorem small (s : MachineState)
    (h : (s.getMem 0x810e0).toNat < 16) :
    (s.getMem 0x810e0).toNat < 1024 := by omega

theorem advance_counter (s : MachineState)
    (h : (s.getMem 0x810e0).toNat < 16) :
    (GroupedBalancedSignUpperH3Store67.advanceState s).getMem 0x810e0 =
      s.getMem 0x810e0 + 1 := by
  rw [same_memory]
  exact GroupedBalancedSignBottomLeafAdvanceData67.advance_counter s (small s h)

theorem advance_address (s : MachineState)
    (h : (s.getMem 0x810e0).toNat < 16) :
    (GroupedBalancedSignUpperH3Store67.advanceState s).getMem 0x81008 =
      s.getMem 0x81008 + 1 := by
  rw [same_memory]
  exact GroupedBalancedSignBottomLeafAdvanceData67.advance_address s (small s h)

theorem advance_frame (s : MachineState)
    (h : (s.getMem 0x810e0).toNat < 16) (a : Word)
    (h0 : a ≠ GroupedBalancedSignBottomStackBound67.stack0 (s.getMem 0x810e0))
    (h8 : a ≠ GroupedBalancedSignBottomStackBound67.stack0 (s.getMem 0x810e0) + 8)
    (haddr : a ≠ 0x81008) (hcount : a ≠ 0x810e0) :
    (GroupedBalancedSignUpperH3Store67.advanceState s).getMem a = s.getMem a := by
  rw [same_memory]
  exact GroupedBalancedSignBottomLeafAdvanceData67.advance_frame s (small s h)
    a h0 h8 haddr hcount

theorem advance_store0 (s : MachineState)
    (h : (s.getMem 0x810e0).toNat < 16) :
    (GroupedBalancedSignUpperH3Store67.advanceState s).getMem
      (GroupedBalancedSignBottomStackBound67.stack0 (s.getMem 0x810e0)) =
      s.getMem 0x80300 := by
  rw [same_memory]
  exact GroupedBalancedSignBottomLeafAdvanceData67.advance_store0 s (small s h)

theorem advance_store8 (s : MachineState)
    (h : (s.getMem 0x810e0).toNat < 16) :
    (GroupedBalancedSignUpperH3Store67.advanceState s).getMem
      (GroupedBalancedSignBottomStackBound67.stack0 (s.getMem 0x810e0) + 8) =
      s.getMem 0x80308 := by
  rw [same_memory]
  exact GroupedBalancedSignBottomLeafAdvanceData67.advance_store8 s (small s h)

theorem advance_trace (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1bb4)
    (h : (s.getMem 0x810e0).toNat < 16) :
    Trace hash GroupedBalancedSignImage67Byte.image s 31 31 0 0
      (GroupedBalancedSignUpperH3Store67.advanceState s) := by
  have hv := GroupedBalancedSignBottomStackBound67.stack0_valid
    (s.getMem 0x810e0) (small s h)
  exact OrdinarySteps.trace (hash := hash)
    (GroupedBalancedSignUpperH3Store67.advance_steps s pc
      (by simpa only [GroupedBalancedSignBottomStackBound67.stack0] using hv.1)
      (by simpa only [GroupedBalancedSignBottomStackBound67.stack0] using hv.2))

theorem advance_pc (s : MachineState) (pc : s.pc = 0x1bb4)
    (h : (s.getMem 0x810e0).toNat < 16) :
    (GroupedBalancedSignUpperH3Store67.advanceState s).pc =
      if s.getMem 0x810e0 + 1 = s.getMem 0x810d0 then 0x1c30 else 0x1750 := by
  have ⟨ne0,ne8⟩ := GroupedBalancedSignBottomStackBound67.below_stack
    (s.getMem 0x810e0) 0x810d0 (small s h) (by decide)
  have raw : (GroupedBalancedSignUpperH3Store67.advanceState s).pc =
      if (GroupedBalancedSignUpperH3Store67.advanceState s).getMem 0x810e0 =
          (GroupedBalancedSignUpperH3Store67.advanceState s).getMem 0x810d0
      then 0x1c30 else 0x1750 := by
    simp [GroupedBalancedSignUpperH3Store67.advanceState,execInstrBr,
      signExtend12,signExtend13,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]
  rw [raw,advance_counter s h,
    advance_frame s h 0x810d0 ne0 ne8 (by decide) (by decide)]

#print axioms same_memory
#print axioms advance_counter
#print axioms advance_address
#print axioms advance_frame
#print axioms advance_store0
#print axioms advance_store8
#print axioms advance_trace
#print axioms advance_pc
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3StoreData67

end

/-! One upper H3 compression and its leaf-table store. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3Complete67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev prepared := GroupedBalancedSignUpperH3Header67.headerState

theorem header_sp (s : MachineState) :
    (prepared s).getReg .x2 = s.getReg .x2 := by
  simp [prepared,GroupedBalancedSignUpperH3Header67.headerState,
    execInstrBr,MachineState.getReg_setReg_ne]

theorem advance_sp (s : MachineState) :
    (GroupedBalancedSignUpperH3Store67.advanceState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignUpperH3Store67.advanceState,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem complete_sp (hash : Hash) (s : MachineState) :
    (GroupedBalancedSignUpperH3Store67.advanceState
      (writeHash (prepared s) (hash (hashInput (prepared s))))).getReg .x2 =
      s.getReg .x2 := by
  rw [advance_sp,Keygen.hash_registers,header_sp]

theorem hash_high_frame (hash : Hash) (s : MachineState) (a : Word)
    (high : 0x81000 ≤ a.toNat) :
    (writeHash (prepared s) (hash (hashInput (prepared s)))).getMem a =
      s.getMem a := by
  have regs := GroupedBalancedSignUpperH3Header67.header_regs s
  rw [Signing.hash_answer_frame (prepared s) _ regs.2.2.2 a]
  · exact GroupedBalancedSignUpperH3Header67.header_high_frame s a high
  · intro i eq
    have hn := congrArg BitVec.toNat eq
    simp only [Signing.wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80300+8*i.val < 2^64)] at hn
    omega

theorem hash_low_frame (hash : Hash) (s : MachineState) (a : Word)
    (low : a.toNat < 0x80000) :
    (writeHash (prepared s) (hash (hashInput (prepared s)))).getMem a =
      s.getMem a := by
  have regs := GroupedBalancedSignUpperH3Header67.header_regs s
  rw [Signing.hash_answer_frame (prepared s) _ regs.2.2.2 a]
  · exact GroupedBalancedSignUpperH3Header67.header_low_frame s a low
  · intro i eq
    have hn := congrArg BitVec.toNat eq
    simp only [Signing.wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80300+8*i.val < 2^64)] at hn
    omega

theorem hash_digit_frame (hash : Hash) (s : MachineState) (a : Word)
    (low : 0x80600 ≤ a.toNat) (high : a.toNat < 0x80800) :
    (writeHash (prepared s) (hash (hashInput (prepared s)))).getMem a =
      s.getMem a := by
  have h0 : a ≠ 0x80000#64 := by
    intro eq; rw [eq] at low; norm_num at low
  have h8 : a ≠ 0x80008#64 := by
    intro eq; rw [eq] at low; norm_num at low
  have h10 : a ≠ 0x80010#64 := by
    intro eq; rw [eq] at low; norm_num at low
  have h18 : a ≠ 0x80018#64 := by
    intro eq; rw [eq] at low; norm_num at low
  have header : (prepared s).getMem a = s.getMem a := by
    simp [prepared,GroupedBalancedSignUpperH3Header67.headerState,
      execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,h0,h8,h10,h18]
  have regs := GroupedBalancedSignUpperH3Header67.header_regs s
  rw [Signing.hash_answer_frame (prepared s) _ regs.2.2.2 a]
  · exact header
  · intro i eq
    have hn := congrArg BitVec.toNat eq
    simp only [Signing.wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80300+8*i.val < 2^64)] at hn
    omega

theorem hash_word (hash : Hash) (s : MachineState) (base leaf : Nat)
    (values : Fin 67 → Reference.Digest)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (address : ∀ j : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 j.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*j.val) 64)
    (endpoints : ∀ j : Fin 134,
      s.getMem (Signing.wordAddress 0x80020 j.val) =
        (values ⟨j.val/2,by have := j.isLt; omega⟩).extractLsb'
          (64*(j.val%2)) 64) (i : Fin 2) :
    (writeHash (prepared s) (hash (hashInput (prepared s)))).getMem
        (Signing.wordAddress 0x80300 i.val) =
      (GroupedBalancedUpperTree67.compressLeaf hash base leaf values).extractLsb'
        (64*i.val) 64 := by
  have regs := GroupedBalancedSignUpperH3Header67.header_regs s
  rw [Signing.hash_answer_word (prepared s)
    (hash (hashInput (prepared s))) regs.2.2.2
      ⟨i.val,by have := i.isLt; omega⟩]
  let answer := hash (hashInput (prepared s))
  have answerEq := GroupedBalancedSignUpperH3Query67.leaf_hash_eq
    hash s base leaf values level address endpoints
  change answer.extractLsb' (64*i.val) 64 =
    (GroupedBalancedUpperTree67.compressLeaf hash base leaf values).extractLsb'
      (64*i.val) 64
  rw [← answerEq]
  change answer.extractLsb' (64*i.val) 64 =
    (answer.extractLsb' 0 128).extractLsb' (64*i.val) 64
  fin_cases i <;> ext j hj <;> simp (disch := omega)

theorem leaf_to_next (hash : Hash) (s : MachineState)
    (base leaf : Nat) (values : Fin 67 → Reference.Digest)
    (pc : s.pc = 0x1b28)
    (counter : (s.getMem 0x810e0).toNat < 16)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (address : ∀ j : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 j.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*j.val) 64)
    (endpoints : ∀ j : Fin 134,
      s.getMem (Signing.wordAddress 0x80020 j.val) =
        (values ⟨j.val/2,by have := j.isLt; omega⟩).extractLsb'
          (64*(j.val%2)) 64) :
    ∃ next : MachineState,
      Trace hash image s 66 209 1 18 next ∧
      next.getMem 0x810e0 = s.getMem 0x810e0 + 1 ∧
      next.getMem 0x81008 = s.getMem 0x81008 + 1 ∧
      next.getMem (GroupedBalancedSignBottomStackBound67.stack0
        (s.getMem 0x810e0)) =
        (GroupedBalancedUpperTree67.compressLeaf hash base leaf values).extractLsb' 0 64 ∧
      next.getMem (GroupedBalancedSignBottomStackBound67.stack0
        (s.getMem 0x810e0) + 8) =
        (GroupedBalancedUpperTree67.compressLeaf hash base leaf values).extractLsb' 64 64 ∧
      next.pc =
        (if s.getMem 0x810e0 + 1 = s.getMem 0x810d0 then 0x1c30 else 0x1750) ∧
      (∀ a : Word, 0x81000 ≤ a.toNat →
        a ≠ GroupedBalancedSignBottomStackBound67.stack0 (s.getMem 0x810e0) →
        a ≠ GroupedBalancedSignBottomStackBound67.stack0 (s.getMem 0x810e0) + 8 →
        a ≠ 0x81008 → a ≠ 0x810e0 → next.getMem a = s.getMem a) ∧
      next.getReg .x2 = s.getReg .x2 ∧
      (∀ a : Word, a.toNat < 0x80000 → next.getMem a=s.getMem a) ∧
      (∀ a : Word, 0x80600 ≤ a.toNat → a.toNat < 0x80800 →
        next.getMem a=s.getMem a) := by
  let ready := prepared s
  let after := writeHash ready (hash (hashInput ready))
  let next := GroupedBalancedSignUpperH3Store67.advanceState after
  have first := (GroupedBalancedSignUpperH3Header67.header_steps s pc).trace (hash := hash)
  have readyPc := GroupedBalancedSignUpperH3Header67.header_pc s pc
  have regs := GroupedBalancedSignUpperH3Header67.header_regs s
  have second := GroupedBalancedSignUpperH3Hash67.hash_trace hash ready readyPc regs
  have afterPc : after.pc = 0x1bb4 := by
    change ready.pc + 4 = 0x1bb4
    rw [readyPc]
    decide
  have countAfter : after.getMem 0x810e0 = s.getMem 0x810e0 :=
    hash_high_frame hash s 0x810e0 (by decide)
  have addrAfter : after.getMem 0x81008 = s.getMem 0x81008 :=
    hash_high_frame hash s 0x81008 (by decide)
  have limitAfter : after.getMem 0x810d0 = s.getMem 0x810d0 :=
    hash_high_frame hash s 0x810d0 (by decide)
  have boundAfter : (after.getMem 0x810e0).toNat < 16 := by
    rw [countAfter]
    exact counter
  have third := GroupedBalancedSignUpperH3StoreData67.advance_trace
    hash after afterPc boundAfter
  refine ⟨next,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [next,after,ready,image,Nat.add_assoc] using (first.trans second).trans third
  · change (GroupedBalancedSignUpperH3Store67.advanceState after).getMem 0x810e0 = _
    rw [GroupedBalancedSignUpperH3StoreData67.advance_counter after boundAfter,countAfter]
  · change (GroupedBalancedSignUpperH3Store67.advanceState after).getMem 0x81008 = _
    rw [GroupedBalancedSignUpperH3StoreData67.advance_address after boundAfter,addrAfter]
  · change (GroupedBalancedSignUpperH3Store67.advanceState after).getMem _ = _
    rw [← countAfter,GroupedBalancedSignUpperH3StoreData67.advance_store0 after boundAfter]
    exact hash_word hash s base leaf values level address endpoints 0
  · change (GroupedBalancedSignUpperH3Store67.advanceState after).getMem _ = _
    rw [← countAfter,GroupedBalancedSignUpperH3StoreData67.advance_store8 after boundAfter]
    exact hash_word hash s base leaf values level address endpoints 1
  · change (GroupedBalancedSignUpperH3Store67.advanceState after).pc = _
    rw [GroupedBalancedSignUpperH3StoreData67.advance_pc after afterPc boundAfter,
      countAfter,limitAfter]
  · intro a high h0 h8 haddr hcount
    change (GroupedBalancedSignUpperH3Store67.advanceState after).getMem a = _
    rw [GroupedBalancedSignUpperH3StoreData67.advance_frame after boundAfter a
      (by rw [countAfter]; exact h0) (by rw [countAfter]; exact h8)
      haddr hcount]
    exact hash_high_frame hash s a high
  · exact complete_sp hash s
  · intro a low
    have ⟨h0,h8⟩ := GroupedBalancedSignBottomStackBound67.below_stack
      (s.getMem 0x810e0) a (by omega) (by omega)
    have haddr : a≠0x81008 := by
      intro eq
      subst a
      have numeric : (0x81008 : Word).toNat = 0x81008 := by decide
      rw [numeric] at low
      omega
    have hcount : a≠0x810e0 := by
      intro eq
      subst a
      have numeric : (0x810e0 : Word).toNat = 0x810e0 := by decide
      rw [numeric] at low
      omega
    change (GroupedBalancedSignUpperH3Store67.advanceState after).getMem a = _
    rw [GroupedBalancedSignUpperH3StoreData67.advance_frame after boundAfter a
      (by rw [countAfter]; exact h0) (by rw [countAfter]; exact h8)
      haddr hcount]
    exact hash_low_frame hash s a low
  · intro a low high
    have ⟨h0,h8⟩ := GroupedBalancedSignBottomStackBound67.below_stack
      (s.getMem 0x810e0) a (by omega) (by omega)
    have haddr : a≠0x81008 := by
      intro eq; subst a
      have numeric : (0x81008 : Word).toNat=0x81008 := by decide
      rw [numeric] at high
      omega
    have hcount : a≠0x810e0 := by
      intro eq; subst a
      have numeric : (0x810e0 : Word).toNat=0x810e0 := by decide
      rw [numeric] at high
      omega
    change (GroupedBalancedSignUpperH3Store67.advanceState after).getMem a = _
    rw [GroupedBalancedSignUpperH3StoreData67.advance_frame after boundAfter a
      (by rw [countAfter]; exact h0) (by rw [countAfter]; exact h8)
      haddr hcount]
    exact hash_digit_frame hash s a low high

#print axioms hash_high_frame
#print axioms complete_sp
#print axioms hash_word
#print axioms leaf_to_next
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3Complete67
