import SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsTick67

/-! A reusable actual-bytecode H2 tick followed by its WOTS step branch. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsTickLoop67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsTick67
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsLoopAdvance67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

def tickNext (hash : Hash) (s : MachineState) : MachineState :=
  advanceState (writeHash (storeState s)
    (hash (hashInput (storeState s))))

theorem tick_next_trace (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x12c0)
    (service : s.getReg .x5 = 1)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 384)
    (destination : s.getReg .x12 = 0x80020) :
    Trace hash image s 4 11 1 1 (tickNext hash s) := by
  let hashed := writeHash (storeState s)
    (hash (hashInput (storeState s)))
  have first := tick_trace hash s pc service source bits destination
  have hashedPc : hashed.pc = 0x12c8 := by
    have storePc := (store_fields s pc).1
    simp [hashed,writeHash,storePc]
  have second := (advance_steps hashed hashedPc).trace (hash := hash)
  simpa only [tickNext,image,GroupedBalancedKeygenWotsTick67.image,
    GroupedBalancedKeygenWotsLoopAdvance67.image,Nat.reduceAdd] using
      first.trans second

theorem tick_next_fields (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x12c0) :
    (tickNext hash s).pc =
      (if s.getReg .x21 + 1 ≠ s.getReg .x20 then 0x12c0 else 0x12d0) ∧
    (tickNext hash s).getReg .x21 = s.getReg .x21 + 1 ∧
    (tickNext hash s).getReg .x20 = s.getReg .x20 ∧
    (∀ r : Reg, r ≠ .x21 →
      (tickNext hash s).getReg r = s.getReg r) := by
  let hashed := writeHash (storeState s)
    (hash (hashInput (storeState s)))
  have storePc := (store_fields s pc).1
  have hashedPc : hashed.pc = 0x12c8 := by
    simp [hashed,writeHash,storePc]
  have fields := advance_fields hashed hashedPc
  have regs (r : Reg) : hashed.getReg r = s.getReg r := by
    simp [hashed,writeHash,MachineState.getReg_setPC,
      (store_fields s pc).2 r]
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [tickNext,regs .x21,regs .x20] using fields.1
  · simpa only [tickNext,regs .x21] using fields.2.1
  · simpa only [tickNext,regs .x20] using fields.2.2.1
  · intro r different
    rw [tickNext,advance_reg_stable hashed r different,regs r]

theorem tick_next_counter (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x12c0)
    (source : s.getReg .x10 = 0x80000)
    (destination : s.getReg .x12 = 0x80020) :
    (tickNext hash s).getMem 0x81030 = s.getMem 0x81030 := by
  have dst : (storeState s).getReg .x12 = 0x80020 :=
    ((store_fields s pc).2 .x12).trans destination
  rw [tickNext,advance_mem]
  rw [GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_frame
    (storeState s) (hash (hashInput (storeState s))) dst 0x81030
    (by intro i; fin_cases i <;> decide)]
  rw [store_mem s source 0x81030,if_neg (by decide)]

theorem tick_next_level (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x12c0)
    (source : s.getReg .x10 = 0x80000)
    (destination : s.getReg .x12 = 0x80020) :
    (tickNext hash s).getMem 0x81000 = s.getMem 0x81000 := by
  have dst : (storeState s).getReg .x12 = 0x80020 :=
    ((store_fields s pc).2 .x12).trans destination
  rw [tickNext,advance_mem]
  rw [GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_frame
    (storeState s) (hash (hashInput (storeState s))) dst 0x81000
    (by intro i; fin_cases i <;> decide)]
  rw [store_mem s source 0x81000,if_neg (by decide)]

theorem tick_next_leaf (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x12c0)
    (source : s.getReg .x10 = 0x80000)
    (destination : s.getReg .x12 = 0x80020) :
    (tickNext hash s).getMem 0x81008 = s.getMem 0x81008 := by
  have dst : (storeState s).getReg .x12 = 0x80020 :=
    ((store_fields s pc).2 .x12).trans destination
  rw [tickNext,advance_mem]
  rw [GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_frame
    (storeState s) (hash (hashInput (storeState s))) dst 0x81008
    (by intro i; fin_cases i <;> decide)]
  rw [store_mem s source 0x81008,if_neg (by decide)]

#print axioms tick_next_trace
#print axioms tick_next_fields
#print axioms tick_next_counter
#print axioms tick_next_level
#print axioms tick_next_leaf

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsTickLoop67
