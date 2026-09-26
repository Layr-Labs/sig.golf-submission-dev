import SigGolfCandidate.Hypertree.GroupedBalancedVerifyEndGroupSwitchFields67

/-! Every group counter value below 45 has a checked control path. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyEndGroupDispatch67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyEndGroup67
open GroupedBalancedVerifyEndGroupFinish67
open GroupedBalancedVerifyEndGroupLoop67
open GroupedBalancedVerifyEndGroupSwitch67
open GroupedBalancedVerifyEndGroupSwitchFields67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem dispatch (s : MachineState) (g : Nat)
    (pc : s.pc = 0x19c4)
    (group : s.getMem 0x81058 = BitVec.ofNat 64 g)
    (bound : g < 45) :
    ∃ (t : MachineState) (steps : Nat), steps ≤ 15 ∧
      OrdinarySteps image s steps t ∧
      t.pc = (if g = 44 then 0x1a04 else 0x1514) ∧
      t.getMem 0x81058 = BitVec.ofNat 64 (g+1) ∧
      t.getMem 0x81060 =
        (if g = 29 then 4 else s.getMem 0x81060) ∧
      (∀ a : Word, a.toNat < 0x80000 → t.getMem a = s.getMem a) ∧
      (∀ a : Word, a ≠ 0x81058 → a ≠ 0x81060 →
        t.getMem a = s.getMem a) := by
  by_cases last : g = 44
  · subst g
    have group44 : s.getMem 0x81058 = 44 := by simpa using group
    have h30 : (countState s).getReg .x6 ≠
        (countState s).getReg .x7 := by
      rw [count_x6,count_x7,group44]
      decide
    refine ⟨finishState s,12,by decide,?_,?_,?_,?_,?_,?_⟩
    · exact Keygen.ordinary_trans image s (countState s)
        (finishState s) 8 4 (count_steps s pc)
          (finish_steps s pc h30)
    · simpa using finish_pc s pc group44
    · exact loop_group s 44 group
    · simpa using finish_mem s 0x81060 (by decide)
    · intro a low
      apply finish_mem s a
      intro eq
      rw [eq] at low
      exact (by decide : ¬ ((0x81058 : Word).toNat < 0x80000)) low
    · intro a neGroup _
      exact finish_mem s a neGroup
  · by_cases switch : g = 29
    · subst g
      have group29 : s.getMem 0x81058 = 29 := by simpa using group
      obtain ⟨trace,atDecoder,nextGroup,height,low⟩ :=
        switch_transition s pc group29
      refine ⟨switchState s,15,by decide,trace,?_,?_,?_,low,?_⟩
      · simpa using atDecoder
      · simpa using nextGroup
      · simpa using height
      · intro a neGroup neHeight
        rw [switch_mem s a neHeight,count_mem s a neGroup]
    · have prior : g < 44 := by omega
      obtain ⟨trace,atDecoder,nextGroup,height,low⟩ :=
        loop_transition s g pc group prior switch
      refine ⟨finishState s,12,by decide,trace,?_,nextGroup,?_,low,?_⟩
      · simpa [last] using atDecoder
      · simpa [switch] using height
      · intro a neGroup _
        exact finish_mem s a neGroup

#print axioms dispatch
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyEndGroupDispatch67
