import SigGolfCandidate.Hypertree.VerifyHoistHeader
import SigGolfCandidate.Hypertree.KeygenDomain

namespace SigGolfCandidate.Hypertree.Verifying.Hoist
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Signing

private theorem low_shift_disjoint (lo : BitVec 32) (b : BitVec 8) :
    (lo.zeroExtend 64) &&& ((b.zeroExtend 64) <<< 32) = 0#64 := by
  ext i (hi : i < 64)
  simp [BitVec.zeroExtend]
  intro h32 hlo
  have ge : 32 ≤ i := by omega
  simp [BitVec.getLsbD_of_ge lo i hlo] at h32



private theorem mask_four (i : Nat) (hi : i < 64) :
    (18446742978492891135#64)[i] = decide (i < 32 ∨ 40 ≤ i) := by
  change (~~~ (((BitVec.allOnes 8).zeroExtend 64) <<< 32))[i] =
      decide (i < 32 ∨ 40 ≤ i)
  simp only [BitVec.getElem_not, BitVec.getElem_shiftLeft,
    BitVec.getElem_setWidth]
  by_cases hlow : i < 32
  · simp [hlow]
  · by_cases hmid : i < 40
    · have hin : i - 32 < 8 := by omega
      have hn : ¬ 40 ≤ i := by omega
      simp [hlow, hn]
      simpa [hin] using (BitVec.getLsbD_allOnes (v := 8) (i := i - 32))
    · have hout : 8 ≤ i - 32 := by omega
      have hp : 40 ≤ i := by omega
      simp [hlow, hp, BitVec.getLsbD_allOnes, hout]

private theorem replace32 (lo : BitVec 32) (old new : BitVec 8) :
    replaceByte (lo.zeroExtend 64 + ((old.zeroExtend 64) <<< 32)) 4 new =
      lo.zeroExtend 64 + ((new.zeroExtend 64) <<< 32) := by
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ (low_shift_disjoint lo old),
      BitVec.add_eq_or_of_and_eq_zero _ _ (low_shift_disjoint lo new)]
  unfold replaceByte
  ext i (hi : i < 64)
  simp [BitVec.zeroExtend]
  rw [mask_four i hi]
  by_cases hlow : i < 32
  · simp [hlow]
  · have lozero : lo.getLsbD i = false := BitVec.getLsbD_of_ge lo i (by omega)
    by_cases hmid : i < 40
    · have hn : ¬ (i < 32 ∨ 40 ≤ i) := by omega
      simp [hlow, hn, lozero]
      omega
    · have oldzero : old.getLsbD (i - 32) = false :=
        BitVec.getLsbD_of_ge old (i - 32) (by omega)
      have newzero : new.getLsbD (i - 32) = false :=
        BitVec.getLsbD_of_ge new (i - 32) (by omega)
      simp [hlow, lozero, oldzero, newzero]
private theorem byte64 (b : BitVec 8) :
    b.zeroExtend 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]

private theorem prefix32 (l f c : BitVec 8) :
    2#64 + ((l.zeroExtend 64) <<< 8) + ((f.zeroExtend 64) <<< 16) +
      ((c.zeroExtend 64) <<< 24) =
      (BitVec.ofNat 32 (2 + l.toNat * 2^8 + f.toNat * 2^16 + c.toNat * 2^24)).zeroExtend 64 := by
  simp only [byte64, KeygenDomain.shift_ofNat, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hl := l.isLt
  have hf := f.isLt
  have hc := c.isLt
  omega

private theorem prefix24 (l f : BitVec 8) :
    2#64 + ((l.zeroExtend 64) <<< 8) + ((f.zeroExtend 64) <<< 16) =
      (BitVec.ofNat 24 (2 + l.toNat * 2^8 + f.toNat * 2^16)).zeroExtend 64 := by
  simp only [byte64, KeygenDomain.shift_ofNat, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hl := l.isLt
  have hf := f.isLt
  omega

private theorem low_chain_disjoint (lo : BitVec 24) (b : BitVec 8) :
    (lo.zeroExtend 64) &&& ((b.zeroExtend 64) <<< 24) = 0#64 := by
  ext i (hi : i < 64)
  simp [BitVec.zeroExtend]
  intro hlow hhigh
  have hzero : lo.getLsbD i = false := BitVec.getLsbD_of_ge lo i (by omega)
  simp [hzero] at hlow

private theorem low_step_disjoint (lo : BitVec 24) (b : BitVec 8) :
    (lo.zeroExtend 64) &&& ((b.zeroExtend 64) <<< 32) = 0#64 := by
  ext i (hi : i < 64)
  simp [BitVec.zeroExtend]
  intro hlow hhigh
  have hzero : lo.getLsbD i = false := BitVec.getLsbD_of_ge lo i (by omega)
  simp [hzero] at hlow

private theorem chain_step_disjoint (chain step : BitVec 8) :
    ((chain.zeroExtend 64) <<< 24) &&& ((step.zeroExtend 64) <<< 32) = 0#64 := by
  ext i (hi : i < 64)
  simp [BitVec.zeroExtend]
  intro h24 hchain h32
  have hzero : chain.getLsbD (i - 24) = false :=
    BitVec.getLsbD_of_ge chain (i - 24) (by omega)
  simp [hzero] at hchain

private theorem combined_step_disjoint (lo : BitVec 24) (chain step : BitVec 8) :
    (lo.zeroExtend 64 + ((chain.zeroExtend 64) <<< 24)) &&&
      ((step.zeroExtend 64) <<< 32) = 0#64 := by
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ (low_chain_disjoint lo chain)]
  rw [BitVec.and_or_distrib_right]
  simp [low_step_disjoint, chain_step_disjoint]

private theorem mask_three (i : Nat) (hi : i < 64) :
    (18446744069431361535#64)[i] = decide (i < 24 ∨ 32 ≤ i) := by
  change (~~~ (((BitVec.allOnes 8).zeroExtend 64) <<< 24))[i] =
      decide (i < 24 ∨ 32 ≤ i)
  simp only [BitVec.getElem_not, BitVec.getElem_shiftLeft,
    BitVec.getElem_setWidth]
  by_cases hlow : i < 24
  · simp [hlow]
  · by_cases hmid : i < 32
    · have hin : i - 24 < 8 := by omega
      have hn : ¬ 32 ≤ i := by omega
      simp [hlow, hn]
      simpa [hin] using (BitVec.getLsbD_allOnes (v := 8) (i := i - 24))
    · have hout : 8 ≤ i - 24 := by omega
      have hp : 32 ≤ i := by omega
      simp [hlow, hp, hout]

private theorem norm_three (lo : BitVec 24) (chain step : BitVec 8) :
    lo.zeroExtend 64 + ((chain.zeroExtend 64) <<< 24) + ((step.zeroExtend 64) <<< 32) =
      lo.zeroExtend 64 ||| ((chain.zeroExtend 64) <<< 24) |||
        ((step.zeroExtend 64) <<< 32) := by
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ (combined_step_disjoint lo chain step),
      BitVec.add_eq_or_of_and_eq_zero _ _ (low_chain_disjoint lo chain)]

private theorem replace_chain64 (lo : BitVec 24) (oldChain step newChain : BitVec 8) :
    replaceByte
      (lo.zeroExtend 64 + ((oldChain.zeroExtend 64) <<< 24) +
        ((step.zeroExtend 64) <<< 32)) 3 newChain =
      lo.zeroExtend 64 + ((newChain.zeroExtend 64) <<< 24) +
        ((step.zeroExtend 64) <<< 32) := by
  rw [norm_three lo oldChain step, norm_three lo newChain step]
  unfold replaceByte
  ext i (hi : i < 64)
  simp [BitVec.zeroExtend]
  rw [mask_three i hi]
  by_cases hlow : i < 24
  · simp [hlow]
  · have lozero : lo.getLsbD i = false := BitVec.getLsbD_of_ge lo i (by omega)
    by_cases hmid : i < 32
    · simp [hlow, hmid, lozero]
    · have oldzero : oldChain.getLsbD (i - 24) = false :=
        BitVec.getLsbD_of_ge oldChain (i - 24) (by omega)
      have newzero : newChain.getLsbD (i - 24) = false :=
        BitVec.getLsbD_of_ge newChain (i - 24) (by omega)
      simp [hlow, hmid, lozero, oldzero, newzero]
      omega


theorem replace_step_bv (l f c st : BitVec 8) :
    replaceByte
      (2#64 + ((l.zeroExtend 64) <<< 8) + ((f.zeroExtend 64) <<< 16) +
        ((c.zeroExtend 64) <<< 24) + ((st.zeroExtend 64) <<< 32))
      4 (st + 1) =
      2#64 + ((l.zeroExtend 64) <<< 8) + ((f.zeroExtend 64) <<< 16) +
        ((c.zeroExtend 64) <<< 24) + (((st + 1).zeroExtend 64) <<< 32) := by
  simp only [prefix32]
  exact replace32 _ st (st + 1)

private theorem cast8 (n : Nat) (h : n < 256) :
    (BitVec.ofNat 8 n).zeroExtend 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem header_unpack (level leaf chain step : Nat)
    (hl : level < 256) (hf : leaf < 256) (hc : chain < 256) (hs : step < 256) :
    KeygenDomain.header 2 level leaf chain step =
      2#64 + (((BitVec.ofNat 8 level).zeroExtend 64) <<< 8) +
        (((BitVec.ofNat 8 leaf).zeroExtend 64) <<< 16) +
        (((BitVec.ofNat 8 chain).zeroExtend 64) <<< 24) +
        (((BitVec.ofNat 8 step).zeroExtend 64) <<< 32) := by
  simp only [KeygenDomain.header, BitVec.ofNat_add]
  rw [← KeygenDomain.shift_ofNat level 8, ← KeygenDomain.shift_ofNat leaf 16,
    ← KeygenDomain.shift_ofNat chain 24, ← KeygenDomain.shift_ofNat step 32]
  rw [← cast8 level hl, ← cast8 leaf hf, ← cast8 chain hc, ← cast8 step hs]

theorem header_step_replace (level leaf chain step : Nat)
    (hl : level < 256) (hf : leaf < 256) (hc : chain < 256) (hs : step < 255) :
    replaceByte (KeygenDomain.header 2 level leaf chain step) 4
      (BitVec.ofNat 8 (step+1)) =
      KeygenDomain.header 2 level leaf chain (step+1) := by
  rw [header_unpack level leaf chain step hl hf hc (by omega),
    header_unpack level leaf chain (step+1) hl hf hc (by omega)]
  simpa [BitVec.ofNat_add] using
    replace_step_bv (BitVec.ofNat 8 level) (BitVec.ofNat 8 leaf)
      (BitVec.ofNat 8 chain) (BitVec.ofNat 8 step)

theorem replace_chain_step_bv (l f oldChain oldStep newChain newStep : BitVec 8) :
    replaceByte
      (replaceByte
        (2#64 + ((l.zeroExtend 64) <<< 8) + ((f.zeroExtend 64) <<< 16) +
          ((oldChain.zeroExtend 64) <<< 24) + ((oldStep.zeroExtend 64) <<< 32))
        3 newChain)
      4 newStep =
      2#64 + ((l.zeroExtend 64) <<< 8) + ((f.zeroExtend 64) <<< 16) +
        ((newChain.zeroExtend 64) <<< 24) + ((newStep.zeroExtend 64) <<< 32) := by
  rw [prefix24 l f]
  rw [replace_chain64]
  rw [← prefix24 l f]
  rw [prefix32 l f newChain]
  exact replace32 _ oldStep newStep

theorem header_chain_step_replace (level leaf oldChain oldStep newChain newStep : Nat)
    (hl : level < 256) (hf : leaf < 256)
    (hoc : oldChain < 256) (hos : oldStep < 256)
    (hnc : newChain < 256) (hns : newStep < 256) :
    replaceByte
      (replaceByte (KeygenDomain.header 2 level leaf oldChain oldStep) 3
        (BitVec.ofNat 8 newChain))
      4 (BitVec.ofNat 8 newStep) =
      KeygenDomain.header 2 level leaf newChain newStep := by
  rw [header_unpack level leaf oldChain oldStep hl hf hoc hos,
    header_unpack level leaf newChain newStep hl hf hnc hns]
  exact replace_chain_step_bv (BitVec.ofNat 8 level) (BitVec.ofNat 8 leaf)
    (BitVec.ofNat 8 oldChain) (BitVec.ofNat 8 oldStep)
    (BitVec.ofNat 8 newChain) (BitVec.ofNat 8 newStep)

def HeaderWordCarry (s : MachineState) (level tree leaf : Nat) : Prop :=
  ∃ oldChain oldStep : Nat, oldChain < 46 ∧ oldStep < 8 ∧
    s.getMem 0x80000 = KeygenDomain.header 2 level leaf oldChain oldStep ∧
    (∀ i : Fin 3, s.getMem (wordAddress 0x80008 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64) ∧
    s.getReg .x5 = 1 ∧ s.getReg .x12 = 0x80020 ∧ s.getReg .x31 = 7

def HeaderReadyWord (s : MachineState) (level tree leaf next : Nat) : Prop :=
  next = 0 ∨ HeaderWordCarry s level tree leaf

theorem partial_mem (s : MachineState) (a : Word) :
    (partialState s).getMem a =
      if a = 0x80000 then
        replaceByte (replaceByte (s.getMem 0x80000) 3 ((s.getReg .x6).truncate 8))
          4 ((s.getReg .x30).truncate 8)
      else s.getMem a := by
  by_cases h : a = 0x80000
  · subst a
    simp [partialState, execInstrBr, signExtend12, MachineState.setByte,
      Expansion.mem_setMem, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      alignToDword, byteOffset]
  · simp [partialState, execInstrBr, signExtend12, MachineState.setByte,
      Expansion.mem_setMem, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      alignToDword, byteOffset]
    split_ifs <;> simp_all

theorem partial_word_carry (s : MachineState) (level tree leaf chain step : Nat)
    (carry : HeaderWordCarry s level tree leaf)
    (hl : level < 256) (hf : leaf < 256)
    (hc : chain < 46) (hs : step < 8)
    (chainReg : s.getReg .x6 = BitVec.ofNat 64 chain)
    (stepReg : s.getReg .x30 = BitVec.ofNat 64 step) :
    HeaderWordCarry (partialState s) level tree leaf := by
  rcases carry with ⟨oldChain,oldStep,oldChainBound,oldStepBound,head,index,r5,r12,r31⟩
  refine ⟨chain,step,hc,hs,?_,?_,?_,?_,?_⟩
  · rw [partial_mem, if_pos rfl, head, chainReg, stepReg]
    simpa only [BitVec.truncate_eq_setWidth,
      BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64)] using
      (header_chain_step_replace level leaf oldChain oldStep chain step hl hf
        (by omega) (by omega) (by omega) (by omega))
  · intro i
    rw [partial_mem, if_neg (by fin_cases i <;> decide)]
    exact index i
  · exact (partial_regs s).1.trans r5
  · exact (partial_regs s).2.2.2.1.trans r12
  · exact (partial_regs s).2.2.2.2.2.trans r31

end SigGolfCandidate.Hypertree.Verifying.Hoist
