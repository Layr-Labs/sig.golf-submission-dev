import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafTick67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomStackSlots67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafTickData67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomAddressStep67. -/
section
/-! The per-leaf loop preserves control data and stores its leaf hash. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafTickData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image

def StableAddress (a : Word) : Prop :=
  (a.toNat < 0x83000 ∨ 0x87000 ≤ a.toNat) ∧
  a ≠ 0x810e0 ∧ a ≠ 0x81008 ∧
  a ≠ 0x80000 ∧ a ≠ 0x80008 ∧ a ≠ 0x80010 ∧ a ≠ 0x80018 ∧
  (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80020 i.val) ∧
  (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80020 i.val) ∧
  (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) ∧
  (∀ i : Fin 2, a ≠ Signing.wordAddress 0x20080 i.val)

theorem leaf_tick_data (hash : Hash) (s : MachineState)
    (secretKey : SecretKey) (leaf : Nat)
    (pc : s.pc = 0x12cc)
    (counter : (s.getMem 0x810e0).toNat < 1024)
    (level : s.getMem 0x81000 = 0)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (keyWords : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    ∃ next : MachineState,
      Trace hash image s
        (if s.getMem 0x810e0 = s.getMem 0x810e8 then 166 else 149)
        (if s.getMem 0x810e0 = s.getMem 0x810e8 then 180 else 163)
        2 2 next ∧
      next.getMem 0x810e0 = s.getMem 0x810e0 + 1 ∧
      next.getMem 0x81008 = s.getMem 0x81008 + 1 ∧
      next.getMem 0x810e8 = s.getMem 0x810e8 ∧
      next.getMem 0x81000 = 0 ∧
      (∀ i : Fin 2,
        next.getMem (Signing.wordAddress 0x81010 i.val) =
          s.getMem (Signing.wordAddress 0x81010 i.val)) ∧
      (∀ i : Fin 4,
        next.getMem (Signing.wordAddress 0x20 i.val) =
          secretKey.extractLsb' (64*i.val) 64) ∧
      next.getMem (GroupedBalancedSignBottomStackBound67.stack0
        (s.getMem 0x810e0)) =
          (GroupedBottomTree.leafRoot hash secretKey leaf).extractLsb' 0 64 ∧
      next.getMem (GroupedBalancedSignBottomStackBound67.stack0
        (s.getMem 0x810e0) + 8) =
          (GroupedBottomTree.leafRoot hash secretKey leaf).extractLsb' 64 64 ∧
      (∀ j k : Nat, j < (s.getMem 0x810e0).toNat → k < 2 →
        next.getMem (GroupedBalancedSignBottomStackSlots67.slot j k) =
          s.getMem (GroupedBalancedSignBottomStackSlots67.slot j k)) ∧
      (∀ a : Word, StableAddress a → next.getMem a = s.getMem a) ∧
      next.pc =
        (if s.getMem 0x810e0 + 1 = (1024 : Word) then 0x14ec else 0x12cc) ∧
      (s.getMem 0x810e0 = s.getMem 0x810e8 →
        ∀ i : Fin 2,
          next.getMem (Signing.wordAddress 0x20080 i.val) =
            (GroupedBottomTree.secret hash secretKey leaf).extractLsb'
              (64*i.val) 64) ∧
      (s.getMem 0x810e0 ≠ s.getMem 0x810e8 →
        ∀ i : Fin 2,
          next.getMem (Signing.wordAddress 0x20080 i.val) =
            s.getMem (Signing.wordAddress 0x20080 i.val)) := by
  obtain ⟨seedReady,seeded,leafReady,leafAfter,next,trace,_,_,_,_,_,leafWords,
    count,addressLow,nextPc,nextEq,seedFrame,leafFrame,selectedWords,
    skippedWords⟩ :=
    GroupedBalancedSignBottomLeafTick67.leaf_tick hash s secretKey leaf
      pc counter level address keyWords
  have leafCounter : leafAfter.getMem 0x810e0 = s.getMem 0x810e0 := by
    rw [leafFrame 0x810e0 (by decide) (by decide) (by decide)
      (by decide) (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)]
    exact seedFrame 0x810e0 (by decide) (by decide) (by decide)
      (by decide) (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
  have leafBound : (leafAfter.getMem 0x810e0).toNat < 1024 := by
    rw [leafCounter]
    exact counter
  have keep (a : Word) (ha : a.toNat < 0x83000 ∨ 0x87000 ≤ a.toNat)
      (hc : a ≠ 0x810e0) (had : a ≠ 0x81008)
      (h0 : a ≠ 0x80000) (h1 : a ≠ 0x80008)
      (h2 : a ≠ 0x80010) (h3 : a ≠ 0x80018)
      (hkey : ∀ i : Fin 4, a ≠ Signing.wordAddress 0x80020 i.val)
      (hin : ∀ i : Fin 2, a ≠ Signing.wordAddress 0x80020 i.val)
      (hout : ∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val)
      (hwit : ∀ i : Fin 2, a ≠ Signing.wordAddress 0x20080 i.val) :
      next.getMem a = s.getMem a := by
    have ⟨st0,st8⟩ := GroupedBalancedSignBottomStackBound67.outside_stack
      (leafAfter.getMem 0x810e0) a leafBound ha
    rw [nextEq,GroupedBalancedSignBottomLeafAdvanceData67.advance_frame
        leafAfter leafBound a st0 st8 had hc,
      leafFrame a h0 h1 h2 h3 hin hout hwit,
      seedFrame a h0 h1 h2 h3 hkey hout]
  refine ⟨next,trace,count,addressLow,?_,?_,?_,?_,?_,?_,?_,?_,nextPc,
    selectedWords,skippedWords⟩
  · exact keep 0x810e8 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
  · rw [keep 0x81000 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)]
    exact level
  · intro i
    exact keep _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by intro j; fin_cases i <;> fin_cases j <;> decide)
      (by intro j; fin_cases i <;> fin_cases j <;> decide)
      (by intro j; fin_cases i <;> fin_cases j <;> decide)
      (by intro j; fin_cases i <;> fin_cases j <;> decide)
  · intro i
    rw [keep _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by intro j; fin_cases i <;> fin_cases j <;> decide)
      (by intro j; fin_cases i <;> fin_cases j <;> decide)
      (by intro j; fin_cases i <;> fin_cases j <;> decide)
      (by intro j; fin_cases i <;> fin_cases j <;> decide)]
    exact keyWords i
  · rw [nextEq,← leafCounter]
    have root0 : leafAfter.getMem 0x80300 =
        (GroupedBottomTree.leafRoot hash secretKey leaf).extractLsb' 0 64 := by
      have h := leafWords (0 : Fin 2)
      norm_num [Signing.wordAddress] at h
      exact h
    exact (GroupedBalancedSignBottomLeafAdvanceData67.advance_store0
      leafAfter leafBound).trans root0
  · rw [nextEq,← leafCounter]
    have root8 : leafAfter.getMem 0x80308 =
        (GroupedBottomTree.leafRoot hash secretKey leaf).extractLsb' 64 64 := by
      have h := leafWords (1 : Fin 2)
      norm_num [Signing.wordAddress] at h
      exact h
    exact (GroupedBalancedSignBottomLeafAdvanceData67.advance_store8
      leafAfter leafBound).trans root8
  · intro j k hj hk
    let a := GroupedBalancedSignBottomStackSlots67.slot j k
    have hjBound : j < 1024 := by omega
    have out (b : Word) (hb : b.toNat < 0x83000) : a ≠ b :=
      GroupedBalancedSignBottomStackSlots67.slot_ne_below j k hjBound hk b hb
    have n0 : a ≠ GroupedBalancedSignBottomStackBound67.stack0
        (leafAfter.getMem 0x810e0) := by
      rw [leafCounter,← GroupedBalancedSignBottomStackSlots67.slot_current0
        (s.getMem 0x810e0) counter]
      exact GroupedBalancedSignBottomStackSlots67.earlier_ne
        (s.getMem 0x810e0).toNat j k 0 counter hj hk (by decide)
    have n8 : a ≠ GroupedBalancedSignBottomStackBound67.stack0
        (leafAfter.getMem 0x810e0) + 8 := by
      rw [leafCounter,← GroupedBalancedSignBottomStackSlots67.slot_current1
        (s.getMem 0x810e0) counter]
      exact GroupedBalancedSignBottomStackSlots67.earlier_ne
        (s.getMem 0x810e0).toNat j k 1 counter hj hk (by decide)
    rw [nextEq,
      GroupedBalancedSignBottomLeafAdvanceData67.advance_frame
        leafAfter leafBound a n0 n8 (out 0x81008 (by decide))
        (out 0x810e0 (by decide)),
      leafFrame a (out 0x80000 (by decide))
        (out 0x80008 (by decide)) (out 0x80010 (by decide))
        (out 0x80018 (by decide))
        (by intro i; fin_cases i <;> exact out _ (by decide))
        (by intro i; fin_cases i <;> exact out _ (by decide))
        (by intro i; fin_cases i <;> exact out _ (by decide)),
      seedFrame a (out 0x80000 (by decide))
        (out 0x80008 (by decide)) (out 0x80010 (by decide))
        (out 0x80018 (by decide))
        (by intro i; fin_cases i <;> exact out _ (by decide))
        (by intro i; fin_cases i <;> exact out _ (by decide))]
  · intro a safe
    rcases safe with ⟨ha,hc,had,h0,h1,h2,h3,hkey,hin,hout,hwit⟩
    exact keep a ha hc had h0 h1 h2 h3 hkey hin hout hwit

#print axioms leaf_tick_data
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafTickData67

end

/-! Incrementing a leaf within one 1024-leaf tree never carries out of its low word. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomAddressStep67
open SigGolf
set_option maxRecDepth 8192
set_option maxHeartbeats 100000

private theorem div64 (leaf : Nat) (hm : leaf % 1024 < 1023) :
    (leaf + 1) / 18446744073709551616 = leaf / 18446744073709551616 := by
  have hmod : (leaf % 18446744073709551616) % 1024 = leaf % 1024 := by omega
  have hlow : leaf % 18446744073709551616 ≤ 18446744073709551614 := by omega
  omega

private theorem div128 (leaf : Nat) (hm : leaf % 1024 < 1023) :
    (leaf + 1) / 340282366920938463463374607431768211456 =
      leaf / 340282366920938463463374607431768211456 := by
  have hmod : (leaf % 340282366920938463463374607431768211456) % 1024 =
      leaf % 1024 := by omega
  have hlow : leaf % 340282366920938463463374607431768211456 ≤
      340282366920938463463374607431768211454 := by omega
  omega

theorem low_step (leaf : Nat) (h : leaf < 2^160)
    (hm : leaf % 1024 < 1023) :
    (BitVec.ofNat 192 (leaf + 1)).extractLsb' 0 64 =
      (BitVec.ofNat 192 leaf).extractLsb' 0 64 + 1 := by
  apply BitVec.toNat_inj.mp
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_add,
    Nat.shiftRight_zero]
  have h192 : leaf + 1 < 2^192 := by omega
  have h192b : leaf < 2^192 := by omega
  rw [Nat.mod_eq_of_lt h192, Nat.mod_eq_of_lt h192b]
  have hone : (1 : BitVec 64).toNat = 1 := rfl
  rw [hone]
  omega

theorem middle_step (leaf : Nat) (h : leaf < 2^160)
    (hm : leaf % 1024 < 1023) :
    (BitVec.ofNat 192 (leaf + 1)).extractLsb' 64 64 =
      (BitVec.ofNat 192 leaf).extractLsb' 64 64 := by
  apply BitVec.toNat_inj.mp
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hh := div64 leaf hm
  omega

theorem high_step (leaf : Nat) (h : leaf < 2^160)
    (hm : leaf % 1024 < 1023) :
    (BitVec.ofNat 192 (leaf + 1)).extractLsb' 128 64 =
      (BitVec.ofNat 192 leaf).extractLsb' 128 64 := by
  apply BitVec.toNat_inj.mp
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hh := div128 leaf hm
  omega

#print axioms low_step
#print axioms middle_step
#print axioms high_step
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomAddressStep67
