import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedHandoff67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperUnselectedHandoff67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedSuffix67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedGroupLeaves67. -/
section
/-! The chosen WOTS signature survives every subsequent leaf in its upper
Merkle group. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedSuffix67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
noncomputable section
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev witnessSlot :=
  GroupedBalancedSignUpperH2WitnessFrame67.slot
private abbrev digitAddress :=
  GroupedBalancedSignUpperH2WitnessFrame67.digitAddress
private abbrev Inv := GroupedBalancedSignUpperLeafFold67.Inv

theorem later_unequal (height selected index : Nat)
    (hh : height=3 ∨ height=4)
    (hselected : selected < index)
    (hindex : index<2^height) :
    BitVec.ofNat 64 index≠BitVec.ofNat 64 selected := by
  intro eq
  have hn := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat] at hn
  have indexSmall : index<2^64 := by
    rcases hh with rfl | rfl <;> omega
  have selectedSmall : selected < 2^64 := by omega
  rw [Nat.mod_eq_of_lt indexSmall,
    Nat.mod_eq_of_lt selectedSmall] at hn
  omega

theorem run_later (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected witnessBase startIndex : Nat)
    (start : MachineState)
    (hh : height=3 ∨ height=4)
    (baseBound : treeBase<256)
    (aligned : leafBase%2^height=0)
    (bound : leafBase+2^height≤2^160)
    (selectedBefore : selected < startIndex)
    (startBound : startIndex≤2^height)
    (initial : Inv hash secretKey treeBase leafBase height selected
      witnessBase startIndex start) :
    ∀ k : Nat, startIndex+k≤2^height →
      ∃ (n c : Nat) (final : MachineState),
        Trace hash image start n c (248*k) (265*k) final ∧
        Inv hash secretKey treeBase leafBase height selected witnessBase
          (startIndex+k) final ∧
        (∀ a : Word, a.toNat<0x80000 →
          final.getMem a=start.getMem a) ∧
        (∀ a : Word, GroupedBalancedSignUpperLeafPersistent67.Persistent a →
          final.getMem a=start.getMem a) ∧
        final.getReg .x2=start.getReg .x2 ∧
        n ≤ 36188*k ∧ c ≤ 41490*k := by
  intro k hk
  induction k with
  | zero =>
      exact ⟨0,0,start,by simpa using
        (Trace.refl (hash := hash) (image := image) start),
        by simpa using initial,by intros; rfl,by intros; rfl,rfl,
        by omega,by omega⟩
  | succ k ih =>
      obtain ⟨n,c,mid,pretrace,midInv,midFrame,midPersistent,midSp,
        nBound,cBound⟩ :=
        ih (by omega)
      have stepBound : startIndex+k<2^height := by omega
      have selectedEarlier : selected < startIndex+k := by omega
      have different : mid.getMem 0x810e0≠mid.getMem 0x810e8 := by
        rw [midInv.data.count,midInv.data.chosen]
        exact later_unequal height selected (startIndex+k) hh
          selectedEarlier stepBound
      obtain ⟨sn,sc,final,step,finalInv,stepFrame,_stepDigits,
        _stepCurrent,stepPersistent,stepSp,snBound,scBound⟩ :=
        GroupedBalancedSignUpperUnselectedHandoff67.unselected_leaf hash
          secretKey treeBase leafBase height selected witnessBase
          (startIndex+k) mid hh baseBound aligned bound stepBound
          midInv different
      refine ⟨n+sn,c+sc,final,?_,?_,?_,?_,stepSp.trans midSp,
        by omega,by omega⟩
      · simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,
          Nat.add_left_comm] using pretrace.trans step
      · simpa [Nat.add_assoc] using finalInv
      · intro a low
        exact (stepFrame a low).trans (midFrame a low)
      · intro a persistent
        exact (stepPersistent a persistent).trans
          (midPersistent a persistent)

theorem selected_to_group_end (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected witnessBase : Nat)
    (message : Reference.Digest)
    (s : MachineState)
    (hh : height=3 ∨ height=4)
    (baseBound : treeBase<256)
    (aligned : leafBase%2^height=0)
    (bound : leafBase+2^height≤2^160)
    (hselected : selected < 2^height)
    (initial : Inv hash secretKey treeBase leafBase height selected
      witnessBase selected s)
    (digits : ∀ j : GroupedBalancedUpperTree67.ChainMixed,
      s.getByte (digitAddress j)=
        BitVec.ofNat 8
          (GroupedBalancedUpperTree67.digit message j).val) :
    ∃ (b n c : Nat) (final : MachineState),
      s.getMem 0x810f0=BitVec.ofNat 64 b ∧
      0x20060≤b ∧ b+16*67≤0x80000 ∧ b%8=0 ∧
      Trace hash image s n c
        (248*(2^height-selected))
        (265*(2^height-selected)) final ∧
      Inv hash secretKey treeBase leafBase height selected witnessBase
        (2^height) final ∧
      (∀ j : GroupedBalancedUpperTree67.ChainMixed, ∀ w : Fin 2,
        final.getMem (witnessSlot b j w)=
          (GroupedBalancedUpperTree67.signValues hash secretKey treeBase
            (leafBase+selected) message j).extractLsb'
              (64*w.val) 64) ∧
      (∀ a : Word, GroupedBalancedSignUpperLeafPersistent67.Persistent a →
        final.getMem a=s.getMem a) ∧
      (∀ a : Word, a.toNat<b → final.getMem a=s.getMem a) ∧
      final.getReg .x2=s.getReg .x2 ∧
      n ≤ 36188*(2^height-selected) ∧
      c ≤ 41490*(2^height-selected) := by
  obtain ⟨b,n,c,mid,bWord,bLower,bUpper,bAlign,chosenTrace,
    chosenInv,chosenWords,chosenPersistent,chosenPrior,chosenSp,
    chosenNBound,chosenCBound⟩ :=
    GroupedBalancedSignUpperSelectedHandoff67.selected_leaf hash
      secretKey treeBase leafBase height selected witnessBase message s
      hh baseBound aligned bound hselected initial digits
  have startBound : selected+1≤2^height := by omega
  let later := 2^height-(selected+1)
  obtain ⟨sn,sc,final,laterTrace,finalInv,laterFrame,laterPersistent,laterSp,
    laterNBound,laterCBound⟩ :=
    run_later hash secretKey treeBase leafBase height selected
      witnessBase (selected+1) mid hh baseBound aligned bound
      (by omega) startBound chosenInv later (by dsimp [later]; omega)
  have finalIndex : selected+1+later=2^height := by
    dsimp [later]
    omega
  have calls : 248+248*later=248*(2^height-selected) := by
    dsimp [later]
    omega
  have blocks : 265+265*later=265*(2^height-selected) := by
    dsimp [later]
    omega
  refine ⟨b,n+sn,c+sc,final,bWord,bLower,bUpper,bAlign,?_,?_,?_,?_,?_,
    laterSp.trans chosenSp,by omega,by omega⟩
  · simpa [calls,blocks] using chosenTrace.trans laterTrace
  · simpa only [finalIndex] using finalInv
  · intro j w
    rw [laterFrame _ (GroupedBalancedSignUpperWitnessSlots67.slot_bound
      b j w bLower bUpper).2]
    exact chosenWords j w
  · intro a persistent
    exact (laterPersistent a persistent).trans
      (chosenPersistent a persistent)
  · intro a before
    exact (laterFrame a (by omega : a.toNat<0x80000)).trans
      (chosenPrior a before)

#print axioms later_unequal
#print axioms run_later
#print axioms selected_to_group_end
end
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedSuffix67

end

/-! The decoded digits and the chosen WOTS signature survive the complete
upper-group leaf loop. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedGroupLeaves67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
noncomputable section
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev Inv := GroupedBalancedSignUpperLeafFold67.Inv
private abbrev digitAddress :=
  GroupedBalancedSignUpperH2WitnessFrame67.digitAddress
private abbrev witnessSlot :=
  GroupedBalancedSignUpperH2WitnessFrame67.slot

theorem run_before (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected witnessBase : Nat)
    (message : Reference.Digest) (start : MachineState)
    (hh : height=3 ∨ height=4)
    (baseBound : treeBase<256)
    (aligned : leafBase%2^height=0)
    (bound : leafBase+2^height≤2^160)
    (selectedBound : selected<2^height)
    (initial : Inv hash secretKey treeBase leafBase height selected
      witnessBase 0 start)
    (digits : ∀ j : GroupedBalancedUpperTree67.ChainMixed,
      start.getByte (digitAddress j)=
        BitVec.ofNat 8
          (GroupedBalancedUpperTree67.digit message j).val) :
    ∀ k : Nat, k ≤ selected →
      ∃ (n c : Nat) (mid : MachineState),
        Trace hash image start n c (248*k) (265*k) mid ∧
        Inv hash secretKey treeBase leafBase height selected witnessBase
          k mid ∧
        mid.getMem 0x810f0=start.getMem 0x810f0 ∧
        (∀ j : GroupedBalancedUpperTree67.ChainMixed,
          mid.getByte (digitAddress j)=
            BitVec.ofNat 8
              (GroupedBalancedUpperTree67.digit message j).val) ∧
        (∀ a : Word, GroupedBalancedSignUpperLeafPersistent67.Persistent a →
          mid.getMem a=start.getMem a) ∧
        (∀ a : Word, a.toNat<0x80000 →
          mid.getMem a=start.getMem a) ∧
        mid.getReg .x2=start.getReg .x2 ∧
        n ≤ 36188*k ∧ c ≤ 41490*k := by
  intro k
  induction k with
  | zero =>
      intro hk
      exact ⟨0,0,start,by simpa using
        (Trace.refl (hash := hash) (image := image) start),initial,rfl,
        digits,by intros; rfl,by intros; rfl,rfl,by omega,by omega⟩
  | succ k ih =>
      intro hk
      obtain ⟨n,c,mid,pretrace,midInv,midCurrent,midDigits,
        midPersistent,midLow,midSp,nBound,cBound⟩ :=
        ih (by omega)
      have stepBound : k<2^height := by omega
      have earlier : k<selected := by omega
      have different : mid.getMem 0x810e0≠mid.getMem 0x810e8 := by
        rw [midInv.data.count,midInv.data.chosen]
        exact (GroupedBalancedSignUpperSelectedSuffix67.later_unequal
          height k selected hh earlier selectedBound).symm
      obtain ⟨sn,sc,final,step,finalInv,stepLow,stepDigits,
        stepCurrent,stepPersistent,stepSp,snBound,scBound⟩ :=
        GroupedBalancedSignUpperUnselectedHandoff67.unselected_leaf hash
          secretKey treeBase leafBase height selected witnessBase k mid
          hh baseBound aligned bound stepBound midInv different
      have finalDigits : ∀ j : GroupedBalancedUpperTree67.ChainMixed,
          final.getByte (digitAddress j)=
            BitVec.ofNat 8
              (GroupedBalancedUpperTree67.digit message j).val := by
        intro j
        rw [GroupedBalancedSignUpperWitnessSlots67.digit_region_frame
          mid final j stepDigits]
        exact midDigits j
      refine ⟨n+sn,c+sc,final,?_,finalInv,stepCurrent.trans midCurrent,
        finalDigits,?_,?_,stepSp.trans midSp,by omega,by omega⟩
      simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        using pretrace.trans step
      intro a persistent
      exact (stepPersistent a persistent).trans
        (midPersistent a persistent)
      intro a low
      exact (stepLow a low).trans (midLow a low)

theorem all_leaves_witness (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected witnessBase : Nat)
    (message : Reference.Digest) (start : MachineState)
    (hh : height=3 ∨ height=4)
    (baseBound : treeBase<256)
    (aligned : leafBase%2^height=0)
    (bound : leafBase+2^height≤2^160)
    (selectedBound : selected<2^height)
    (initial : Inv hash secretKey treeBase leafBase height selected
      witnessBase 0 start)
    (digits : ∀ j : GroupedBalancedUpperTree67.ChainMixed,
      start.getByte (digitAddress j)=
        BitVec.ofNat 8
          (GroupedBalancedUpperTree67.digit message j).val) :
    ∃ (b n c : Nat) (final : MachineState),
      start.getMem 0x810f0=BitVec.ofNat 64 b ∧
      0x20060≤b ∧ b+16*67≤0x80000 ∧ b%8=0 ∧
      Trace hash image start n c (248*2^height) (265*2^height) final ∧
      Inv hash secretKey treeBase leafBase height selected witnessBase
        (2^height) final ∧
      (∀ j : GroupedBalancedUpperTree67.ChainMixed, ∀ w : Fin 2,
        final.getMem (witnessSlot b j w)=
          (GroupedBalancedUpperTree67.signValues hash secretKey treeBase
            (leafBase+selected) message j).extractLsb'
              (64*w.val) 64) ∧
      (∀ a : Word, GroupedBalancedSignUpperLeafPersistent67.Persistent a →
        final.getMem a=start.getMem a) ∧
      (∀ a : Word, a.toNat<b → final.getMem a=start.getMem a) ∧
      final.getReg .x2=start.getReg .x2 ∧
      n ≤ 36188*2^height ∧ c ≤ 41490*2^height := by
  obtain ⟨n,c,mid,pretrace,midInv,midCurrent,midDigits,
    midPersistent,midLow,midSp,nBound,cBound⟩ :=
    run_before hash secretKey treeBase leafBase height selected
      witnessBase message start hh baseBound aligned bound selectedBound
      initial digits selected (by omega)
  obtain ⟨b,sn,sc,final,bWord,bLower,bUpper,bAlign,
    tailTrace,finalInv,finalWords,tailPersistent,tailPrior,tailSp,
    tailNBound,tailCBound⟩ :=
    GroupedBalancedSignUpperSelectedSuffix67.selected_to_group_end hash
      secretKey treeBase leafBase height selected witnessBase message
      mid hh baseBound aligned bound selectedBound midInv midDigits
  have calls : 248*selected+248*(2^height-selected)=248*2^height := by
    omega
  have blocks : 265*selected+265*(2^height-selected)=265*2^height := by
    omega
  refine ⟨b,n+sn,c+sc,final,midCurrent.symm.trans bWord,
    bLower,bUpper,bAlign,?_,finalInv,
    finalWords,?_,?_,tailSp.trans midSp,by omega,by omega⟩
  simpa [calls,blocks] using pretrace.trans tailTrace
  intro a persistent
  exact (tailPersistent a persistent).trans
    (midPersistent a persistent)
  intro a before
  exact (tailPrior a before).trans
    (midLow a (by omega : a.toNat<0x80000))

#print axioms run_before
#print axioms all_leaves_witness
end
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedGroupLeaves67
