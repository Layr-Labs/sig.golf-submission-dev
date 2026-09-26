import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperPostFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedGroupTree67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperPostGroup67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperPostStack67


/-! The post-root index/layer update is disjoint from all signature words
before the new Merkle authentication area. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedPostFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

theorem before (hash : Hash) (s final : MachineState)
    (index : BitVec 192) (height : Nat)
    (pc : s.pc=0x1c34)
    (valid0 : accessValid (s.getMem 0x810c0) 8=true)
    (valid8 : accessValid (s.getMem 0x810c0+8) 8=true)
    (hh : height=3 ∨ height=4)
    (limit : s.getMem 0x81060=BitVec.ofNat 64 height)
    (selected : ∀ w : Fin 3,
      s.getMem (Signing.wordAddress 0x81090 w.val)=
        index.extractLsb' (64*w.val) 64)
    (trace : Trace hash image s
      (24+36*height+
        (if s.getMem 0x81058+1=(30:Word) then 15 else 11))
      (24+36*height+
        (if s.getMem 0x81058+1=(30:Word) then 15 else 11))
      0 0 final)
    (a : Word) (low : a.toNat<0x80000) :
    final.getMem a=s.getMem a := by
  have ne (b : Word) (hb : 0x80000≤b.toNat) : a≠b := by
    intro eq
    subst a
    omega
  apply GroupedBalancedSignUpperPostFrame67.run_frame hash s final
    index height pc valid0 valid8 hh limit selected trace a
  exact ⟨ne 0x80500 (by decide),ne 0x80508 (by decide),
    ne 0x810f0 (by decide),ne 0x81100 (by decide),
    ne 0x81090 (by decide),ne 0x81098 (by decide),
    ne 0x810a0 (by decide),ne 0x81058 (by decide),
    ne 0x81060 (by decide)⟩

#print axioms before
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedPostFrame67


/-! The chosen WOTS signature survives the complete upper group, including
the post-root index shift and next-layer update. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedGroupComplete67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeParentData67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
noncomputable section
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev Inv := GroupedBalancedSignUpperLeafFold67.Inv
private abbrev digitAddress :=
  GroupedBalancedSignUpperH2WitnessFrame67.digitAddress
private abbrev slot := GroupedBalancedSignUpperH2WitnessFrame67.slot

def cost (s : MachineState) (height : Nat) : Nat :=
  24+36*height+
    (if s.getMem 0x81058+1=(30:Word) then 15 else 11)

private theorem outside_far (a : Word)
    (far : a.toNat<0x100 ∨ 0xfff700≤a.toNat) :
    GroupedBalancedSignUpperPostFrame67.Outside a := by
  have ne (b : Word) (low : 0x100≤b.toNat)
      (high : b.toNat<0x90000) : a≠b := by
    intro eq
    subst a
    rcases far with below | above <;> omega
  exact ⟨ne 0x80500 (by decide) (by decide),
    ne 0x80508 (by decide) (by decide),
    ne 0x810f0 (by decide) (by decide),
    ne 0x81100 (by decide) (by decide),
    ne 0x81090 (by decide) (by decide),
    ne 0x81098 (by decide) (by decide),
    ne 0x810a0 (by decide) (by decide),
    ne 0x81058 (by decide) (by decide),
    ne 0x81060 (by decide) (by decide)⟩

theorem height3 (hash : Hash) (secretKey : SecretKey)
    (treeBase rootAddress witnessBase selected wotsBase : Nat)
    (message : Reference.Digest) (index : BitVec 192)
    (start : MachineState)
    (initial : Inv hash secretKey treeBase (rootAddress*2^3) 3 selected
      witnessBase 0 start)
    (startSp : start.getReg .x2=0xfff700)
    (digits : ∀ j : GroupedBalancedUpperTree67.ChainMixed,
      start.getByte (digitAddress j)=
        BitVec.ofNat 8 (GroupedBalancedUpperTree67.digit message j).val)
    (current : start.getMem 0x810f0=BitVec.ofNat 64 wotsBase)
    (selectedWords : ∀ w : Fin 3,
      start.getMem (Signing.wordAddress 0x81090 w.val)=
        index.extractLsb' (64*w.val) 64)
    (witnessNext : witnessBase=wotsBase+16*67)
    (aligned : (rootAddress*2^3)%2^3=0)
    (bound : rootAddress*2^3+2^3≤2^160)
    (leafBound : rootAddress*2^3<2^192)
    (params : Params (rootAddress*2^3) 0 4 0x83000 0x88000
      ((rootAddress*2^3)/2))
    (chosenBound : selected<2^3)
    (treeBound : treeBase+3<2^64)
    (baseBound : treeBase<256)
    (witnessBound : witnessBase+16*3+16≤0x80000)
    (witnessAligned : witnessBase%8=0) :
    ∃ (n c : Nat) (final : MachineState),
      Trace hash image start (n+957+cost start 3)
        (c+1006+cost start 3) 1991 2127 final ∧
      final.pc=
        (if start.getMem 0x81058+1=(45:Word) then 0x1d60 else 0x15e0) ∧
      (∀ j : GroupedBalancedUpperTree67.ChainMixed, ∀ w : Fin 2,
        final.getMem (slot wotsBase j w)=
          (GroupedBalancedUpperTree67.signValues hash secretKey treeBase
            (rootAddress*2^3+selected) message j).extractLsb'
              (64*w.val) 64) ∧
      (∀ a : Word, a.toNat<wotsBase → final.getMem a=start.getMem a) ∧
      (∀ level, level<3 → ∀ i : Fin 2,
        final.getMem (BitVec.ofNat 64 (witnessBase+16*level+8*i.val))=
          (GroupedBalancedSignUpperTreeModel67.nodeAt hash treeBase
            (rootAddress*2^3)
            (fun k => GroupedBalancedUpperTree67.leafRoot hash secretKey
              treeBase (rootAddress*2^3+k)) level
            (Nat.xor (selected/2^level) 1)).extractLsb'
              (64*i.val) 64) ∧
      (∀ w : Fin 2,
        final.getMem (BitVec.ofNat 64 (0x80500+8*w.val))=
          (GroupedBalancedUpperTree67.root hash secretKey treeBase 3
            rootAddress).extractLsb' (64*w.val) 64) ∧
      final.getMem 0x81058=start.getMem 0x81058+1 ∧
      final.getMem 0x81060=
        (if start.getMem 0x81058+1=(30 : Word) then 4 else
          BitVec.ofNat 64 3) ∧
      final.getMem 0x810f0=BitVec.ofNat 64 witnessBase+(3#64 <<< 4) ∧
      (∀ w : Fin 3,
        final.getMem (Signing.wordAddress 0x81090 w.val)=
          (index >>> 3).extractLsb' (64*w.val) 64) ∧
      final.getReg .x2=start.getReg .x2 ∧
      (∀ a : Word, a.toNat<0x100 → final.getMem a=start.getMem a) ∧
      final.getMem 0x81000=BitVec.ofNat 64 (treeBase+3) ∧
      (∀ a : Word, 0xfff700≤a.toNat →
        final.getMem a=start.getMem a) ∧
      n ≤ 600000 ∧ c ≤ 700000 := by
  obtain ⟨n,c,rooted,groupTrace,groupPc,rootPtr,groupHeight,
    groupLayer,groupIndex,groupWitness,groupPrior,groupSiblings,
    groupSp,rootWords,groupFrame,treeWord,nBound,cBound⟩ :=
    GroupedBalancedSignUpperSelectedGroupTree67.height3 hash secretKey
      treeBase rootAddress witnessBase selected wotsBase message index start
      initial startSp digits current selectedWords witnessNext aligned bound leafBound
      params chosenBound treeBound baseBound witnessBound witnessAligned
  have valid0 : accessValid (rooted.getMem 0x810c0) 8=true := by
    rw [rootPtr]
    decide
  have valid8 : accessValid (rooted.getMem 0x810c0+8) 8=true := by
    rw [rootPtr]
    decide
  obtain ⟨final,postTrace,postPc,post0,post8,postLayer,postHeight,
    postCurrent,postIndex⟩ :=
    GroupedBalancedSignUpperPostGroup67.run hash rooted 0x88000 index 3
      groupPc valid0 valid8 rootPtr (Or.inl rfl) groupHeight groupIndex
  have groupF8 : rooted.getMem 0x810f8=BitVec.ofNat 64 witnessBase := by
    rw [groupFrame 0x810f8
      (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl rfl)))))]
    exact initial.witness
  have postSp := GroupedBalancedSignUpperPostStack67.post_group_sp hash
    rooted final index 3 groupPc valid0 valid8 (Or.inl rfl) groupHeight
    groupIndex postTrace
  have postTree : final.getMem 0x81000=rooted.getMem 0x81000 :=
    GroupedBalancedSignUpperPostFrame67.run_frame hash rooted final index 3
      groupPc valid0 valid8 (Or.inl rfl) groupHeight groupIndex postTrace
      0x81000 (by simp [GroupedBalancedSignUpperPostFrame67.Outside])
  refine ⟨n,c,final,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,
    nBound,cBound⟩
  · have combined := groupTrace.trans postTrace
    have exactLayer : rooted.getMem (528472#64)=
        start.getMem (528472#64) := groupLayer
    simpa [cost,exactLayer,Nat.add_assoc] using combined
  · simpa only [groupLayer] using postPc
  · intro j w
    have expectedUpper : wotsBase+16*67≤0x80000 := by omega
    have before :=
      GroupedBalancedSignUpperSelectedSlotSchedule67.slot_before_merkle
        wotsBase j w expectedUpper
    change (slot wotsBase j w).toNat<wotsBase+1072 at before
    have low : (slot wotsBase j w).toNat<0x80000 := by omega
    rw [GroupedBalancedSignUpperSelectedPostFrame67.before hash rooted
      final index 3 groupPc valid0 valid8 (Or.inl rfl) groupHeight
      groupIndex postTrace (slot wotsBase j w) low]
    exact groupWitness j w
  · intro a before
    have low : a.toNat<0x80000 := by omega
    rw [GroupedBalancedSignUpperSelectedPostFrame67.before hash rooted
      final index 3 groupPc valid0 valid8 (Or.inl rfl) groupHeight
      groupIndex postTrace a low]
    exact groupPrior a before
  · intro level levelBound i
    have low : (BitVec.ofNat 64 (witnessBase+16*level+8*i.val)).toNat<
        0x80000 := by
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega :
        witnessBase+16*level+8*i.val<2^64)]
      omega
    rw [GroupedBalancedSignUpperSelectedPostFrame67.before hash rooted
      final index 3 groupPc valid0 valid8 (Or.inl rfl) groupHeight
      groupIndex postTrace _ low]
    exact groupSiblings level levelBound i
  · intro w
    fin_cases w
    · simpa using post0.trans (rootWords ⟨0,by decide⟩)
    · simpa using post8.trans (rootWords ⟨1,by decide⟩)
  · simpa only [groupLayer] using postLayer
  · simpa only [groupLayer] using postHeight
  · simpa only [groupF8] using postCurrent
  · exact postIndex
  · exact postSp.trans groupSp
  · intro a low
    have post := GroupedBalancedSignUpperPostFrame67.run_frame hash rooted
      final index 3 groupPc valid0 valid8 (Or.inl rfl) groupHeight
      groupIndex postTrace a (outside_far a (Or.inl low))
    exact post.trans (groupFrame a (Or.inl low))
  · exact postTree.trans treeWord
  · intro a high
    have post := GroupedBalancedSignUpperPostFrame67.run_frame hash rooted
      final index 3 groupPc valid0 valid8 (Or.inl rfl) groupHeight
      groupIndex postTrace a (outside_far a (Or.inr high))
    exact post.trans (groupFrame a (Or.inr (Or.inr high)))

theorem height4 (hash : Hash) (secretKey : SecretKey)
    (treeBase rootAddress witnessBase selected wotsBase : Nat)
    (message : Reference.Digest) (index : BitVec 192)
    (start : MachineState)
    (initial : Inv hash secretKey treeBase (rootAddress*2^4) 4 selected
      witnessBase 0 start)
    (startSp : start.getReg .x2=0xfff700)
    (digits : ∀ j : GroupedBalancedUpperTree67.ChainMixed,
      start.getByte (digitAddress j)=
        BitVec.ofNat 8 (GroupedBalancedUpperTree67.digit message j).val)
    (current : start.getMem 0x810f0=BitVec.ofNat 64 wotsBase)
    (selectedWords : ∀ w : Fin 3,
      start.getMem (Signing.wordAddress 0x81090 w.val)=
        index.extractLsb' (64*w.val) 64)
    (witnessNext : witnessBase=wotsBase+16*67)
    (aligned : (rootAddress*2^4)%2^4=0)
    (bound : rootAddress*2^4+2^4≤2^160)
    (leafBound : rootAddress*2^4<2^192)
    (params : Params (rootAddress*2^4) 0 8 0x83000 0x88000
      ((rootAddress*2^4)/2))
    (chosenBound : selected<2^4)
    (treeBound : treeBase+4<2^64)
    (baseBound : treeBase<256)
    (witnessBound : witnessBase+16*4+16≤0x80000)
    (witnessAligned : witnessBase%8=0) :
    ∃ (n c : Nat) (final : MachineState),
      Trace hash image start (n+1743+cost start 4)
        (c+1848+cost start 4) 3983 4255 final ∧
      final.pc=
        (if start.getMem 0x81058+1=(45:Word) then 0x1d60 else 0x15e0) ∧
      (∀ j : GroupedBalancedUpperTree67.ChainMixed, ∀ w : Fin 2,
        final.getMem (slot wotsBase j w)=
          (GroupedBalancedUpperTree67.signValues hash secretKey treeBase
            (rootAddress*2^4+selected) message j).extractLsb'
              (64*w.val) 64) ∧
      (∀ a : Word, a.toNat<wotsBase → final.getMem a=start.getMem a) ∧
      (∀ level, level<4 → ∀ i : Fin 2,
        final.getMem (BitVec.ofNat 64 (witnessBase+16*level+8*i.val))=
          (GroupedBalancedSignUpperTreeModel67.nodeAt hash treeBase
            (rootAddress*2^4)
            (fun k => GroupedBalancedUpperTree67.leafRoot hash secretKey
              treeBase (rootAddress*2^4+k)) level
            (Nat.xor (selected/2^level) 1)).extractLsb'
              (64*i.val) 64) ∧
      (∀ w : Fin 2,
        final.getMem (BitVec.ofNat 64 (0x80500+8*w.val))=
          (GroupedBalancedUpperTree67.root hash secretKey treeBase 4
            rootAddress).extractLsb' (64*w.val) 64) ∧
      final.getMem 0x81058=start.getMem 0x81058+1 ∧
      final.getMem 0x81060=
        (if start.getMem 0x81058+1=(30 : Word) then 4 else
          BitVec.ofNat 64 4) ∧
      final.getMem 0x810f0=BitVec.ofNat 64 witnessBase+(4#64 <<< 4) ∧
      (∀ w : Fin 3,
        final.getMem (Signing.wordAddress 0x81090 w.val)=
          (index >>> 4).extractLsb' (64*w.val) 64) ∧
      final.getReg .x2=start.getReg .x2 ∧
      (∀ a : Word, a.toNat<0x100 → final.getMem a=start.getMem a) ∧
      final.getMem 0x81000=BitVec.ofNat 64 (treeBase+4) ∧
      (∀ a : Word, 0xfff700≤a.toNat →
        final.getMem a=start.getMem a) ∧
      n ≤ 600000 ∧ c ≤ 700000 := by
  obtain ⟨n,c,rooted,groupTrace,groupPc,rootPtr,groupHeight,
    groupLayer,groupIndex,groupWitness,groupPrior,groupSiblings,
    groupSp,rootWords,groupFrame,treeWord,nBound,cBound⟩ :=
    GroupedBalancedSignUpperSelectedGroupTree67.height4 hash secretKey
      treeBase rootAddress witnessBase selected wotsBase message index start
      initial startSp digits current selectedWords witnessNext aligned bound leafBound
      params chosenBound treeBound baseBound witnessBound witnessAligned
  have valid0 : accessValid (rooted.getMem 0x810c0) 8=true := by
    rw [rootPtr]
    decide
  have valid8 : accessValid (rooted.getMem 0x810c0+8) 8=true := by
    rw [rootPtr]
    decide
  obtain ⟨final,postTrace,postPc,post0,post8,postLayer,postHeight,
    postCurrent,postIndex⟩ :=
    GroupedBalancedSignUpperPostGroup67.run hash rooted 0x83000 index 4
      groupPc valid0 valid8 rootPtr (Or.inr rfl) groupHeight groupIndex
  have groupF8 : rooted.getMem 0x810f8=BitVec.ofNat 64 witnessBase := by
    rw [groupFrame 0x810f8
      (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl rfl)))))]
    exact initial.witness
  have postSp := GroupedBalancedSignUpperPostStack67.post_group_sp hash
    rooted final index 4 groupPc valid0 valid8 (Or.inr rfl) groupHeight
    groupIndex postTrace
  have postTree : final.getMem 0x81000=rooted.getMem 0x81000 :=
    GroupedBalancedSignUpperPostFrame67.run_frame hash rooted final index 4
      groupPc valid0 valid8 (Or.inr rfl) groupHeight groupIndex postTrace
      0x81000 (by simp [GroupedBalancedSignUpperPostFrame67.Outside])
  refine ⟨n,c,final,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,
    nBound,cBound⟩
  · have combined := groupTrace.trans postTrace
    have exactLayer : rooted.getMem (528472#64)=
        start.getMem (528472#64) := groupLayer
    simpa [cost,exactLayer,Nat.add_assoc] using combined
  · simpa only [groupLayer] using postPc
  · intro j w
    have expectedUpper : wotsBase+16*67≤0x80000 := by omega
    have before :=
      GroupedBalancedSignUpperSelectedSlotSchedule67.slot_before_merkle
        wotsBase j w expectedUpper
    change (slot wotsBase j w).toNat<wotsBase+1072 at before
    have low : (slot wotsBase j w).toNat<0x80000 := by omega
    rw [GroupedBalancedSignUpperSelectedPostFrame67.before hash rooted
      final index 4 groupPc valid0 valid8 (Or.inr rfl) groupHeight
      groupIndex postTrace (slot wotsBase j w) low]
    exact groupWitness j w
  · intro a before
    have low : a.toNat<0x80000 := by omega
    rw [GroupedBalancedSignUpperSelectedPostFrame67.before hash rooted
      final index 4 groupPc valid0 valid8 (Or.inr rfl) groupHeight
      groupIndex postTrace a low]
    exact groupPrior a before
  · intro level levelBound i
    have low : (BitVec.ofNat 64 (witnessBase+16*level+8*i.val)).toNat<
        0x80000 := by
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega :
        witnessBase+16*level+8*i.val<2^64)]
      omega
    rw [GroupedBalancedSignUpperSelectedPostFrame67.before hash rooted
      final index 4 groupPc valid0 valid8 (Or.inr rfl) groupHeight
      groupIndex postTrace _ low]
    exact groupSiblings level levelBound i
  · intro w
    fin_cases w
    · simpa using post0.trans (rootWords ⟨0,by decide⟩)
    · simpa using post8.trans (rootWords ⟨1,by decide⟩)
  · simpa only [groupLayer] using postLayer
  · simpa only [groupLayer] using postHeight
  · simpa only [groupF8] using postCurrent
  · exact postIndex
  · exact postSp.trans groupSp
  · intro a low
    have post := GroupedBalancedSignUpperPostFrame67.run_frame hash rooted
      final index 4 groupPc valid0 valid8 (Or.inr rfl) groupHeight
      groupIndex postTrace a (outside_far a (Or.inl low))
    exact post.trans (groupFrame a (Or.inl low))
  · exact postTree.trans treeWord
  · intro a high
    have post := GroupedBalancedSignUpperPostFrame67.run_frame hash rooted
      final index 4 groupPc valid0 valid8 (Or.inr rfl) groupHeight
      groupIndex postTrace a (outside_far a (Or.inr high))
    exact post.trans (groupFrame a (Or.inr (Or.inr high)))

#print axioms height3
#print axioms height4
end
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedGroupComplete67
