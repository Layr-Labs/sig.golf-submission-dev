import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafPersistent67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCalleeFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCalleeLow67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCalleeTreeWord67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCalleeTableFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperHandoff67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperPostGroup67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperPostFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperPostStack67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperFinish67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperGroupLeafTree67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperGroupComplete67. -/
section
/-! Compose all upper WOTS leaves with the final ByteSign Merkle callee. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperGroupLeafTree67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeParentData67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

theorem height3 (hash : Hash) (secretKey : SecretKey)
    (treeBase rootAddress witnessBase selected : Nat) (start : MachineState)
    (initial : GroupedBalancedSignUpperLeafFold67.Inv hash secretKey treeBase
      (rootAddress*2^3) 3 selected witnessBase 0 start)
    (startSp : start.getReg .x2=0xfff700)
    (handoff : GroupedBalancedSignUpperLeafPersistent67.Handoff hash secretKey
      treeBase (rootAddress*2^3) 3 selected witnessBase)
    (aligned : (rootAddress*2^3)%2^3=0)
    (bound : rootAddress*2^3+2^3≤2^160)
    (leafBound : rootAddress*2^3<2^192)
    (params : Params (rootAddress*2^3) 0 4 0x83000 0x88000
      ((rootAddress*2^3)/2))
    (selectedBound : selected<1024)
    (treeBound : treeBase+3<2^64)
    (witnessLower : 0x20060≤witnessBase)
    (witnessBound : witnessBase+16*3+16≤0x80000)
    (witnessAligned : witnessBase%8=0) :
    ∃ (n c : Nat) (returned : MachineState),
      Trace hash image start (n+957) (c+1006) 1991 2127 returned ∧
      returned.pc=0x1c34 ∧
      returned.getReg .x2=start.getReg .x2 ∧
      returned.getMem 0x810c0=0x88000 ∧
      (∀ i : Fin 2,
        returned.getMem (BitVec.ofNat 64 (0x88000+8*i.val))=
          (GroupedBalancedUpperTree67.root hash secretKey treeBase 3
            rootAddress).extractLsb' (64*i.val) 64) ∧
      (∀ a : Word, GroupedBalancedSignUpperLeafPersistent67.Persistent a →
        returned.getMem a=start.getMem a) ∧
      returned.getMem 0x81000=BitVec.ofNat 64 (treeBase+3) ∧
      n ≤ 600000 ∧ c ≤ 700000 := by
  obtain ⟨n,c,leaf,leafTrace,leafInv,leafFrame,leafSp,nBound,cBound⟩ :=
    GroupedBalancedSignUpperLeafPersistent67.run_all hash secretKey treeBase
      (rootAddress*2^3) 3 selected witnessBase start (Or.inl rfl)
      aligned bound initial handoff
  have leafPc : leaf.pc=0x1c30 := by
    simpa using leafInv.data.pc
  have leafSelected : (leaf.getMem 0x810e8).toNat<1024 := by
    rw [leafInv.data.chosen,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : selected<2^64)]
    exact selectedBound
  have leafCount : leaf.getMem 0x810d0=8 := by
    simpa using leafInv.data.limit
  have leafScratch : ∀ i : Fin 3,
      leaf.getMem (Signing.wordAddress 0x810a8 i.val)=
        (BitVec.ofNat 192 (rootAddress*2^3)).extractLsb'
          (64*i.val) 64 := leafInv.data.scratch
  have leavesReady : ∀ j, j<8 → ∀ i : Fin 2,
      leaf.getMem (BitVec.ofNat 64 (0x83000+16*j+8*i.val))=
        (GroupedBalancedUpperTree67.leafRoot hash secretKey treeBase
          (rootAddress*2^3+j)).extractLsb' (64*i.val) 64 := by
    intro j hj i
    simpa [GroupedBalancedSignBottomStackSlots67.slot] using
      leafInv.data.previous j (by simpa using hj) i
  obtain ⟨returned,calleeTrace,calleePc,calleeSp,rootPtr,rootWords⟩ :=
    GroupedBalancedSignUpperTreeByteCallee67.height3_root hash secretKey
      treeBase rootAddress witnessBase leaf leafPc leafInv.stack
      leafInv.data.tree leafInv.heightWord leafInv.witness leafSelected
      leafCount leafBound params leafScratch leavesReady treeBound
      witnessBound witnessAligned
  have frame : ∀ a : Word,
      GroupedBalancedSignUpperLeafPersistent67.Persistent a →
      returned.getMem a=start.getMem a := by
    intro a safe
    have calleeFrame : returned.getMem a=leaf.getMem a := by
      rcases safe with low | control | table
      · exact GroupedBalancedSignUpperTreeCalleeLow67.height3_low hash leaf
          returned treeBase witnessBase calleeTrace leafPc leafInv.stack
          leafInv.data.tree leafInv.heightWord leafInv.witness leafSelected
          leafCount treeBound witnessLower witnessBound witnessAligned a low
      · exact GroupedBalancedSignUpperTreeCalleeFrame67.height3_frame hash
          leaf returned treeBase witnessBase calleeTrace leafPc leafInv.stack
          leafInv.data.tree leafInv.heightWord leafInv.witness leafSelected
          leafCount treeBound witnessBound witnessAligned a control
      · exact GroupedBalancedSignUpperCalleeTableFrame67.height3 hash leaf
          returned treeBase witnessBase calleeTrace leafPc
          (leafSp.trans startSp) leafInv.data.tree leafInv.heightWord
          leafInv.witness leafSelected leafCount treeBound witnessBound
          witnessAligned a table
    exact calleeFrame.trans (leafFrame a safe)
  have treeWord := GroupedBalancedSignUpperCalleeTreeWord67.height3 hash leaf
    returned treeBase witnessBase calleeTrace leafPc leafInv.stack
    leafInv.data.tree leafInv.heightWord leafInv.witness leafSelected
    leafCount treeBound witnessBound witnessAligned
  refine ⟨n,c,returned,?_,calleePc,?_,rootPtr,rootWords,frame,treeWord,
    by norm_num at nBound ⊢; omega,
    by norm_num at cBound ⊢; omega⟩
  · have combined := leafTrace.trans calleeTrace
    simpa only [show 248*2^3+7=1991 by decide,
      show 265*2^3+7=2127 by decide] using combined
  · exact calleeSp.trans leafSp

#print axioms height3

theorem height4 (hash : Hash) (secretKey : SecretKey)
    (treeBase rootAddress witnessBase selected : Nat) (start : MachineState)
    (initial : GroupedBalancedSignUpperLeafFold67.Inv hash secretKey treeBase
      (rootAddress*2^4) 4 selected witnessBase 0 start)
    (startSp : start.getReg .x2=0xfff700)
    (handoff : GroupedBalancedSignUpperLeafPersistent67.Handoff hash secretKey
      treeBase (rootAddress*2^4) 4 selected witnessBase)
    (aligned : (rootAddress*2^4)%2^4=0)
    (bound : rootAddress*2^4+2^4≤2^160)
    (leafBound : rootAddress*2^4<2^192)
    (params : Params (rootAddress*2^4) 0 8 0x83000 0x88000
      ((rootAddress*2^4)/2))
    (selectedBound : selected<1024)
    (treeBound : treeBase+4<2^64)
    (witnessLower : 0x20060≤witnessBase)
    (witnessBound : witnessBase+16*4+16≤0x80000)
    (witnessAligned : witnessBase%8=0) :
    ∃ (n c : Nat) (returned : MachineState),
      Trace hash image start (n+1743) (c+1848) 3983 4255 returned ∧
      returned.pc=0x1c34 ∧
      returned.getReg .x2=start.getReg .x2 ∧
      returned.getMem 0x810c0=0x83000 ∧
      (∀ i : Fin 2,
        returned.getMem (BitVec.ofNat 64 (0x83000+8*i.val))=
          (GroupedBalancedUpperTree67.root hash secretKey treeBase 4
            rootAddress).extractLsb' (64*i.val) 64) ∧
      (∀ a : Word, GroupedBalancedSignUpperLeafPersistent67.Persistent a →
        returned.getMem a=start.getMem a) ∧
      returned.getMem 0x81000=BitVec.ofNat 64 (treeBase+4) ∧
      n ≤ 600000 ∧ c ≤ 700000 := by
  obtain ⟨n,c,leaf,leafTrace,leafInv,leafFrame,leafSp,nBound,cBound⟩ :=
    GroupedBalancedSignUpperLeafPersistent67.run_all hash secretKey treeBase
      (rootAddress*2^4) 4 selected witnessBase start (Or.inr rfl)
      aligned bound initial handoff
  have leafPc : leaf.pc=0x1c30 := by
    simpa using leafInv.data.pc
  have leafSelected : (leaf.getMem 0x810e8).toNat<1024 := by
    rw [leafInv.data.chosen,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : selected<2^64)]
    exact selectedBound
  have leafCount : leaf.getMem 0x810d0=16 := by
    simpa using leafInv.data.limit
  have leafScratch : ∀ i : Fin 3,
      leaf.getMem (Signing.wordAddress 0x810a8 i.val)=
        (BitVec.ofNat 192 (rootAddress*2^4)).extractLsb'
          (64*i.val) 64 := leafInv.data.scratch
  have leavesReady : ∀ j, j<16 → ∀ i : Fin 2,
      leaf.getMem (BitVec.ofNat 64 (0x83000+16*j+8*i.val))=
        (GroupedBalancedUpperTree67.leafRoot hash secretKey treeBase
          (rootAddress*2^4+j)).extractLsb' (64*i.val) 64 := by
    intro j hj i
    simpa [GroupedBalancedSignBottomStackSlots67.slot] using
      leafInv.data.previous j (by simpa using hj) i
  obtain ⟨returned,calleeTrace,calleePc,calleeSp,rootPtr,rootWords⟩ :=
    GroupedBalancedSignUpperTreeByteCallee67.height4_root hash secretKey
      treeBase rootAddress witnessBase leaf leafPc leafInv.stack
      leafInv.data.tree leafInv.heightWord leafInv.witness leafSelected
      leafCount leafBound params leafScratch leavesReady treeBound
      witnessBound witnessAligned
  have frame : ∀ a : Word,
      GroupedBalancedSignUpperLeafPersistent67.Persistent a →
      returned.getMem a=start.getMem a := by
    intro a safe
    have calleeFrame : returned.getMem a=leaf.getMem a := by
      rcases safe with low | control | table
      · exact GroupedBalancedSignUpperTreeCalleeLow67.height4_low hash leaf
          returned treeBase witnessBase calleeTrace leafPc leafInv.stack
          leafInv.data.tree leafInv.heightWord leafInv.witness leafSelected
          leafCount treeBound witnessLower witnessBound witnessAligned a low
      · exact GroupedBalancedSignUpperTreeCalleeFrame67.height4_frame hash
          leaf returned treeBase witnessBase calleeTrace leafPc leafInv.stack
          leafInv.data.tree leafInv.heightWord leafInv.witness leafSelected
          leafCount treeBound witnessBound witnessAligned a control
      · exact GroupedBalancedSignUpperCalleeTableFrame67.height4 hash leaf
          returned treeBase witnessBase calleeTrace leafPc
          (leafSp.trans startSp) leafInv.data.tree leafInv.heightWord
          leafInv.witness leafSelected leafCount treeBound witnessBound
          witnessAligned a table
    exact calleeFrame.trans (leafFrame a safe)
  have treeWord := GroupedBalancedSignUpperCalleeTreeWord67.height4 hash leaf
    returned treeBase witnessBase calleeTrace leafPc leafInv.stack
    leafInv.data.tree leafInv.heightWord leafInv.witness leafSelected
    leafCount treeBound witnessBound witnessAligned
  refine ⟨n,c,returned,?_,calleePc,calleeSp.trans leafSp,
    rootPtr,rootWords,frame,treeWord,
    by norm_num at nBound ⊢; omega,
    by norm_num at cBound ⊢; omega⟩
  have combined := leafTrace.trans calleeTrace
  simpa only [show 248*2^4+15=3983 by decide,
    show 265*2^4+15=4255 by decide] using combined

#print axioms height4
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperGroupLeafTree67

end

/-! One complete upper signing group, from the first leaf through its layer update. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperGroupComplete67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeParentData67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

def cost (s : MachineState) (height : Nat) : Nat :=
  24 + 36*height +
    (if s.getMem 0x81058 + 1 = (30 : Word) then 15 else 11)

theorem cost_h3_normal (s : MachineState)
    (h : s.getMem 0x81058 + 1 ≠ (30 : Word)) : cost s 3=143 := by
  change s.getMem (528472#64)+1#64 ≠ 30#64 at h
  simp [cost,h]

theorem cost_h3_switch (s : MachineState)
    (h : s.getMem 0x81058 + 1 = (30 : Word)) : cost s 3=147 := by
  change s.getMem (528472#64)+1#64 = 30#64 at h
  simp [cost,h]

theorem cost_h4_normal (s : MachineState)
    (h : s.getMem 0x81058 + 1 ≠ (30 : Word)) : cost s 4=179 := by
  change s.getMem (528472#64)+1#64 ≠ 30#64 at h
  simp [cost,h]

private theorem low_outside (a : Word) (low : a.toNat < 0x100) :
    GroupedBalancedSignUpperPostFrame67.Outside a := by
  have ne (b : Word) (hb : 0x100 ≤ b.toNat) : a ≠ b := by
    intro eq
    subst a
    omega
  exact ⟨ne 0x80500 (by decide),ne 0x80508 (by decide),
    ne 0x810f0 (by decide),ne 0x81100 (by decide),
    ne 0x81090 (by decide),ne 0x81098 (by decide),
    ne 0x810a0 (by decide),ne 0x81058 (by decide),
    ne 0x81060 (by decide)⟩

private theorem table_outside (a : Word) (table : 0xfff700≤a.toNat) :
    GroupedBalancedSignUpperPostFrame67.Outside a := by
  have ne (b : Word) (hb : b.toNat<0x90000) : a≠b := by
    intro eq
    subst a
    omega
  exact ⟨ne 0x80500 (by decide),ne 0x80508 (by decide),
    ne 0x810f0 (by decide),ne 0x81100 (by decide),
    ne 0x81090 (by decide),ne 0x81098 (by decide),
    ne 0x810a0 (by decide),ne 0x81058 (by decide),
    ne 0x81060 (by decide)⟩

theorem height3 (hash : Hash) (secretKey : SecretKey)
    (treeBase rootAddress witnessBase chosen : Nat)
    (index : BitVec 192) (start : MachineState)
    (initial : GroupedBalancedSignUpperLeafFold67.Inv hash secretKey treeBase
      (rootAddress*2^3) 3 chosen witnessBase 0 start)
    (startSp : start.getReg .x2=0xfff700)
    (selectedWords : ∀ w : Fin 3,
      start.getMem (Signing.wordAddress 0x81090 w.val) =
        index.extractLsb' (64*w.val) 64)
    (aligned : (rootAddress*2^3)%2^3=0)
    (bound : rootAddress*2^3+2^3≤2^160)
    (leafBound : rootAddress*2^3<2^192)
    (params : Params (rootAddress*2^3) 0 4 0x83000 0x88000
      ((rootAddress*2^3)/2))
    (chosenBound : chosen<1024)
    (treeBound : treeBase+3<2^64)
    (baseBound : treeBase<256)
    (witnessLower : 0x20060≤witnessBase)
    (witnessBound : witnessBase+16*3+16≤0x80000)
    (witnessAligned : witnessBase%8=0) :
    ∃ (n c : Nat) (final : MachineState),
      Trace hash image start (n+957+cost start 3) (c+1006+cost start 3)
        1991 2127 final ∧
      final.pc =
        (if start.getMem 0x81058 + 1 = (45 : Word) then 0x1d60 else 0x15e0) ∧
      (∀ w : Fin 2,
        final.getMem (BitVec.ofNat 64 (0x80500+8*w.val)) =
          (GroupedBalancedUpperTree67.root hash secretKey treeBase 3
            rootAddress).extractLsb' (64*w.val) 64) ∧
      final.getMem 0x81058=start.getMem 0x81058+1 ∧
      final.getMem 0x81060=
        (if start.getMem 0x81058+1=(30 : Word) then 4 else
          BitVec.ofNat 64 3) ∧
      final.getMem 0x810f0=BitVec.ofNat 64 witnessBase + (3#64 <<< 4) ∧
      (∀ w : Fin 3,
        final.getMem (Signing.wordAddress 0x81090 w.val)=
          (index >>> 3).extractLsb' (64*w.val) 64) ∧
      final.getReg .x2=start.getReg .x2 ∧
      (∀ a : Word, a.toNat<0x100 → final.getMem a=start.getMem a) ∧
      final.getMem 0x81000=BitVec.ofNat 64 (treeBase+3) ∧
      (∀ a : Word, 0xfff700≤a.toNat →
        final.getMem a=start.getMem a) ∧
      n ≤ 600000 ∧ c ≤ 700000 := by
  have handoff := GroupedBalancedSignUpperHandoff67.handoff hash secretKey
    treeBase (rootAddress*2^3) 3 chosen witnessBase (Or.inl rfl) baseBound
  obtain ⟨n,c,rooted,groupTrace,groupPc,groupSp,rootPtr,rootWords,
    groupFrame,treeWord,nBound,cBound⟩ :=
    GroupedBalancedSignUpperGroupLeafTree67.height3 hash secretKey
      treeBase rootAddress witnessBase chosen start initial startSp handoff
      aligned bound leafBound params chosenBound treeBound witnessLower
      witnessBound witnessAligned
  have groupHeight : rooted.getMem 0x81060=3 := by
    rw [groupFrame 0x81060 (Or.inr (Or.inl (Or.inr (Or.inl rfl))))]
    exact initial.heightWord
  have groupIndex : ∀ w : Fin 3,
      rooted.getMem (Signing.wordAddress 0x81090 w.val)=
        index.extractLsb' (64*w.val) 64 := by
    intro w
    rw [groupFrame _ (Or.inr (Or.inl (by
      fin_cases w <;>
        simp [GroupedBalancedSignUpperTreeControlFrame67.Safe,
          Signing.wordAddress])))]
    exact selectedWords w
  have groupLayer : rooted.getMem 0x81058=start.getMem 0x81058 :=
    groupFrame 0x81058 (Or.inr (Or.inl (Or.inl rfl)))
  have groupF8 : rooted.getMem 0x810f8=BitVec.ofNat 64 witnessBase := by
    rw [groupFrame 0x810f8
      (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl rfl)))))]
    exact initial.witness
  have valid0 : accessValid (rooted.getMem 0x810c0) 8=true := by
    rw [rootPtr]
    decide
  have valid8 : accessValid (rooted.getMem 0x810c0+8) 8=true := by
    rw [rootPtr]
    decide
  obtain ⟨final,postTrace,postPc,post0,post8,postLayer,
    postHeight,postCurrent,postIndex⟩ :=
    GroupedBalancedSignUpperPostGroup67.run hash rooted 0x88000 index 3
      groupPc valid0 valid8 rootPtr (Or.inl rfl) groupHeight groupIndex
  have postSp := GroupedBalancedSignUpperPostStack67.post_group_sp hash
    rooted final index 3 groupPc valid0 valid8 (Or.inl rfl) groupHeight
    groupIndex postTrace
  have postLow : ∀ a : Word, a.toNat<0x100 →
      final.getMem a=rooted.getMem a := by
    intro a low
    exact GroupedBalancedSignUpperPostFrame67.run_frame hash rooted final
      index 3 groupPc valid0 valid8 (Or.inl rfl) groupHeight groupIndex
      postTrace a (low_outside a low)
  have postTable : ∀ a : Word, 0xfff700≤a.toNat →
      final.getMem a=rooted.getMem a := by
    intro a table
    exact GroupedBalancedSignUpperPostFrame67.run_frame hash rooted final
      index 3 groupPc valid0 valid8 (Or.inl rfl) groupHeight groupIndex
      postTrace a (table_outside a table)
  have postTree : final.getMem 0x81000=rooted.getMem 0x81000 :=
    GroupedBalancedSignUpperPostFrame67.run_frame hash rooted final
      index 3 groupPc valid0 valid8 (Or.inl rfl) groupHeight groupIndex
      postTrace 0x81000 (by simp [GroupedBalancedSignUpperPostFrame67.Outside])
  refine ⟨n,c,final,?_,?_,?_,?_,?_,?_,postIndex,
    postSp.trans groupSp,?_,postTree.trans treeWord,?_,nBound,cBound⟩
  · have all := groupTrace.trans postTrace
    simpa only [cost,groupLayer,Nat.add_assoc] using all
  · simpa only [groupLayer] using postPc
  · intro w
    fin_cases w
    · simpa using post0.trans (rootWords ⟨0,by decide⟩)
    · simpa using post8.trans (rootWords ⟨1,by decide⟩)
  · simpa only [groupLayer] using postLayer
  · simpa only [groupLayer] using postHeight
  · simpa only [groupF8] using postCurrent
  · intro a low
    exact (postLow a low).trans (groupFrame a (Or.inl low))
  · intro a table
    exact (postTable a table).trans
      (groupFrame a (Or.inr (Or.inr table)))

theorem height4 (hash : Hash) (secretKey : SecretKey)
    (treeBase rootAddress witnessBase chosen : Nat)
    (index : BitVec 192) (start : MachineState)
    (initial : GroupedBalancedSignUpperLeafFold67.Inv hash secretKey treeBase
      (rootAddress*2^4) 4 chosen witnessBase 0 start)
    (startSp : start.getReg .x2=0xfff700)
    (selectedWords : ∀ w : Fin 3,
      start.getMem (Signing.wordAddress 0x81090 w.val) =
        index.extractLsb' (64*w.val) 64)
    (aligned : (rootAddress*2^4)%2^4=0)
    (bound : rootAddress*2^4+2^4≤2^160)
    (leafBound : rootAddress*2^4<2^192)
    (params : Params (rootAddress*2^4) 0 8 0x83000 0x88000
      ((rootAddress*2^4)/2))
    (chosenBound : chosen<1024)
    (treeBound : treeBase+4<2^64)
    (baseBound : treeBase<256)
    (witnessLower : 0x20060≤witnessBase)
    (witnessBound : witnessBase+16*4+16≤0x80000)
    (witnessAligned : witnessBase%8=0) :
    ∃ (n c : Nat) (final : MachineState),
      Trace hash image start (n+1743+cost start 4) (c+1848+cost start 4)
        3983 4255 final ∧
      final.pc =
        (if start.getMem 0x81058 + 1 = (45 : Word) then 0x1d60 else 0x15e0) ∧
      (∀ w : Fin 2,
        final.getMem (BitVec.ofNat 64 (0x80500+8*w.val)) =
          (GroupedBalancedUpperTree67.root hash secretKey treeBase 4
            rootAddress).extractLsb' (64*w.val) 64) ∧
      final.getMem 0x81058=start.getMem 0x81058+1 ∧
      final.getMem 0x81060=
        (if start.getMem 0x81058+1=(30 : Word) then 4 else
          BitVec.ofNat 64 4) ∧
      final.getMem 0x810f0=BitVec.ofNat 64 witnessBase + (4#64 <<< 4) ∧
      (∀ w : Fin 3,
        final.getMem (Signing.wordAddress 0x81090 w.val)=
          (index >>> 4).extractLsb' (64*w.val) 64) ∧
      final.getReg .x2=start.getReg .x2 ∧
      (∀ a : Word, a.toNat<0x100 → final.getMem a=start.getMem a) ∧
      final.getMem 0x81000=BitVec.ofNat 64 (treeBase+4) ∧
      (∀ a : Word, 0xfff700≤a.toNat →
        final.getMem a=start.getMem a) ∧
      n ≤ 600000 ∧ c ≤ 700000 := by
  have handoff := GroupedBalancedSignUpperHandoff67.handoff hash secretKey
    treeBase (rootAddress*2^4) 4 chosen witnessBase (Or.inr rfl) baseBound
  obtain ⟨n,c,rooted,groupTrace,groupPc,groupSp,rootPtr,rootWords,
    groupFrame,treeWord,nBound,cBound⟩ :=
    GroupedBalancedSignUpperGroupLeafTree67.height4 hash secretKey
      treeBase rootAddress witnessBase chosen start initial startSp handoff
      aligned bound leafBound params chosenBound treeBound witnessLower
      witnessBound witnessAligned
  have groupHeight : rooted.getMem 0x81060=4 := by
    rw [groupFrame 0x81060 (Or.inr (Or.inl (Or.inr (Or.inl rfl))))]
    exact initial.heightWord
  have groupIndex : ∀ w : Fin 3,
      rooted.getMem (Signing.wordAddress 0x81090 w.val)=
        index.extractLsb' (64*w.val) 64 := by
    intro w
    rw [groupFrame _ (Or.inr (Or.inl (by
      fin_cases w <;>
        simp [GroupedBalancedSignUpperTreeControlFrame67.Safe,
          Signing.wordAddress])))]
    exact selectedWords w
  have groupLayer : rooted.getMem 0x81058=start.getMem 0x81058 :=
    groupFrame 0x81058 (Or.inr (Or.inl (Or.inl rfl)))
  have groupF8 : rooted.getMem 0x810f8=BitVec.ofNat 64 witnessBase := by
    rw [groupFrame 0x810f8
      (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl rfl)))))]
    exact initial.witness
  have valid0 : accessValid (rooted.getMem 0x810c0) 8=true := by
    rw [rootPtr]
    decide
  have valid8 : accessValid (rooted.getMem 0x810c0+8) 8=true := by
    rw [rootPtr]
    decide
  obtain ⟨final,postTrace,postPc,post0,post8,postLayer,
    postHeight,postCurrent,postIndex⟩ :=
    GroupedBalancedSignUpperPostGroup67.run hash rooted 0x83000 index 4
      groupPc valid0 valid8 rootPtr (Or.inr rfl) groupHeight groupIndex
  have postSp := GroupedBalancedSignUpperPostStack67.post_group_sp hash
    rooted final index 4 groupPc valid0 valid8 (Or.inr rfl) groupHeight
    groupIndex postTrace
  have postLow : ∀ a : Word, a.toNat<0x100 →
      final.getMem a=rooted.getMem a := by
    intro a low
    exact GroupedBalancedSignUpperPostFrame67.run_frame hash rooted final
      index 4 groupPc valid0 valid8 (Or.inr rfl) groupHeight groupIndex
      postTrace a (low_outside a low)
  have postTable : ∀ a : Word, 0xfff700≤a.toNat →
      final.getMem a=rooted.getMem a := by
    intro a table
    exact GroupedBalancedSignUpperPostFrame67.run_frame hash rooted final
      index 4 groupPc valid0 valid8 (Or.inr rfl) groupHeight groupIndex
      postTrace a (table_outside a table)
  have postTree : final.getMem 0x81000=rooted.getMem 0x81000 :=
    GroupedBalancedSignUpperPostFrame67.run_frame hash rooted final
      index 4 groupPc valid0 valid8 (Or.inr rfl) groupHeight groupIndex
      postTrace 0x81000 (by simp [GroupedBalancedSignUpperPostFrame67.Outside])
  refine ⟨n,c,final,?_,?_,?_,?_,?_,?_,postIndex,
    postSp.trans groupSp,?_,postTree.trans treeWord,?_,nBound,cBound⟩
  · have all := groupTrace.trans postTrace
    simpa only [cost,groupLayer,Nat.add_assoc] using all
  · simpa only [groupLayer] using postPc
  · intro w
    fin_cases w
    · simpa using post0.trans (rootWords ⟨0,by decide⟩)
    · simpa using post8.trans (rootWords ⟨1,by decide⟩)
  · simpa only [groupLayer] using postLayer
  · simpa only [groupLayer] using postHeight
  · simpa only [groupF8] using postCurrent
  · intro a low
    exact (postLow a low).trans (groupFrame a (Or.inl low))
  · intro a table
    exact (postTable a table).trans
      (groupFrame a (Or.inr (Or.inr table)))


theorem height4_success (hash : Hash) (secretKey : SecretKey)
    (treeBase rootAddress witnessBase chosen : Nat)
    (index : BitVec 192) (start : MachineState)
    (initial : GroupedBalancedSignUpperLeafFold67.Inv hash secretKey treeBase
      (rootAddress*2^4) 4 chosen witnessBase 0 start)
    (startSp : start.getReg .x2=0xfff700)
    (selectedWords : ∀ w : Fin 3,
      start.getMem (Signing.wordAddress 0x81090 w.val) =
        index.extractLsb' (64*w.val) 64)
    (aligned : (rootAddress*2^4)%2^4=0)
    (bound : rootAddress*2^4+2^4≤2^160)
    (leafBound : rootAddress*2^4<2^192)
    (params : Params (rootAddress*2^4) 0 8 0x83000 0x88000
      ((rootAddress*2^4)/2))
    (chosenBound : chosen<1024)
    (treeBound : treeBase+4<2^64)
    (baseBound : treeBase<256)
    (witnessLower : 0x20060≤witnessBase)
    (witnessBound : witnessBase+16*4+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (last : start.getMem 0x81058=44) :
    ∃ (n c : Nat) (final : MachineState),
      Executes hash image start (n+1925)
        ⟨.success,final,c+2030,3983,4255⟩ := by
  obtain ⟨n,c,post,path,postPc,_,_,_,_,_,_,_,_,_,_,_⟩ :=
    height4 hash secretKey treeBase rootAddress witnessBase chosen index
      start initial startSp selectedWords aligned bound leafBound params chosenBound
      treeBound baseBound witnessLower witnessBound witnessAligned
  have h45 : start.getMem 0x81058+1=(45 : Word) := by
    rw [last]
    decide
  have h30 : start.getMem 0x81058+1≠(30 : Word) := by
    rw [last]
    decide
  have pc : post.pc=0x1d60 := by
    rw [h45] at postPc
    simpa using postPc
  have suffix := GroupedBalancedSignUpperFinish67.finish_success hash post
    pc
  have whole := path.then_executes suffix
  refine ⟨n,c,GroupedBalancedSignUpperFinish67.successState post,?_⟩
  rw [cost_h4_normal start h30] at whole
  simpa [Execution.charge,Nat.add_assoc] using whole

#print axioms height3
#print axioms height4
#print axioms height4_success
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperGroupComplete67
