import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedGroupLeaves67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeCalleeFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeByteCallee67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCalleeFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingCallee67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCalleeLow67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCalleeTreeWord67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCalleeTableFrame67


/-! Numeric location of each WOTS word relative to the following Merkle
authentication words in the signing buffer. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedSlotSchedule67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree

private abbrev slot := GroupedBalancedSignUpperH2WitnessFrame67.slot

theorem slot_before_merkle (b : Nat)
    (j : GroupedBalancedUpperTree67.ChainMixed) (w : Fin 2)
    (upper : b+16*67≤0x80000) :
    (slot b j w).toNat < b+1072 := by
  rw [GroupedBalancedSignUpperH2WitnessFrame67.slot_nat b j w
    (by have := j.isLt; omega)]
  have := j.isLt
  have := w.isLt
  omega

theorem base_unique (expected b : Nat)
    (word : BitVec.ofNat 64 expected=BitVec.ofNat 64 b)
    (expectedUpper : expected+16*67≤0x80000)
    (bUpper : b+16*67≤0x80000) : b=expected := by
  have hn := congrArg BitVec.toNat word
  simp only [BitVec.toNat_ofNat] at hn
  have currentSmall : expected<2^64 := by omega
  have bSmall : b<2^64 := by omega
  rw [Nat.mod_eq_of_lt currentSmall,Nat.mod_eq_of_lt bSmall] at hn
  omega

#print axioms slot_before_merkle
#print axioms base_unique
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedSlotSchedule67


/-! The selected WOTS witness survives the Merkle tree callee after the
complete upper-group leaf loop. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedGroupTree67
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
    ∃ (n c : Nat) (returned : MachineState),
      Trace hash image start (n+957) (c+1006) 1991 2127 returned ∧
      returned.pc=0x1c34 ∧
      returned.getMem 0x810c0=0x88000 ∧
      returned.getMem 0x81060=3 ∧
      returned.getMem 0x81058=start.getMem 0x81058 ∧
      (∀ w : Fin 3,
        returned.getMem (Signing.wordAddress 0x81090 w.val)=
          index.extractLsb' (64*w.val) 64) ∧
      (∀ j : GroupedBalancedUpperTree67.ChainMixed, ∀ w : Fin 2,
        returned.getMem (slot wotsBase j w)=
          (GroupedBalancedUpperTree67.signValues hash secretKey treeBase
            (rootAddress*2^3+selected) message j).extractLsb'
              (64*w.val) 64) ∧
      (∀ a : Word, a.toNat<wotsBase →
        returned.getMem a=start.getMem a) ∧
      (∀ level, level<3 → ∀ i : Fin 2,
        returned.getMem (BitVec.ofNat 64
          (witnessBase+16*level+8*i.val))=
          (GroupedBalancedSignUpperTreeModel67.nodeAt hash treeBase
            (rootAddress*2^3)
            (fun k => GroupedBalancedUpperTree67.leafRoot hash secretKey
              treeBase (rootAddress*2^3+k)) level
            (Nat.xor (selected/2^level) 1)).extractLsb'
              (64*i.val) 64) ∧
      returned.getReg .x2=start.getReg .x2 ∧
      (∀ i : Fin 2,
        returned.getMem (BitVec.ofNat 64 (0x88000+8*i.val))=
          (GroupedBalancedUpperTree67.root hash secretKey treeBase 3
            rootAddress).extractLsb' (64*i.val) 64) ∧
      (∀ a : Word, GroupedBalancedSignUpperLeafPersistent67.Persistent a →
        returned.getMem a=start.getMem a) ∧
      returned.getMem 0x81000=BitVec.ofNat 64 (treeBase+3) ∧
      n ≤ 600000 ∧ c ≤ 700000 := by
  obtain ⟨b,n,c,leaf,bWord,bLower,bUpper,bAlign,leafTrace,leafInv,
    leafWords,leafPersistent,leafPrior,leafSp,nBound,cBound⟩ :=
    GroupedBalancedSignUpperSelectedGroupLeaves67.all_leaves_witness hash
      secretKey treeBase (rootAddress*2^3) 3 selected witnessBase message
      start (Or.inl rfl) baseBound aligned bound chosenBound initial digits
  have expectedUpper : wotsBase+16*67≤0x80000 := by
    omega
  have baseEq : b=wotsBase :=
    GroupedBalancedSignUpperSelectedSlotSchedule67.base_unique wotsBase b
      (current.symm.trans bWord) expectedUpper bUpper
  have leafPc : leaf.pc=0x1c30 := by
    simpa using leafInv.data.pc
  have leafSelected : (leaf.getMem 0x810e8).toNat<1024 := by
    rw [leafInv.data.chosen,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : selected<2^64)]
    omega
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
  have control (a : Word)
      (safe : GroupedBalancedSignUpperTreeControlFrame67.Safe a) :
      returned.getMem a=start.getMem a :=
    (GroupedBalancedSignUpperTreeCalleeFrame67.height3_frame hash leaf
      returned treeBase witnessBase calleeTrace leafPc leafInv.stack
      leafInv.data.tree leafInv.heightWord leafInv.witness leafSelected
      leafCount treeBound witnessBound witnessAligned a safe).trans
      (leafPersistent a (Or.inr (Or.inl safe)))
  have siblings :=
    GroupedBalancedSignUpperSelectedTreeSiblingCallee67.height3 hash
      treeBase (rootAddress*2^3) witnessBase selected
      (fun k => GroupedBalancedUpperTree67.leafRoot hash secretKey treeBase
        (rootAddress*2^3+k)) leaf returned calleeTrace leafPc
      leafInv.stack leafInv.data.tree leafInv.heightWord leafInv.witness
      leafInv.data.chosen chosenBound leafCount leafBound params leafScratch
      leavesReady treeBound witnessBound witnessAligned
  have frame : ∀ a : Word,
      GroupedBalancedSignUpperLeafPersistent67.Persistent a →
      returned.getMem a=start.getMem a := by
    intro a safe
    have calleeFrame : returned.getMem a=leaf.getMem a := by
      rcases safe with low | controlSafe | table
      · exact GroupedBalancedSignUpperTreeCalleeLow67.height3_low hash leaf
          returned treeBase witnessBase calleeTrace leafPc leafInv.stack
          leafInv.data.tree leafInv.heightWord leafInv.witness leafSelected
          leafCount treeBound (by omega : 0x20060≤witnessBase)
          witnessBound witnessAligned a low
      · exact GroupedBalancedSignUpperTreeCalleeFrame67.height3_frame hash
          leaf returned treeBase witnessBase calleeTrace leafPc
          leafInv.stack leafInv.data.tree leafInv.heightWord
          leafInv.witness leafSelected leafCount treeBound witnessBound
          witnessAligned a controlSafe
      · exact GroupedBalancedSignUpperCalleeTableFrame67.height3 hash leaf
          returned treeBase witnessBase calleeTrace leafPc
          (leafSp.trans startSp) leafInv.data.tree leafInv.heightWord
          leafInv.witness leafSelected leafCount treeBound witnessBound
          witnessAligned a table
    exact calleeFrame.trans (leafPersistent a safe)
  have treeWord := GroupedBalancedSignUpperCalleeTreeWord67.height3 hash leaf
    returned treeBase witnessBase calleeTrace leafPc leafInv.stack
    leafInv.data.tree leafInv.heightWord leafInv.witness leafSelected
    leafCount treeBound witnessBound witnessAligned
  refine ⟨n,c,returned,?_,calleePc,rootPtr,?_,?_,?_,?_,?_,?_,
    calleeSp.trans leafSp,rootWords,frame,treeWord,by omega,by omega⟩
  · have combined := leafTrace.trans calleeTrace
    simpa only [show 248*2^3+7=1991 by decide,
      show 265*2^3+7=2127 by decide] using combined
  · rw [control 0x81060 (Or.inr (Or.inl rfl))]
    exact initial.heightWord
  · exact control 0x81058 (Or.inl rfl)
  · intro w
    rw [control _ (by fin_cases w <;>
      simp [GroupedBalancedSignUpperTreeControlFrame67.Safe,
        Signing.wordAddress])]
    exact selectedWords w
  · intro j w
    have before : (slot b j w).toNat<witnessBase := by
      rw [witnessNext,←baseEq]
      exact GroupedBalancedSignUpperSelectedSlotSchedule67.slot_before_merkle
        b j w bUpper
    have frame :=
      GroupedBalancedSignUpperSelectedTreeCalleeFrame67.height3_before
        hash leaf returned treeBase witnessBase calleeTrace leafPc
        leafInv.stack leafInv.data.tree leafInv.heightWord leafInv.witness
        leafSelected leafCount treeBound witnessBound witnessAligned
        (slot b j w) before
    rw [←baseEq]
    exact frame.trans (leafWords j w)
  · intro a beforeWots
    have beforeMerkle : a.toNat<witnessBase := by omega
    have frame :=
      GroupedBalancedSignUpperSelectedTreeCalleeFrame67.height3_before
        hash leaf returned treeBase witnessBase calleeTrace leafPc
        leafInv.stack leafInv.data.tree leafInv.heightWord leafInv.witness
        leafSelected leafCount treeBound witnessBound witnessAligned
        a beforeMerkle
    exact frame.trans (leafPrior a (by omega))
  · exact siblings

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
    ∃ (n c : Nat) (returned : MachineState),
      Trace hash image start (n+1743) (c+1848) 3983 4255 returned ∧
      returned.pc=0x1c34 ∧
      returned.getMem 0x810c0=0x83000 ∧
      returned.getMem 0x81060=4 ∧
      returned.getMem 0x81058=start.getMem 0x81058 ∧
      (∀ w : Fin 3,
        returned.getMem (Signing.wordAddress 0x81090 w.val)=
          index.extractLsb' (64*w.val) 64) ∧
      (∀ j : GroupedBalancedUpperTree67.ChainMixed, ∀ w : Fin 2,
        returned.getMem (slot wotsBase j w)=
          (GroupedBalancedUpperTree67.signValues hash secretKey treeBase
            (rootAddress*2^4+selected) message j).extractLsb'
              (64*w.val) 64) ∧
      (∀ a : Word, a.toNat<wotsBase →
        returned.getMem a=start.getMem a) ∧
      (∀ level, level<4 → ∀ i : Fin 2,
        returned.getMem (BitVec.ofNat 64
          (witnessBase+16*level+8*i.val))=
          (GroupedBalancedSignUpperTreeModel67.nodeAt hash treeBase
            (rootAddress*2^4)
            (fun k => GroupedBalancedUpperTree67.leafRoot hash secretKey
              treeBase (rootAddress*2^4+k)) level
            (Nat.xor (selected/2^level) 1)).extractLsb'
              (64*i.val) 64) ∧
      returned.getReg .x2=start.getReg .x2 ∧
      (∀ i : Fin 2,
        returned.getMem (BitVec.ofNat 64 (0x83000+8*i.val))=
          (GroupedBalancedUpperTree67.root hash secretKey treeBase 4
            rootAddress).extractLsb' (64*i.val) 64) ∧
      (∀ a : Word, GroupedBalancedSignUpperLeafPersistent67.Persistent a →
        returned.getMem a=start.getMem a) ∧
      returned.getMem 0x81000=BitVec.ofNat 64 (treeBase+4) ∧
      n ≤ 600000 ∧ c ≤ 700000 := by
  obtain ⟨b,n,c,leaf,bWord,bLower,bUpper,bAlign,leafTrace,leafInv,
    leafWords,leafPersistent,leafPrior,leafSp,nBound,cBound⟩ :=
    GroupedBalancedSignUpperSelectedGroupLeaves67.all_leaves_witness hash
      secretKey treeBase (rootAddress*2^4) 4 selected witnessBase message
      start (Or.inr rfl) baseBound aligned bound chosenBound initial digits
  have expectedUpper : wotsBase+16*67≤0x80000 := by
    omega
  have baseEq : b=wotsBase :=
    GroupedBalancedSignUpperSelectedSlotSchedule67.base_unique wotsBase b
      (current.symm.trans bWord) expectedUpper bUpper
  have leafPc : leaf.pc=0x1c30 := by
    simpa using leafInv.data.pc
  have leafSelected : (leaf.getMem 0x810e8).toNat<1024 := by
    rw [leafInv.data.chosen,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : selected<2^64)]
    omega
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
  have control (a : Word)
      (safe : GroupedBalancedSignUpperTreeControlFrame67.Safe a) :
      returned.getMem a=start.getMem a :=
    (GroupedBalancedSignUpperTreeCalleeFrame67.height4_frame hash leaf
      returned treeBase witnessBase calleeTrace leafPc leafInv.stack
      leafInv.data.tree leafInv.heightWord leafInv.witness leafSelected
      leafCount treeBound witnessBound witnessAligned a safe).trans
      (leafPersistent a (Or.inr (Or.inl safe)))
  have siblings :=
    GroupedBalancedSignUpperSelectedTreeSiblingCallee67.height4 hash
      treeBase (rootAddress*2^4) witnessBase selected
      (fun k => GroupedBalancedUpperTree67.leafRoot hash secretKey treeBase
        (rootAddress*2^4+k)) leaf returned calleeTrace leafPc
      leafInv.stack leafInv.data.tree leafInv.heightWord leafInv.witness
      leafInv.data.chosen chosenBound leafCount leafBound params leafScratch
      leavesReady treeBound witnessBound witnessAligned
  have frame : ∀ a : Word,
      GroupedBalancedSignUpperLeafPersistent67.Persistent a →
      returned.getMem a=start.getMem a := by
    intro a safe
    have calleeFrame : returned.getMem a=leaf.getMem a := by
      rcases safe with low | controlSafe | table
      · exact GroupedBalancedSignUpperTreeCalleeLow67.height4_low hash leaf
          returned treeBase witnessBase calleeTrace leafPc leafInv.stack
          leafInv.data.tree leafInv.heightWord leafInv.witness leafSelected
          leafCount treeBound (by omega : 0x20060≤witnessBase)
          witnessBound witnessAligned a low
      · exact GroupedBalancedSignUpperTreeCalleeFrame67.height4_frame hash
          leaf returned treeBase witnessBase calleeTrace leafPc
          leafInv.stack leafInv.data.tree leafInv.heightWord
          leafInv.witness leafSelected leafCount treeBound witnessBound
          witnessAligned a controlSafe
      · exact GroupedBalancedSignUpperCalleeTableFrame67.height4 hash leaf
          returned treeBase witnessBase calleeTrace leafPc
          (leafSp.trans startSp) leafInv.data.tree leafInv.heightWord
          leafInv.witness leafSelected leafCount treeBound witnessBound
          witnessAligned a table
    exact calleeFrame.trans (leafPersistent a safe)
  have treeWord := GroupedBalancedSignUpperCalleeTreeWord67.height4 hash leaf
    returned treeBase witnessBase calleeTrace leafPc leafInv.stack
    leafInv.data.tree leafInv.heightWord leafInv.witness leafSelected
    leafCount treeBound witnessBound witnessAligned
  refine ⟨n,c,returned,?_,calleePc,rootPtr,?_,?_,?_,?_,?_,?_,
    calleeSp.trans leafSp,rootWords,frame,treeWord,by omega,by omega⟩
  · have combined := leafTrace.trans calleeTrace
    simpa only [show 248*2^4+15=3983 by decide,
      show 265*2^4+15=4255 by decide] using combined
  · rw [control 0x81060 (Or.inr (Or.inl rfl))]
    exact initial.heightWord
  · exact control 0x81058 (Or.inl rfl)
  · intro w
    rw [control _ (by fin_cases w <;>
      simp [GroupedBalancedSignUpperTreeControlFrame67.Safe,
        Signing.wordAddress])]
    exact selectedWords w
  · intro j w
    have before : (slot b j w).toNat<witnessBase := by
      rw [witnessNext,←baseEq]
      exact GroupedBalancedSignUpperSelectedSlotSchedule67.slot_before_merkle
        b j w bUpper
    have frame :=
      GroupedBalancedSignUpperSelectedTreeCalleeFrame67.height4_before
        hash leaf returned treeBase witnessBase calleeTrace leafPc
        leafInv.stack leafInv.data.tree leafInv.heightWord leafInv.witness
        leafSelected leafCount treeBound witnessBound witnessAligned
        (slot b j w) before
    rw [←baseEq]
    exact frame.trans (leafWords j w)
  · intro a beforeWots
    have beforeMerkle : a.toNat<witnessBase := by omega
    have frame :=
      GroupedBalancedSignUpperSelectedTreeCalleeFrame67.height4_before
        hash leaf returned treeBase witnessBase calleeTrace leafPc
        leafInv.stack leafInv.data.tree leafInv.heightWord leafInv.witness
        leafSelected leafCount treeBound witnessBound witnessAligned
        a beforeMerkle
    exact frame.trans (leafPrior a (by omega))
  · exact siblings

#print axioms height3
#print axioms height4
end
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedGroupTree67
