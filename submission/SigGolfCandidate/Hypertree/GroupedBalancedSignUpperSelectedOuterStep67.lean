import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperIndexedStep67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedGroupComplete67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperOuterInvariant67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedIndexedStep67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedOuterStep67. -/
section
/-! One indexed upper group with its selected WOTS and Merkle witness. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedIndexedStep67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperIndexedInitial67
open GroupedBalancedSignUpperBaseToInitial67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev slot := GroupedBalancedSignUpperH2WitnessFrame67.slot
private abbrev cost := GroupedBalancedSignUpperSelectedGroupComplete67.cost

theorem height3 (hash : Hash) (secretKey : SecretKey)
    (treeBase witnessBase wotsBase : Nat) (index : BitVec 192)
    (s : MachineState) (message : BitVec 128)
    (pc : s.pc=0x15e0) (height : s.getMem 0x81060=3)
    (stack : s.getReg .x2=0xfff700)
    (currentWords : CurrentWords s message)
    (tables : GroupedBalancedVerifyByteContract67.Tables s)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (currentWord : s.getMem 0x810f0=BitVec.ofNat 64 wotsBase)
    (witnessNext : witnessBase=wotsBase+1072)
    (wotsLower : 0x20060≤wotsBase)
    (wotsUpper : wotsBase+16*67≤0x80000)
    (wotsAligned : wotsBase%8=0)
    (keyWords : ∀ j : Fin 4,
      s.getMem (Signing.wordAddress 0x20 j.val)=
        secretKey.extractLsb' (64*j.val) 64)
    (indexWords : ∀ w : Fin 3,
      s.getMem (Signing.wordAddress 0x81090 w.val)=
        index.extractLsb' (64*w.val) 64)
    (indexBound : index.toNat<2^160)
    (treeBaseBound : treeBase<256)
    (witnessBound : witnessBase+16*3+16≤0x80000) :
    ∃ (n c : Nat) (final : MachineState),
      Trace hash image s
        ((61+entryCost message)+(n+957+cost s 3))
        ((61+entryCost message)+(c+1006+cost s 3))
        1991 2127 final ∧
      final.pc=
        (if s.getMem 0x81058+1=(45 : Word) then 0x1d60 else 0x15e0) ∧
      (∀ w : Fin 2,
        final.getMem (BitVec.ofNat 64 (0x80500+8*w.val))=
          (GroupedBalancedUpperTree67.root hash secretKey treeBase 3
            (index.toNat/8)).extractLsb' (64*w.val) 64) ∧
      final.getMem 0x81058=s.getMem 0x81058+1 ∧
      final.getMem 0x81060=
        (if s.getMem 0x81058+1=(30 : Word) then 4 else
          BitVec.ofNat 64 3) ∧
      final.getMem 0x810f0=BitVec.ofNat 64 witnessBase+(3#64 <<< 4) ∧
      (∀ w : Fin 3,
        final.getMem (Signing.wordAddress 0x81090 w.val)=
          (index >>> 3).extractLsb' (64*w.val) 64) ∧
      final.getReg .x2=s.getReg .x2 ∧
      (∀ a : Word, a.toNat<0x100 → final.getMem a=s.getMem a) ∧
      final.getMem 0x81000=BitVec.ofNat 64 (treeBase+3) ∧
      (∀ a : Word, 0xfff700≤a.toNat → final.getMem a=s.getMem a) ∧
      n ≤ 600000 ∧ c ≤ 700000 ∧
      (∀ j : GroupedBalancedUpperTree67.ChainMixed, ∀ w : Fin 2,
        final.getMem (slot wotsBase j w)=
          (GroupedBalancedUpperTree67.signValues hash secretKey treeBase
            index.toNat message j).extractLsb' (64*w.val) 64) ∧
      (∀ level, level<3 → ∀ i : Fin 2,
        final.getMem (BitVec.ofNat 64 (witnessBase+16*level+8*i.val))=
          (GroupedBalancedSignUpperTreeModel67.nodeAt hash treeBase
            (index.toNat/8*8)
            (fun k => GroupedBalancedUpperTree67.leafRoot hash secretKey
              treeBase (index.toNat/8*8+k)) level
            (Nat.xor ((index.toNat%8)/2^level) 1)).extractLsb'
              (64*i.val) 64) ∧
      (∀ a : Word, a.toNat<wotsBase → final.getMem a=s.getMem a) := by
  have current : ∃ b : Nat,
      s.getMem 0x810f0=BitVec.ofNat 64 b ∧ witnessBase=b+1072 ∧
      0x20060≤b ∧ b+16*67≤0x80000 ∧ b%8=0 :=
    ⟨wotsBase,currentWord,witnessNext,wotsLower,wotsUpper,wotsAligned⟩
  have hmsg := current_message_bytes s message currentWords
  obtain ⟨entry,entryTrace,initial,boundary,entrySp,entryTable,
    entryDigits,entrySignature,entryCurrent⟩ :=
    GroupedBalancedSignUpperIndexedInitial67.h3 hash secretKey treeBase
      witnessBase index s message pc height stack hmsg tables tree current
      keyWords indexWords
  have selectedWords := boundary_index s entry index boundary indexWords
  have groupBounds := GroupedBalancedSignUpperIndexMask67.h3_group_bounds
    index indexBound
  have leafBound : index.toNat/8*8<2^160 := by omega
  have params := GroupedBalancedSignUpperTreeParams67.height3
    (index.toNat/8) leafBound
  have witnessAligned : witnessBase%8=0 := by omega
  obtain ⟨n,c,final,groupTrace,groupPc,groupWitness,groupPrior,
    groupSiblings,groupWords,groupLayer,groupHeight,groupCurrent,
    groupIndex,groupSp,groupLow,groupTree,groupTable,nBound,cBound⟩ :=
    GroupedBalancedSignUpperSelectedGroupComplete67.height3 hash secretKey
      treeBase (index.toNat/8) witnessBase (index.toNat%8) wotsBase
      message index entry initial (entrySp.trans stack)
      (by simpa [GroupedBalancedSignUpperH2WitnessFrame67.digitAddress]
        using entryDigits)
      (entryCurrent.trans currentWord) selectedWords witnessNext
      groupBounds.1 groupBounds.2.1 (by omega) params groupBounds.2.2
      (by omega) treeBaseBound witnessBound witnessAligned
  rcases boundary with ⟨layerFrame,_,_,_,_,_,entryLow⟩
  have costEq : cost entry 3=cost s 3 := by
    unfold cost GroupedBalancedSignUpperSelectedGroupComplete67.cost
    rw [layerFrame]
  have leafEq : index.toNat/8*2^3+index.toNat%8=index.toNat := by
    norm_num
    omega
  refine ⟨n,c,final,?_,?_,groupWords,?_,?_,groupCurrent,groupIndex,
    groupSp.trans entrySp,?_,groupTree,?_,nBound,cBound,?_,groupSiblings,?_⟩
  · have full := (OrdinarySteps.trace (hash := hash) entryTrace).trans
      groupTrace
    simpa only [costEq,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using full
  · simpa only [layerFrame] using groupPc
  · simpa only [layerFrame] using groupLayer
  · simpa only [layerFrame] using groupHeight
  · intro a ha
    exact (groupLow a ha).trans (entryLow a ha)
  · intro a ha
    exact (groupTable a ha).trans (entryTable a ha)
  · intro j w
    have h := groupWitness j w
    rw [leafEq] at h
    exact h
  · intro a ha
    exact (groupPrior a ha).trans
      (entrySignature a (by omega : a.toNat<0x80000))

theorem height4 (hash : Hash) (secretKey : SecretKey)
    (treeBase witnessBase wotsBase : Nat) (index : BitVec 192)
    (s : MachineState) (message : BitVec 128)
    (pc : s.pc=0x15e0) (height : s.getMem 0x81060=4)
    (stack : s.getReg .x2=0xfff700)
    (currentWords : CurrentWords s message)
    (tables : GroupedBalancedVerifyByteContract67.Tables s)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (currentWord : s.getMem 0x810f0=BitVec.ofNat 64 wotsBase)
    (witnessNext : witnessBase=wotsBase+1072)
    (wotsLower : 0x20060≤wotsBase)
    (wotsUpper : wotsBase+16*67≤0x80000)
    (wotsAligned : wotsBase%8=0)
    (keyWords : ∀ j : Fin 4,
      s.getMem (Signing.wordAddress 0x20 j.val)=
        secretKey.extractLsb' (64*j.val) 64)
    (indexWords : ∀ w : Fin 3,
      s.getMem (Signing.wordAddress 0x81090 w.val)=
        index.extractLsb' (64*w.val) 64)
    (indexBound : index.toNat<2^160)
    (treeBaseBound : treeBase<256)
    (witnessBound : witnessBase+16*4+16≤0x80000) :
    ∃ (n c : Nat) (final : MachineState),
      Trace hash image s
        ((60+entryCost message)+(n+1743+cost s 4))
        ((60+entryCost message)+(c+1848+cost s 4))
        3983 4255 final ∧
      final.pc=
        (if s.getMem 0x81058+1=(45 : Word) then 0x1d60 else 0x15e0) ∧
      (∀ w : Fin 2,
        final.getMem (BitVec.ofNat 64 (0x80500+8*w.val))=
          (GroupedBalancedUpperTree67.root hash secretKey treeBase 4
            (index.toNat/16)).extractLsb' (64*w.val) 64) ∧
      final.getMem 0x81058=s.getMem 0x81058+1 ∧
      final.getMem 0x81060=
        (if s.getMem 0x81058+1=(30 : Word) then 4 else
          BitVec.ofNat 64 4) ∧
      final.getMem 0x810f0=BitVec.ofNat 64 witnessBase+(4#64 <<< 4) ∧
      (∀ w : Fin 3,
        final.getMem (Signing.wordAddress 0x81090 w.val)=
          (index >>> 4).extractLsb' (64*w.val) 64) ∧
      final.getReg .x2=s.getReg .x2 ∧
      (∀ a : Word, a.toNat<0x100 → final.getMem a=s.getMem a) ∧
      final.getMem 0x81000=BitVec.ofNat 64 (treeBase+4) ∧
      (∀ a : Word, 0xfff700≤a.toNat → final.getMem a=s.getMem a) ∧
      n ≤ 600000 ∧ c ≤ 700000 ∧
      (∀ j : GroupedBalancedUpperTree67.ChainMixed, ∀ w : Fin 2,
        final.getMem (slot wotsBase j w)=
          (GroupedBalancedUpperTree67.signValues hash secretKey treeBase
            index.toNat message j).extractLsb' (64*w.val) 64) ∧
      (∀ level, level<4 → ∀ i : Fin 2,
        final.getMem (BitVec.ofNat 64 (witnessBase+16*level+8*i.val))=
          (GroupedBalancedSignUpperTreeModel67.nodeAt hash treeBase
            (index.toNat/16*16)
            (fun k => GroupedBalancedUpperTree67.leafRoot hash secretKey
              treeBase (index.toNat/16*16+k)) level
            (Nat.xor ((index.toNat%16)/2^level) 1)).extractLsb'
              (64*i.val) 64) ∧
      (∀ a : Word, a.toNat<wotsBase → final.getMem a=s.getMem a) := by
  have current : ∃ b : Nat,
      s.getMem 0x810f0=BitVec.ofNat 64 b ∧ witnessBase=b+1072 ∧
      0x20060≤b ∧ b+16*67≤0x80000 ∧ b%8=0 :=
    ⟨wotsBase,currentWord,witnessNext,wotsLower,wotsUpper,wotsAligned⟩
  have hmsg := current_message_bytes s message currentWords
  obtain ⟨entry,entryTrace,initial,boundary,entrySp,entryTable,
    entryDigits,entrySignature,entryCurrent⟩ :=
    GroupedBalancedSignUpperIndexedInitial67.h4 hash secretKey treeBase
      witnessBase index s message pc height stack hmsg tables tree current
      keyWords indexWords
  have selectedWords := boundary_index s entry index boundary indexWords
  have groupBounds := GroupedBalancedSignUpperIndexMask67.h4_group_bounds
    index indexBound
  have leafBound : index.toNat/16*16<2^160 := by omega
  have params := GroupedBalancedSignUpperTreeParams67.height4
    (index.toNat/16) leafBound
  have witnessAligned : witnessBase%8=0 := by omega
  obtain ⟨n,c,final,groupTrace,groupPc,groupWitness,groupPrior,
    groupSiblings,groupWords,groupLayer,groupHeight,groupCurrent,
    groupIndex,groupSp,groupLow,groupTree,groupTable,nBound,cBound⟩ :=
    GroupedBalancedSignUpperSelectedGroupComplete67.height4 hash secretKey
      treeBase (index.toNat/16) witnessBase (index.toNat%16) wotsBase
      message index entry initial (entrySp.trans stack)
      (by simpa [GroupedBalancedSignUpperH2WitnessFrame67.digitAddress]
        using entryDigits)
      (entryCurrent.trans currentWord) selectedWords witnessNext
      groupBounds.1 groupBounds.2.1 (by omega) params groupBounds.2.2
      (by omega) treeBaseBound witnessBound witnessAligned
  rcases boundary with ⟨layerFrame,_,_,_,_,_,entryLow⟩
  have costEq : cost entry 4=cost s 4 := by
    unfold cost GroupedBalancedSignUpperSelectedGroupComplete67.cost
    rw [layerFrame]
  have leafEq : index.toNat/16*2^4+index.toNat%16=index.toNat := by
    norm_num
    omega
  refine ⟨n,c,final,?_,?_,groupWords,?_,?_,groupCurrent,groupIndex,
    groupSp.trans entrySp,?_,groupTree,?_,nBound,cBound,?_,groupSiblings,?_⟩
  · have full := (OrdinarySteps.trace (hash := hash) entryTrace).trans
      groupTrace
    simpa only [costEq,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using full
  · simpa only [layerFrame] using groupPc
  · simpa only [layerFrame] using groupLayer
  · simpa only [layerFrame] using groupHeight
  · intro a ha
    exact (groupLow a ha).trans (entryLow a ha)
  · intro a ha
    exact (groupTable a ha).trans (entryTable a ha)
  · intro j w
    have h := groupWitness j w
    rw [leafEq] at h
    exact h
  · intro a ha
    exact (groupPrior a ha).trans
      (entrySignature a (by omega : a.toNat<0x80000))


#print axioms height4
#print axioms height3
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedIndexedStep67

end

/-! Advance one nonterminal upper group with exact selected witness words. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedOuterStep67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperSchedule67
open GroupedBalancedSignUpperOuterInvariant67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev slot := GroupedBalancedSignUpperH2WitnessFrame67.slot

theorem one_step (hash : Hash) (secretKey : SecretKey)
    (initialIndex : BitVec 192) (initialBound : initialIndex.toNat<2^150)
    (k : Nat) (hk : k<44) (message : BitVec 128) (s : MachineState)
    (before : Boundary hash secretKey initialIndex k message s) :
    ∃ (n c : Nat) (final : MachineState),
      Trace hash image s n c (calls k) (blocks k) final ∧
      Boundary hash secretKey initialIndex (k+1)
        (groupRoot hash secretKey initialIndex k) final ∧
      n ≤ 603000 ∧ c ≤ 703000 ∧
      (∀ j : GroupedBalancedUpperTree67.ChainMixed, ∀ w : Fin 2,
        final.getMem (slot (currentWitness k) j w)=
          (GroupedBalancedUpperTree67.signValues hash secretKey
            (treeBase k) (indexAt initialIndex k).toNat message j).extractLsb'
              (64*w.val) 64) ∧
      (∀ level, level<height k → ∀ i : Fin 2,
        final.getMem (BitVec.ofNat 64
          (witnessBase k+16*level+8*i.val))=
          (GroupedBalancedSignUpperTreeModel67.nodeAt hash (treeBase k)
            ((indexAt initialIndex k).toNat/2^height k*2^height k)
            (fun x => GroupedBalancedUpperTree67.leafRoot hash secretKey
              (treeBase k)
              ((indexAt initialIndex k).toNat/2^height k*2^height k+x))
            level
            (Nat.xor (((indexAt initialIndex k).toNat%2^height k)/2^level)
              1)).extractLsb' (64*i.val) 64) ∧
      (∀ a : Word, a.toNat<currentWitness k → final.getMem a=s.getMem a) := by
  have entryBound : GroupedBalancedSignUpperBaseToInitial67.entryCost
      message ≤ 292 := by
    unfold GroupedBalancedSignUpperBaseToInitial67.entryCost
    split_ifs <;> omega
  have hk45 : k<45 := by omega
  let index := indexAt initialIndex k
  have ibound : index.toNat<2^160 := index_bound initialIndex initialBound k
  have baseBound : treeBase k<256 := base_bound k hk45
  have lower := witness_current_lower k
  have upper := witness_current_upper k (by omega : k≤45)
  have aligned := witness_current_aligned k
  by_cases hk30 : k<30
  · have h3 : height k=3 := by simp [height,hk30]
    have hword : s.getMem 0x81060=3 := by
      simpa [h3] using before.heightWord
    have wbound : witnessBase k+16*3+16≤0x80000 := by
      simpa [h3] using witness_base_bound k hk45
    obtain ⟨n,c,final,path,pc,rootWords,layer,heightWord,witnessWord,
      selectedWords,stack,lowFrame,treeWord,tableFrame,nBound,cBound,
      chosenWords,siblingWords,priorFrame⟩ :=
      GroupedBalancedSignUpperSelectedIndexedStep67.height3 hash secretKey
        (treeBase k) (witnessBase k) (currentWitness k) index s message
        before.pc hword before.stack before.currentWords before.tables
        before.treeWord before.witnessWord rfl lower upper aligned
        before.keyWords before.selectedWords ibound baseBound wbound
    have root : ∀ w : Fin 2,
        final.getMem (BitVec.ofNat 64 (0x80500+8*w.val))=
          (groupRoot hash secretKey initialIndex k).extractLsb'
            (64*w.val) 64 := by
      intro w
      simpa [groupRoot,index,height,hk30] using rootWords w
    have next := boundary_next hash secretKey initialIndex k hk message s final
      before pc root layer (by simpa [h3] using heightWord)
      (by simpa [h3] using witnessWord)
      (by simpa [h3,index] using selectedWords) stack lowFrame
      (by simpa [h3] using treeWord) tableFrame
    have costBound : GroupedBalancedSignUpperSelectedGroupComplete67.cost
        s 3 ≤ 147 := by
      unfold GroupedBalancedSignUpperSelectedGroupComplete67.cost
      split_ifs <;> omega
    refine ⟨(61+GroupedBalancedSignUpperBaseToInitial67.entryCost message)+
        (n+957+GroupedBalancedSignUpperSelectedGroupComplete67.cost s 3),
      (61+GroupedBalancedSignUpperBaseToInitial67.entryCost message)+
        (c+1006+GroupedBalancedSignUpperSelectedGroupComplete67.cost s 3),
      final,?_,next,by omega,by omega,chosenWords,?_,priorFrame⟩
    · simpa [calls,blocks,hk30] using path
    · intro level hlevel i
      simpa only [h3,show (2:Nat)^3=8 by decide,index] using
        siblingWords level (by simpa [h3] using hlevel) i
  · have h4 : height k=4 := by simp [height,hk30]
    have hword : s.getMem 0x81060=4 := by
      simpa [h4] using before.heightWord
    have wbound : witnessBase k+16*4+16≤0x80000 := by
      simpa [h4] using witness_base_bound k hk45
    obtain ⟨n,c,final,path,pc,rootWords,layer,heightWord,witnessWord,
      selectedWords,stack,lowFrame,treeWord,tableFrame,nBound,cBound,
      chosenWords,siblingWords,priorFrame⟩ :=
      GroupedBalancedSignUpperSelectedIndexedStep67.height4 hash secretKey
        (treeBase k) (witnessBase k) (currentWitness k) index s message
        before.pc hword before.stack before.currentWords before.tables
        before.treeWord before.witnessWord rfl lower upper aligned
        before.keyWords before.selectedWords ibound baseBound wbound
    have root : ∀ w : Fin 2,
        final.getMem (BitVec.ofNat 64 (0x80500+8*w.val))=
          (groupRoot hash secretKey initialIndex k).extractLsb'
            (64*w.val) 64 := by
      intro w
      simpa [groupRoot,index,height,hk30] using rootWords w
    have next := boundary_next hash secretKey initialIndex k hk message s final
      before pc root layer (by simpa [h4] using heightWord)
      (by simpa [h4] using witnessWord)
      (by simpa [h4,index] using selectedWords) stack lowFrame
      (by simpa [h4] using treeWord) tableFrame
    have costBound : GroupedBalancedSignUpperSelectedGroupComplete67.cost
        s 4 ≤ 183 := by
      unfold GroupedBalancedSignUpperSelectedGroupComplete67.cost
      split_ifs <;> omega
    refine ⟨(60+GroupedBalancedSignUpperBaseToInitial67.entryCost message)+
        (n+1743+GroupedBalancedSignUpperSelectedGroupComplete67.cost s 4),
      (60+GroupedBalancedSignUpperBaseToInitial67.entryCost message)+
        (c+1848+GroupedBalancedSignUpperSelectedGroupComplete67.cost s 4),
      final,?_,next,by omega,by omega,chosenWords,?_,priorFrame⟩
    · simpa [calls,blocks,hk30] using path
    · intro level hlevel i
      simpa only [h4,show (2:Nat)^4=16 by decide,index] using
        siblingWords level (by simpa [h4] using hlevel) i

#print axioms one_step
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedOuterStep67
