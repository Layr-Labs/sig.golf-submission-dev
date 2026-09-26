import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCalleeRoot67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperIndexedInitial67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperGroupComplete67


/-! Numeric initial parent-row parameters for upper heights three and four. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeParams67
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeParentData67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem height3 (rootAddress : Nat) (bounded : rootAddress*2^3<2^160) :
    Params (rootAddress*2^3) 0 4 0x83000 0x88000
      ((rootAddress*2^3)/2) := by
  refine ⟨⟨by decide,by decide⟩,Or.inr (Or.inr (Or.inl rfl)),?_,rfl,?_,
    Or.inl ⟨rfl,rfl⟩⟩
  · norm_num at bounded ⊢
    omega
  · norm_num at bounded ⊢
    omega

theorem height4 (rootAddress : Nat) (bounded : rootAddress*2^4<2^160) :
    Params (rootAddress*2^4) 0 8 0x83000 0x88000
      ((rootAddress*2^4)/2) := by
  refine ⟨⟨by decide,by decide⟩,Or.inr (Or.inr (Or.inr rfl)),?_,rfl,?_,
    Or.inl ⟨rfl,rfl⟩⟩
  · norm_num at bounded ⊢
    omega
  · norm_num at bounded ⊢
    omega

#print axioms height3
#print axioms height4
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeParams67


/-! One upper signing group from the layer boundary to the next boundary. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperIndexedStep67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperIndexedInitial67
open GroupedBalancedSignUpperBaseToInitial67
open GroupedBalancedSignUpperGroupComplete67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

theorem height3 (hash : Hash) (secretKey : SecretKey)
    (treeBase witnessBase : Nat) (index : BitVec 192)
    (s : MachineState) (message : BitVec 128)
    (pc : s.pc=0x15e0) (height : s.getMem 0x81060=3)
    (stack : s.getReg .x2=0xfff700)
    (currentWords : CurrentWords s message)
    (tables : GroupedBalancedVerifyByteContract67.Tables s)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (current : ∃ b : Nat,
      s.getMem 0x810f0=BitVec.ofNat 64 b ∧ witnessBase=b+1072 ∧
      0x20060≤b ∧ b+16*67≤0x80000 ∧ b%8=0)
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
      n ≤ 600000 ∧ c ≤ 700000 := by
  have hmsg := current_message_bytes s message currentWords
  obtain ⟨entry,entryTrace,initial,boundary,entrySp,entryTable,_,_,_⟩ :=
    GroupedBalancedSignUpperIndexedInitial67.h3 hash secretKey treeBase
      witnessBase index s message pc height stack hmsg tables tree current
      keyWords indexWords
  have selectedWords := boundary_index s entry index boundary indexWords
  have groupBounds := GroupedBalancedSignUpperIndexMask67.h3_group_bounds
    index indexBound
  have leafBound : index.toNat/8*8<2^160 := by omega
  have params := GroupedBalancedSignUpperTreeParams67.height3
    (index.toNat/8) leafBound
  have witnessLower : 0x20060≤witnessBase := by
    obtain ⟨b,_,beq,blow,_,_⟩ := current
    omega
  have witnessAligned : witnessBase%8=0 := by
    obtain ⟨b,_,beq,_,_,balign⟩ := current
    omega
  obtain ⟨n,c,final,groupTrace,groupPc,groupWords,groupLayer,
    groupHeight,groupWitness,groupIndex,groupSp,groupLow,groupTree,
    groupTable,nBound,cBound⟩ :=
    GroupedBalancedSignUpperGroupComplete67.height3 hash secretKey
      treeBase (index.toNat/8) witnessBase (index.toNat%8) index entry
      initial (entrySp.trans stack) selectedWords groupBounds.1
      groupBounds.2.1 (by omega) params (by omega) (by omega)
      treeBaseBound witnessLower witnessBound witnessAligned
  rcases boundary with ⟨layerFrame,_,_,_,_,_,entryLow⟩
  have costEq : cost entry 3=cost s 3 := by
    unfold cost
    rw [layerFrame]
  refine ⟨n,c,final,?_,?_,groupWords,?_,?_,groupWitness,groupIndex,
    groupSp.trans entrySp,?_,groupTree,?_,nBound,cBound⟩
  · have full := (OrdinarySteps.trace (hash := hash) entryTrace).trans groupTrace
    simpa only [costEq,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using full
  · simpa only [layerFrame] using groupPc
  · simpa only [layerFrame] using groupLayer
  · simpa only [layerFrame] using groupHeight
  · intro a ha
    exact (groupLow a ha).trans (entryLow a ha)
  · intro a ha
    exact (groupTable a ha).trans (entryTable a ha)


theorem height4 (hash : Hash) (secretKey : SecretKey)
    (treeBase witnessBase : Nat) (index : BitVec 192)
    (s : MachineState) (message : BitVec 128)
    (pc : s.pc=0x15e0) (height : s.getMem 0x81060=4)
    (stack : s.getReg .x2=0xfff700)
    (currentWords : CurrentWords s message)
    (tables : GroupedBalancedVerifyByteContract67.Tables s)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (current : ∃ b : Nat,
      s.getMem 0x810f0=BitVec.ofNat 64 b ∧ witnessBase=b+1072 ∧
      0x20060≤b ∧ b+16*67≤0x80000 ∧ b%8=0)
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
      n ≤ 600000 ∧ c ≤ 700000 := by
  have hmsg := current_message_bytes s message currentWords
  obtain ⟨entry,entryTrace,initial,boundary,entrySp,entryTable,_,_,_⟩ :=
    GroupedBalancedSignUpperIndexedInitial67.h4 hash secretKey treeBase
      witnessBase index s message pc height stack hmsg tables tree current
      keyWords indexWords
  have selectedWords := boundary_index s entry index boundary indexWords
  have groupBounds := GroupedBalancedSignUpperIndexMask67.h4_group_bounds
    index indexBound
  have leafBound : index.toNat/16*16<2^160 := by omega
  have params := GroupedBalancedSignUpperTreeParams67.height4
    (index.toNat/16) leafBound
  have witnessLower : 0x20060≤witnessBase := by
    obtain ⟨b,_,beq,blow,_,_⟩ := current
    omega
  have witnessAligned : witnessBase%8=0 := by
    obtain ⟨b,_,beq,_,_,balign⟩ := current
    omega
  obtain ⟨n,c,final,groupTrace,groupPc,groupWords,groupLayer,
    groupHeight,groupWitness,groupIndex,groupSp,groupLow,groupTree,
    groupTable,nBound,cBound⟩ :=
    GroupedBalancedSignUpperGroupComplete67.height4 hash secretKey
      treeBase (index.toNat/16) witnessBase (index.toNat%16) index entry
      initial (entrySp.trans stack) selectedWords groupBounds.1
      groupBounds.2.1 (by omega) params (by omega) (by omega)
      treeBaseBound witnessLower witnessBound witnessAligned
  rcases boundary with ⟨layerFrame,_,_,_,_,_,entryLow⟩
  have costEq : cost entry 4=cost s 4 := by
    unfold cost
    rw [layerFrame]
  refine ⟨n,c,final,?_,?_,groupWords,?_,?_,groupWitness,groupIndex,
    groupSp.trans entrySp,?_,groupTree,?_,nBound,cBound⟩
  · have full := (OrdinarySteps.trace (hash := hash) entryTrace).trans groupTrace
    simpa only [costEq,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using full
  · simpa only [layerFrame] using groupPc
  · simpa only [layerFrame] using groupLayer
  · simpa only [layerFrame] using groupHeight
  · intro a ha
    exact (groupLow a ha).trans (entryLow a ha)
  · intro a ha
    exact (groupTable a ha).trans (entryTable a ha)

#print axioms height4
#print axioms height3
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperIndexedStep67
