import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperOuterInvariant67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperIndexedStep67

/-! Advance one nonterminal upper group while preserving the outer invariant. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperOuterStep67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperSchedule67
open GroupedBalancedSignUpperOuterInvariant67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

theorem one_step (hash : Hash) (secretKey : SecretKey)
    (initialIndex : BitVec 192) (initialBound : initialIndex.toNat<2^150)
    (k : Nat) (hk : k<44) (message : BitVec 128) (s : MachineState)
    (before : Boundary hash secretKey initialIndex k message s) :
    ∃ (n c : Nat) (final : MachineState),
      Trace hash image s n c (calls k) (blocks k) final ∧
      Boundary hash secretKey initialIndex (k+1)
        (groupRoot hash secretKey initialIndex k) final ∧
      n ≤ 603000 ∧ c ≤ 703000 := by
  have entryBound : GroupedBalancedSignUpperBaseToInitial67.entryCost message ≤ 292 := by
    unfold GroupedBalancedSignUpperBaseToInitial67.entryCost
    split_ifs <;> omega
  have hk45 : k<45 := by omega
  have current : ∃ b : Nat,
      s.getMem 0x810f0=BitVec.ofNat 64 b ∧
      witnessBase k=b+1072 ∧ 0x20060≤b ∧
      b+16*67≤0x80000 ∧ b%8=0 :=
    ⟨currentWitness k,before.witnessWord,rfl,
      witness_current_lower k,witness_current_upper k (by omega),
      witness_current_aligned k⟩
  let index := indexAt initialIndex k
  have ibound : index.toNat<2^160 := index_bound initialIndex initialBound k
  have baseBound : treeBase k<256 := base_bound k hk45
  by_cases hk30 : k<30
  · have h3 : height k=3 := by simp [height,hk30]
    have hword : s.getMem 0x81060=3 := by
      simpa [h3] using before.heightWord
    have wbound : witnessBase k+16*3+16≤0x80000 := by
      simpa [h3] using witness_base_bound k hk45
    obtain ⟨n,c,final,path,pc,rootWords,layer,heightWord,witnessWord,
      selectedWords,stack,lowFrame,treeWord,tableFrame,nBound,cBound⟩ :=
      GroupedBalancedSignUpperIndexedStep67.height3 hash secretKey
        (treeBase k) (witnessBase k) index s message before.pc hword
        before.stack before.currentWords before.tables before.treeWord
        current before.keyWords before.selectedWords ibound baseBound wbound
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
    have costBound : GroupedBalancedSignUpperGroupComplete67.cost s 3 ≤ 147 := by
      unfold GroupedBalancedSignUpperGroupComplete67.cost
      split_ifs <;> omega
    exact ⟨(61+GroupedBalancedSignUpperBaseToInitial67.entryCost message)+
        (n+957+GroupedBalancedSignUpperGroupComplete67.cost s 3),
      (61+GroupedBalancedSignUpperBaseToInitial67.entryCost message)+
        (c+1006+GroupedBalancedSignUpperGroupComplete67.cost s 3),
      final,by simpa [calls,blocks,hk30] using path,next,
      by omega,by omega⟩
  · have h4 : height k=4 := by simp [height,hk30]
    have hword : s.getMem 0x81060=4 := by
      simpa [h4] using before.heightWord
    have wbound : witnessBase k+16*4+16≤0x80000 := by
      simpa [h4] using witness_base_bound k hk45
    obtain ⟨n,c,final,path,pc,rootWords,layer,heightWord,witnessWord,
      selectedWords,stack,lowFrame,treeWord,tableFrame,nBound,cBound⟩ :=
      GroupedBalancedSignUpperIndexedStep67.height4 hash secretKey
        (treeBase k) (witnessBase k) index s message before.pc hword
        before.stack before.currentWords before.tables before.treeWord
        current before.keyWords before.selectedWords ibound baseBound wbound
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
    have costBound : GroupedBalancedSignUpperGroupComplete67.cost s 4 ≤ 183 := by
      unfold GroupedBalancedSignUpperGroupComplete67.cost
      split_ifs <;> omega
    exact ⟨(60+GroupedBalancedSignUpperBaseToInitial67.entryCost message)+
        (n+1743+GroupedBalancedSignUpperGroupComplete67.cost s 4),
      (60+GroupedBalancedSignUpperBaseToInitial67.entryCost message)+
        (c+1848+GroupedBalancedSignUpperGroupComplete67.cost s 4),
      final,by simpa [calls,blocks,hk30] using path,next,
      by omega,by omega⟩

#print axioms one_step
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperOuterStep67
