import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedOuterStep67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperFinish67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedOuterFold67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedOuterComplete67. -/
section
/-! The upper signer preserves all earlier signature words across a suffix. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedOuterFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperSchedule67
open GroupedBalancedSignUpperOuterInvariant67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

def callsFrom (k m : Nat) : Nat :=
  ∑ j ∈ Finset.range m, calls (k+j)

def blocksFrom (k m : Nat) : Nat :=
  ∑ j ∈ Finset.range m, blocks (k+j)

theorem current_mono (k m : Nat) :
    currentWitness k≤currentWitness (k+m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.add_succ,witness_next]
      unfold GroupedBalancedSignUpperSchedule67.witnessBase
      omega

theorem run_from (hash : Hash) (secretKey : SecretKey)
    (initialIndex : BitVec 192) (initialBound : initialIndex.toNat<2^150)
    (k m : Nat) (hk : k+m≤44)
    (message : BitVec 128) (start : MachineState)
    (initial : Boundary hash secretKey initialIndex k message start) :
    ∃ (n c : Nat) (currentMessage : BitVec 128) (final : MachineState),
      Trace hash image start n c (callsFrom k m) (blocksFrom k m) final ∧
      Boundary hash secretKey initialIndex (k+m) currentMessage final ∧
      (∀ a : Word, a.toNat<currentWitness k →
        final.getMem a=start.getMem a) ∧
      n ≤ 603000*m ∧ c ≤ 703000*m := by
  induction m with
  | zero =>
      refine ⟨0,0,message,start,?_,by simpa using initial,?_,by omega,
        by omega⟩
      · simpa [callsFrom,blocksFrom] using
          (Trace.refl (hash := hash) (image := image) start)
      · intro a _; rfl
  | succ m ih =>
      have hk44 : k+m<44 := by omega
      obtain ⟨n,c,currentMessage,middle,path,boundary,oldFrame,nBound,
        cBound⟩ := ih (by omega)
      obtain ⟨sn,sc,final,step,next,snBound,scBound,_,_,prior⟩ :=
        GroupedBalancedSignUpperSelectedOuterStep67.one_step hash secretKey
          initialIndex initialBound (k+m) hk44 currentMessage middle boundary
      refine ⟨n+sn,c+sc,_,final,?_,by simpa [Nat.add_assoc] using next,
        ?_,?_,?_⟩
      · have full := path.trans step
        simpa [callsFrom,blocksFrom,Finset.sum_range_succ,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using full
      · intro a ha
        have hmono := current_mono k m
        exact (prior a (by omega)).trans (oldFrame a ha)
      · simp only [Nat.mul_succ]
        omega
      · simp only [Nat.mul_succ]
        omega

theorem run_forty_four (hash : Hash) (secretKey : SecretKey)
    (initialIndex : BitVec 192) (initialBound : initialIndex.toNat<2^150)
    (message : BitVec 128) (start : MachineState)
    (initial : Boundary hash secretKey initialIndex 0 message start) :
    ∃ (n c : Nat) (currentMessage : BitVec 128) (final : MachineState),
      Trace hash image start n c 115492 123380 final ∧
      Boundary hash secretKey initialIndex 44 currentMessage final ∧
      (∀ a : Word, a.toNat<currentWitness 0 →
        final.getMem a=start.getMem a) ∧
      n ≤ 26532000 ∧ c ≤ 30932000 := by
  obtain ⟨n,c,currentMessage,final,path,boundary,frame,nBound,cBound⟩ :=
    run_from hash secretKey initialIndex initialBound 0 44 (by decide)
      message start initial
  have hc : callsFrom 0 44=115492 := by decide
  have hb : blocksFrom 0 44=123380 := by decide
  exact ⟨n,c,currentMessage,final,by simpa [hc,hb] using path,
    by simpa using boundary,frame,by omega,by omega⟩

#print axioms run_from
#print axioms run_forty_four
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedOuterFold67

end

/-! All upper groups terminate with their earlier wire words intact. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedOuterComplete67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperSchedule67
open GroupedBalancedSignUpperOuterInvariant67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev slot := GroupedBalancedSignUpperH2WitnessFrame67.slot

theorem finish_mem (s : MachineState) (a : Word) :
    (GroupedBalancedSignUpperFinish67.successState s).getMem a=s.getMem a := by
  simp [GroupedBalancedSignUpperFinish67.successState,execInstrBr]

theorem final_group (hash : Hash) (secretKey : SecretKey)
    (initialIndex : BitVec 192) (initialBound : initialIndex.toNat<2^150)
    (message : BitVec 128) (s : MachineState)
    (before : Boundary hash secretKey initialIndex 44 message s) :
    ∃ (n c : Nat) (final : MachineState),
      Executes hash image s n ⟨.success,final,c,3983,4255⟩ ∧
      n ≤ 603003 ∧ c ≤ 703003 ∧
      (∀ j : GroupedBalancedUpperTree67.ChainMixed, ∀ w : Fin 2,
        final.getMem (slot (currentWitness 44) j w)=
          (GroupedBalancedUpperTree67.signValues hash secretKey
            (treeBase 44) (indexAt initialIndex 44).toNat message j).extractLsb'
              (64*w.val) 64) ∧
      (∀ level, level<4 → ∀ i : Fin 2,
        final.getMem (BitVec.ofNat 64
          (witnessBase 44+16*level+8*i.val))=
          (GroupedBalancedSignUpperTreeModel67.nodeAt hash (treeBase 44)
            ((indexAt initialIndex 44).toNat/16*16)
            (fun x => GroupedBalancedUpperTree67.leafRoot hash secretKey
              (treeBase 44)
              ((indexAt initialIndex 44).toNat/16*16+x)) level
            (Nat.xor (((indexAt initialIndex 44).toNat%16)/2^level)
              1)).extractLsb' (64*i.val) 64) ∧
      (∀ a : Word, a.toNat<currentWitness 44 →
        final.getMem a=s.getMem a) := by
  have entryBound : GroupedBalancedSignUpperBaseToInitial67.entryCost
      message ≤ 292 := by
    unfold GroupedBalancedSignUpperBaseToInitial67.entryCost
    split_ifs <;> omega
  have costBound : GroupedBalancedSignUpperSelectedGroupComplete67.cost
      s 4 ≤ 183 := by
    unfold GroupedBalancedSignUpperSelectedGroupComplete67.cost
    split_ifs <;> omega
  have hheight : s.getMem 0x81060=4 := by
    simpa [height] using before.heightWord
  obtain ⟨n,c,post,path,postPc,_,_,_,_,_,_,_,_,_,nBound,cBound,
    chosenWords,siblingWords,prior⟩ :=
    GroupedBalancedSignUpperSelectedIndexedStep67.height4 hash secretKey
      (treeBase 44) (witnessBase 44) (currentWitness 44)
      (indexAt initialIndex 44) s message before.pc hheight before.stack
      before.currentWords before.tables before.treeWord before.witnessWord
      rfl (witness_current_lower 44)
      (witness_current_upper 44 (by decide))
      (witness_current_aligned 44) before.keyWords before.selectedWords
      (index_bound initialIndex initialBound 44)
      (base_bound 44 (by decide))
      (by simpa [height] using witness_base_bound 44 (by decide))
  have hlast : s.getMem 0x81058+1=(45 : Word) := by
    rw [before.layer]
    decide
  have pc : post.pc=0x1d60 := by
    rw [hlast] at postPc
    simpa using postPc
  have suffix := GroupedBalancedSignUpperFinish67.finish_success hash post
    pc
  have whole := path.then_executes suffix
  refine ⟨(60+GroupedBalancedSignUpperBaseToInitial67.entryCost message)+
      (n+1743+GroupedBalancedSignUpperSelectedGroupComplete67.cost s 4)+3,
    (60+GroupedBalancedSignUpperBaseToInitial67.entryCost message)+
      (c+1848+GroupedBalancedSignUpperSelectedGroupComplete67.cost s 4)+3,
    GroupedBalancedSignUpperFinish67.successState post,?_,by omega,
    by omega,?_,?_,?_⟩
  · simpa [Execution.charge,Nat.add_assoc] using whole
  · intro j w
    rw [finish_mem]
    exact chosenWords j w
  · intro level hlevel i
    rw [finish_mem]
    exact siblingWords level hlevel i
  · intro a ha
    rw [finish_mem]
    exact prior a ha

theorem all_groups (hash : Hash) (secretKey : SecretKey)
    (initialIndex : BitVec 192) (initialBound : initialIndex.toNat<2^150)
    (message : BitVec 128) (start : MachineState)
    (initial : Boundary hash secretKey initialIndex 0 message start) :
    ∃ (n c : Nat) (final : MachineState),
      Executes hash image start n ⟨.success,final,c,119475,127635⟩ ∧
      n ≤ 27135003 ∧ c ≤ 31635003 ∧
      (∀ a : Word, a.toNat<currentWitness 0 →
        final.getMem a=start.getMem a) := by
  obtain ⟨n,c,currentMessage,middle,path,boundary,frame,nBound,cBound⟩ :=
    GroupedBalancedSignUpperSelectedOuterFold67.run_forty_four hash
      secretKey initialIndex initialBound message start initial
  obtain ⟨sn,sc,final,last,snBound,scBound,_,_,prior⟩ :=
    final_group hash secretKey initialIndex initialBound currentMessage middle
      boundary
  have whole := path.then_executes last
  refine ⟨n+sn,c+sc,final,?_,by omega,by omega,?_⟩
  · simpa [Execution.charge] using whole
  · intro a ha
    exact (prior a (by
      have monotone := GroupedBalancedSignUpperSelectedOuterFold67.current_mono
        0 44
      simpa using (show a.toNat<currentWitness (0+44) by omega))).trans
      (frame a ha)

#print axioms finish_mem
#print axioms final_group
#print axioms all_groups
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedOuterComplete67
