import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperOuterStep67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperFinish67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperOuterFold67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperOuterComplete67. -/
section
/-! Execute the first forty-four upper groups from a common boundary state. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperOuterFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperSchedule67
open GroupedBalancedSignUpperOuterInvariant67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

theorem run_prefix (hash : Hash) (secretKey : SecretKey)
    (initialIndex : BitVec 192) (initialBound : initialIndex.toNat<2^150)
    (message : BitVec 128) (start : MachineState)
    (initial : Boundary hash secretKey initialIndex 0 message start)
    (k : Nat) (hk : k≤44) :
    ∃ (n c : Nat) (currentMessage : BitVec 128) (final : MachineState),
      Trace hash image start n c
        (∑ j ∈ Finset.range k, calls j)
        (∑ j ∈ Finset.range k, blocks j) final ∧
      Boundary hash secretKey initialIndex k currentMessage final ∧
      n ≤ 603000*k ∧ c ≤ 703000*k := by
  induction k with
  | zero =>
      exact ⟨0,0,message,start,
        by simpa using (Trace.refl (hash := hash) (image := image) start),
        initial,by omega,by omega⟩
  | succ k ih =>
      have hk44 : k<44 := by omega
      obtain ⟨n,c,currentMessage,middle,path,boundary,nBound,cBound⟩ := ih (by omega)
      obtain ⟨n',c',final,step,next,nStepBound,cStepBound⟩ :=
        GroupedBalancedSignUpperOuterStep67.one_step hash secretKey
          initialIndex initialBound k hk44 currentMessage middle boundary
      refine ⟨n+n',c+c',_,final,?_,next,?_,?_⟩
      · simpa only [Finset.sum_range_succ] using path.trans step
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
      n ≤ 26532000 ∧ c ≤ 30932000 := by
  obtain ⟨n,c,currentMessage,final,path,boundary,nBound,cBound⟩ :=
    run_prefix hash secretKey initialIndex initialBound message start initial 44
      (by decide)
  have hc : (∑ j ∈ Finset.range 44, calls j)=115492 := by decide
  have hb : (∑ j ∈ Finset.range 44, blocks j)=123380 := by decide
  exact ⟨n,c,currentMessage,final,by simpa [hc,hb] using path,boundary,
    by omega,by omega⟩

#print axioms run_prefix
#print axioms run_forty_four
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperOuterFold67

end

/-! Compose all upper groups and the public-key comparison. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperOuterComplete67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperSchedule67
open GroupedBalancedSignUpperOuterInvariant67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

theorem final_group (hash : Hash) (secretKey : SecretKey)
    (initialIndex : BitVec 192) (initialBound : initialIndex.toNat<2^150)
    (message : BitVec 128) (s : MachineState)
    (before : Boundary hash secretKey initialIndex 44 message s) :
    ∃ (n c : Nat) (final : MachineState),
      Executes hash image s n ⟨.success,final,c,3983,4255⟩ ∧
      n ≤ 603003 ∧ c ≤ 703003 := by
  have entryBound : GroupedBalancedSignUpperBaseToInitial67.entryCost message ≤ 292 := by
    unfold GroupedBalancedSignUpperBaseToInitial67.entryCost
    split_ifs <;> omega
  have costBound : GroupedBalancedSignUpperGroupComplete67.cost s 4 ≤ 183 := by
    unfold GroupedBalancedSignUpperGroupComplete67.cost
    split_ifs <;> omega
  have hheight : s.getMem 0x81060=4 := by
    simpa [height] using before.heightWord
  have current : ∃ b : Nat,
      s.getMem 0x810f0=BitVec.ofNat 64 b ∧
      witnessBase 44=b+1072 ∧ 0x20060≤b ∧
      b+16*67≤0x80000 ∧ b%8=0 :=
    ⟨currentWitness 44,before.witnessWord,rfl,
      witness_current_lower 44,witness_current_upper 44 (by decide),
      witness_current_aligned 44⟩
  obtain ⟨n,c,post,path,postPc,_,_,_,_,_,_,_,_,_,nBound,cBound⟩ :=
    GroupedBalancedSignUpperIndexedStep67.height4 hash secretKey
      (treeBase 44) (witnessBase 44) (indexAt initialIndex 44)
      s message before.pc hheight before.stack before.currentWords
      before.tables before.treeWord current before.keyWords
      before.selectedWords (index_bound initialIndex initialBound 44)
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
      (n+1743+GroupedBalancedSignUpperGroupComplete67.cost s 4)+3,
    (60+GroupedBalancedSignUpperBaseToInitial67.entryCost message)+
      (c+1848+GroupedBalancedSignUpperGroupComplete67.cost s 4)+3,
    GroupedBalancedSignUpperFinish67.successState post,?_,by omega,by omega⟩
  simpa [Execution.charge,Nat.add_assoc] using whole

theorem all_groups (hash : Hash) (secretKey : SecretKey)
    (initialIndex : BitVec 192) (initialBound : initialIndex.toNat<2^150)
    (message : BitVec 128) (start : MachineState)
    (initial : Boundary hash secretKey initialIndex 0 message start) :
    ∃ (n c : Nat) (final : MachineState),
      Executes hash image start n ⟨.success,final,c,119475,127635⟩ ∧
      n ≤ 27135003 ∧ c ≤ 31635003 := by
  obtain ⟨n,c,currentMessage,middle,path,boundary,nBound,cBound⟩ :=
    GroupedBalancedSignUpperOuterFold67.run_forty_four hash secretKey
      initialIndex initialBound message start initial
  obtain ⟨n',c',final,last,nLastBound,cLastBound⟩ :=
    final_group hash secretKey initialIndex initialBound currentMessage middle
      boundary
  have whole := path.then_executes last
  exact ⟨n+n',c+c',final,
    by simpa [Execution.charge] using whole,by omega,by omega⟩

#print axioms final_group
#print axioms all_groups
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperOuterComplete67
