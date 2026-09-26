import SigGolfCandidate.Hypertree.GroupedBalancedKeygenOneLevel67
/-! All fifteen direct67 keygen H4 parent hashes. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenTreeFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedKeygenImage67.image

theorem reset_ready (hash : Hash) (s : MachineState) (k src dst ell : Nat)
    (pc : s.pc = 0x1470)
    (count : s.getMem 0x81070#64 = BitVec.ofNat 64 k)
    (source : s.getMem 0x81078#64 = BitVec.ofNat 64 src)
    (destination : s.getMem 0x81080#64 = BitVec.ofNat 64 dst)
    (treeLevel : s.getMem 0x81050#64 = BitVec.ofNat 64 ell) :
    ∃ ready, Trace hash image s 4 4 0 0 ready ∧ ready.pc = 0x1480 ∧
      ready.getMem 0x81040#64 = 0 ∧
      ready.getMem 0x81070#64 = BitVec.ofNat 64 k ∧
      ready.getMem 0x81078#64 = BitVec.ofNat 64 src ∧
      ready.getMem 0x81080#64 = BitVec.ofNat 64 dst ∧
      ready.getMem 0x81050#64 = BitVec.ofNat 64 ell := by
  let ready := GroupedBalancedKeygenReset67.resetState s
  refine ⟨ready,(GroupedBalancedKeygenReset67.reset_steps s pc).trace,
    GroupedBalancedKeygenReset67.reset_pc s pc,
    GroupedBalancedKeygenReset67.reset_counter s,?_,?_,?_,?_⟩
  · rw [GroupedBalancedKeygenReset67.reset_other s 0x81070#64 (by decide),count]
  · rw [GroupedBalancedKeygenReset67.reset_other s 0x81078#64 (by decide),source]
  · rw [GroupedBalancedKeygenReset67.reset_other s 0x81080#64 (by decide),destination]
  · rw [GroupedBalancedKeygenReset67.reset_other s 0x81050#64 (by decide),treeLevel]

theorem tree_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x1428) :
    ∃ final, Trace hash image s 1359 1464 15 15 final ∧
      final.pc = 0x1648 ∧ final.getMem 0x81078#64 = 0x82000 ∧
      final.getMem 0x81050#64 = 4 := by
  let s0 := GroupedBalancedKeygenTreeSetup67.setupState s
  have t0 : Trace hash image s 22 22 0 0 s0 :=
    (GroupedBalancedKeygenTreeSetup67.setup_steps s pc).trace
  obtain ⟨c0,src0,dst0,ell0,idx0,_⟩ :=
    GroupedBalancedKeygenSetupControls67.setup_controls s
  obtain ⟨s1,t1,pc1,c1,src1,dst1,ell1,_⟩ :=
    GroupedBalancedKeygenOneLevel67.one_level hash s0 8 0x82000 0x82100 0
      (GroupedBalancedKeygenSetupControls67.setup_pc s pc)
      (by decide) (by decide) (Or.inl rfl) (Or.inr rfl)
      idx0 (by simpa using c0) (by simpa using src0)
      (by simpa using dst0) (by simpa using ell0)
  have pc1' : s1.pc = 0x1470 := by simpa using pc1
  have c1' : s1.getMem 0x81070#64 = 4 := by simpa using c1
  obtain ⟨r1,u1,rpc1,ri1,rc1,rs1,rd1,re1⟩ :=
    reset_ready hash s1 4 0x82100 0x82000 1 pc1'
      (by simpa using c1') (by simpa using src1)
      (by simpa using dst1) (by simpa using ell1)
  obtain ⟨s2,t2,pc2,c2,src2,dst2,ell2,_⟩ :=
    GroupedBalancedKeygenOneLevel67.one_level hash r1 4 0x82100 0x82000 1
      rpc1 (by decide) (by decide) (Or.inr rfl) (Or.inl rfl)
      ri1 rc1 rs1 rd1 re1
  have pc2' : s2.pc = 0x1470 := by simpa using pc2
  have c2' : s2.getMem 0x81070#64 = 2 := by simpa using c2
  obtain ⟨r2,u2,rpc2,ri2,rc2,rs2,rd2,re2⟩ :=
    reset_ready hash s2 2 0x82000 0x82100 2 pc2'
      (by simpa using c2') (by simpa using src2)
      (by simpa using dst2) (by simpa using ell2)
  obtain ⟨s3,t3,pc3,c3,src3,dst3,ell3,_⟩ :=
    GroupedBalancedKeygenOneLevel67.one_level hash r2 2 0x82000 0x82100 2
      rpc2 (by decide) (by decide) (Or.inl rfl) (Or.inr rfl)
      ri2 rc2 rs2 rd2 re2
  have pc3' : s3.pc = 0x1470 := by simpa using pc3
  have c3' : s3.getMem 0x81070#64 = 1 := by simpa using c3
  obtain ⟨r3,u3,rpc3,ri3,rc3,rs3,rd3,re3⟩ :=
    reset_ready hash s3 1 0x82100 0x82000 3 pc3'
      (by simpa using c3') (by simpa using src3)
      (by simpa using dst3) (by simpa using ell3)
  obtain ⟨final,t4,pc4,_,src4,_,ell4,_⟩ :=
    GroupedBalancedKeygenOneLevel67.one_level hash r3 1 0x82100 0x82000 3
      rpc3 (by decide) (by decide) (Or.inr rfl) (Or.inl rfl)
      ri3 rc3 rs3 rd3 re3
  refine ⟨final,?_,by simpa using pc4,by simpa using src4,by simpa using ell4⟩
  simpa only [Nat.reduceMul,Nat.reduceAdd,Nat.add_zero] using
    (((((((t0.trans t1).trans u1).trans t2).trans u2).trans t3).trans u3).trans t4)

#print axioms reset_ready
#print axioms tree_trace
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenTreeFold67
