import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootCacheNode67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodesFold67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenOneLevel67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootLevel67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenTreeFold67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootTree67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootCacheFold67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootCacheTree67. -/
section
/-! Cache frame through every node of a direct67 H4 tree level. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootCacheFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenRootCacheNode67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

private theorem ne_high (a : Word) (low : a.toNat < 0x20060)
    (b : Nat) (lower : 0x80000 ≤ b) (upper : b < 2^64) :
    a ≠ BitVec.ofNat 64 b := by
  intro eq
  have h := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt upper] at h
  omega

theorem nodes_cache (hash : Hash) (s final : MachineState)
    (n rem src dst : Nat)
    (pc : s.pc = 0x1480) (positive : 0 < rem) (bound : n+rem ≤ 8)
    (srcCase : src = 0x82000 ∨ src = 0x82100)
    (dstCase : dst = 0x82000 ∨ dst = 0x82100)
    (index : s.getMem 0x81040#64 = BitVec.ofNat 64 n)
    (count : s.getMem 0x81070#64 = BitVec.ofNat 64 (n+rem))
    (source : s.getMem 0x81078#64 = BitVec.ofNat 64 src)
    (destination : s.getMem 0x81080#64 = BitVec.ofNat 64 dst)
    (trace : Trace hash image s (79*rem) (86*rem) rem rem final) :
    CacheFrame s final := by
  induction rem generalizing s n final with
  | zero => omega
  | succ t ih =>
      obtain ⟨mid,first,midPC,midIndex,midFrame⟩ :=
        GroupedBalancedKeygenOneNode67.one_node hash s n (n+t+1) src dst
          pc (by omega) (by omega) srcCase dstCase index
          (by simpa only [Nat.add_assoc] using count) source destination
      have firstCache := one_node_cache hash s mid n (n+t+1) src dst
        pc (by omega) (by omega) srcCase dstCase index
        (by simpa only [Nat.add_assoc] using count) source destination first
      by_cases last : t = 0
      · subst t
        have same : final = mid := Trace.deterministic trace
          (by simpa only [Nat.reduceMul,Nat.mul_one,Nat.reduceAdd] using first)
        rw [same]
        exact firstCache
      · have midPC' : mid.pc = 0x1480 := by
          simpa [last] using midPC
        have midCount : mid.getMem 0x81070#64 = BitVec.ofNat 64 ((n+1)+t) := by
          rw [midFrame 0x81070#64 (by decide) (by decide) (by decide) (by decide)]
          simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using count
        have midSrc : mid.getMem 0x81078#64 = BitVec.ofNat 64 src := by
          rw [midFrame 0x81078#64 (by decide) (by decide) (by decide) (by decide)]
          exact source
        have midDst : mid.getMem 0x81080#64 = BitVec.ofNat 64 dst := by
          rw [midFrame 0x81080#64 (by decide) (by decide) (by decide) (by decide)]
          exact destination
        obtain ⟨known,second,_,_,_⟩ :=
          GroupedBalancedKeygenNodesFold67.nodes hash mid (n+1) t src dst
            midPC' (by omega) (by omega) srcCase dstCase midIndex
            midCount midSrc midDst
        have full : Trace hash image s (79*(t+1)) (86*(t+1)) (t+1) (t+1) known := by
          simpa only [Nat.mul_succ,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
            using first.trans second
        have same : final = known := Trace.deterministic trace full
        rw [same]
        exact firstCache.trans (ih mid known (n+1) midPC' (by omega)
          (by omega) midIndex midCount midSrc midDst second)

theorem one_level_cache (hash : Hash) (s final : MachineState)
    (k src dst ell : Nat)
    (pc : s.pc = 0x1480) (positive : 0 < k) (bound : k ≤ 8)
    (srcCase : src = 0x82000 ∨ src = 0x82100)
    (dstCase : dst = 0x82000 ∨ dst = 0x82100)
    (index : s.getMem 0x81040#64 = 0)
    (count : s.getMem 0x81070#64 = BitVec.ofNat 64 k)
    (source : s.getMem 0x81078#64 = BitVec.ofNat 64 src)
    (destination : s.getMem 0x81080#64 = BitVec.ofNat 64 dst)
    (treeLevel : s.getMem 0x81050#64 = BitVec.ofNat 64 ell)
    (trace : Trace hash image s (79*k+35) (86*k+35) k k final) :
    CacheFrame s final := by
  obtain ⟨nodes,first,nodesPC,_,_⟩ :=
    GroupedBalancedKeygenNodesFold67.nodes hash s 0 k src dst pc positive
      (by omega) srcCase dstCase (by simpa using index)
      (by simpa using count) source destination
  have nodesFrame := nodes_cache hash s nodes 0 k src dst pc positive
    (by omega) srcCase dstCase (by simpa using index)
    (by simpa using count) source destination first
  let made := GroupedBalancedKeygenLevel67.levelState nodes
  have second : Trace hash image nodes 35 35 0 0 made :=
    (GroupedBalancedKeygenLevel67.level_steps nodes nodesPC).trace
  have full : Trace hash image s (79*k+35) (86*k+35) k k made := by
    simpa only [Nat.add_assoc,Nat.add_zero] using first.trans second
  have same : final = made := Trace.deterministic trace full
  rw [same]
  intro a low
  have notHigh (b : Nat) (lower : 0x80000 ≤ b) (upper : b < 2^64) :
      a ≠ BitVec.ofNat 64 b :=
    ne_high a low b lower upper
  rw [GroupedBalancedKeygenRootLevel67.level_frame nodes a
    (notHigh 0x81078 (by decide) (by decide))
    (notHigh 0x81080 (by decide) (by decide))
    (notHigh 0x81070 (by decide) (by decide))
    (notHigh 0x81000 (by decide) (by decide))
    (notHigh 0x81050 (by decide) (by decide))]
  exact nodesFrame a low

#print axioms nodes_cache
#print axioms one_level_cache

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootCacheFold67

end

/-! Low-memory confinement of all fifteen H4 parent hashes. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootCacheTree67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenRootCacheNode67
open GroupedBalancedKeygenRootCacheFold67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

private theorem ne_high (a : Word) (low : a.toNat < 0x20060)
    (b : Nat) (lower : 0x80000 ≤ b) (upper : b < 2^64) :
    a ≠ BitVec.ofNat 64 b := by
  intro eq
  have h := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt upper] at h
  omega

theorem setup_cache (s : MachineState) :
    CacheFrame s (GroupedBalancedKeygenTreeSetup67.setupState s) := by
  intro a low
  exact GroupedBalancedKeygenRootTree67.setup_frame s a
    (ne_high a low 0x81070 (by decide) (by decide))
    (ne_high a low 0x81078 (by decide) (by decide))
    (ne_high a low 0x81080 (by decide) (by decide))
    (ne_high a low 0x81050 (by decide) (by decide))
    (ne_high a low 0x81040 (by decide) (by decide))

theorem reset_cache (s : MachineState) :
    CacheFrame s (GroupedBalancedKeygenReset67.resetState s) := by
  intro a low
  exact GroupedBalancedKeygenReset67.reset_other s a
    (ne_high a low 0x81040 (by decide) (by decide))

theorem tree_cache (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x1428)
    (trace : Trace hash image s 1359 1464 15 15 final) :
    CacheFrame s final := by
  let s0 := GroupedBalancedKeygenTreeSetup67.setupState s
  have t0 : Trace hash image s 22 22 0 0 s0 :=
    (GroupedBalancedKeygenTreeSetup67.setup_steps s pc).trace
  have f0 := setup_cache s
  obtain ⟨c0,src0,dst0,ell0,idx0,_⟩ :=
    GroupedBalancedKeygenSetupControls67.setup_controls s
  obtain ⟨s1,t1,pc1,c1,src1,dst1,ell1,_⟩ :=
    GroupedBalancedKeygenOneLevel67.one_level hash s0 8 0x82000 0x82100 0
      (GroupedBalancedKeygenSetupControls67.setup_pc s pc)
      (by decide) (by decide) (Or.inl rfl) (Or.inr rfl)
      idx0 (by simpa using c0) (by simpa using src0)
      (by simpa using dst0) (by simpa using ell0)
  have f1 := one_level_cache hash s0 s1 8 0x82000 0x82100 0
      (GroupedBalancedKeygenSetupControls67.setup_pc s pc)
      (by decide) (by decide) (Or.inl rfl) (Or.inr rfl)
      idx0 (by simpa using c0) (by simpa using src0)
      (by simpa using dst0) (by simpa using ell0) t1
  have pc1' : s1.pc = 0x1470 := by simpa using pc1
  have c1' : s1.getMem 0x81070#64 = 4 := by simpa using c1
  obtain ⟨r1,u1,rpc1,ri1,rc1,rs1,rd1,re1⟩ :=
    GroupedBalancedKeygenTreeFold67.reset_ready hash s1 4 0x82100 0x82000 1 pc1'
      (by simpa using c1') (by simpa using src1)
      (by simpa using dst1) (by simpa using ell1)
  have fr1 : CacheFrame s1 r1 := by
    have resetTrace : Trace hash image s1 4 4 0 0
        (GroupedBalancedKeygenReset67.resetState s1) :=
      (GroupedBalancedKeygenReset67.reset_steps s1 pc1').trace
    have same := Trace.deterministic u1 resetTrace
    rw [same]
    exact reset_cache s1
  obtain ⟨s2,t2,pc2,c2,src2,dst2,ell2,_⟩ :=
    GroupedBalancedKeygenOneLevel67.one_level hash r1 4 0x82100 0x82000 1
      rpc1 (by decide) (by decide) (Or.inr rfl) (Or.inl rfl)
      ri1 rc1 rs1 rd1 re1
  have f2 := one_level_cache hash r1 s2 4 0x82100 0x82000 1
      rpc1 (by decide) (by decide) (Or.inr rfl) (Or.inl rfl)
      ri1 rc1 rs1 rd1 re1 t2
  have pc2' : s2.pc = 0x1470 := by simpa using pc2
  have c2' : s2.getMem 0x81070#64 = 2 := by simpa using c2
  obtain ⟨r2,u2,rpc2,ri2,rc2,rs2,rd2,re2⟩ :=
    GroupedBalancedKeygenTreeFold67.reset_ready hash s2 2 0x82000 0x82100 2 pc2'
      (by simpa using c2') (by simpa using src2)
      (by simpa using dst2) (by simpa using ell2)
  have fr2 : CacheFrame s2 r2 := by
    have resetTrace : Trace hash image s2 4 4 0 0
        (GroupedBalancedKeygenReset67.resetState s2) :=
      (GroupedBalancedKeygenReset67.reset_steps s2 pc2').trace
    have same := Trace.deterministic u2 resetTrace
    rw [same]
    exact reset_cache s2
  obtain ⟨s3,t3,pc3,c3,src3,dst3,ell3,_⟩ :=
    GroupedBalancedKeygenOneLevel67.one_level hash r2 2 0x82000 0x82100 2
      rpc2 (by decide) (by decide) (Or.inl rfl) (Or.inr rfl)
      ri2 rc2 rs2 rd2 re2
  have f3 := one_level_cache hash r2 s3 2 0x82000 0x82100 2
      rpc2 (by decide) (by decide) (Or.inl rfl) (Or.inr rfl)
      ri2 rc2 rs2 rd2 re2 t3
  have pc3' : s3.pc = 0x1470 := by simpa using pc3
  have c3' : s3.getMem 0x81070#64 = 1 := by simpa using c3
  obtain ⟨r3,u3,rpc3,ri3,rc3,rs3,rd3,re3⟩ :=
    GroupedBalancedKeygenTreeFold67.reset_ready hash s3 1 0x82100 0x82000 3 pc3'
      (by simpa using c3') (by simpa using src3)
      (by simpa using dst3) (by simpa using ell3)
  have fr3 : CacheFrame s3 r3 := by
    have resetTrace : Trace hash image s3 4 4 0 0
        (GroupedBalancedKeygenReset67.resetState s3) :=
      (GroupedBalancedKeygenReset67.reset_steps s3 pc3').trace
    have same := Trace.deterministic u3 resetTrace
    rw [same]
    exact reset_cache s3
  obtain ⟨known,t4,_,_,_,_,_,_⟩ :=
    GroupedBalancedKeygenOneLevel67.one_level hash r3 1 0x82100 0x82000 3
      rpc3 (by decide) (by decide) (Or.inr rfl) (Or.inl rfl)
      ri3 rc3 rs3 rd3 re3
  have f4 := one_level_cache hash r3 known 1 0x82100 0x82000 3
      rpc3 (by decide) (by decide) (Or.inr rfl) (Or.inl rfl)
      ri3 rc3 rs3 rd3 re3 t4
  have full : Trace hash image s 1359 1464 15 15 known := by
    simpa only [Nat.reduceMul,Nat.reduceAdd,Nat.add_zero] using
      (((((((t0.trans t1).trans u1).trans t2).trans u2).trans t3).trans u3).trans t4)
  have same : final = known := Trace.deterministic trace full
  rw [same]
  exact ((((((f0.trans f1).trans fr1).trans f2).trans fr2).trans f3).trans fr3).trans f4

#print axioms tree_cache

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootCacheTree67
