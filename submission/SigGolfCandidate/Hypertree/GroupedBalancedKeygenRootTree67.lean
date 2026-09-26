import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootLevel67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenTreeFold67

/-! Four exact H4 keygen levels produce the reference public root. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootTree67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenRootNodes67
set_option maxRecDepth 16384
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedKeygenImage67.image
private abbrev root := GroupedBalancedUpperTree67.root
private abbrev setup := GroupedBalancedKeygenTreeSetup67.setupState
private abbrev reset := GroupedBalancedKeygenReset67.resetState

theorem setup_frame (s : MachineState) (a : Word)
    (ne70 : a ≠ 0x81070#64) (ne78 : a ≠ 0x81078#64)
    (ne80 : a ≠ 0x81080#64) (ne50 : a ≠ 0x81050#64)
    (ne40 : a ≠ 0x81040#64) :
    (setup s).getMem a = s.getMem a := by
  simp [setup,GroupedBalancedKeygenTreeSetup67.setupState,
    execInstrBr,signExtend12,ne70,ne78,ne80,ne50,ne40,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem setup_high (s : MachineState) (a : Word)
    (high : 0x82000 ≤ a.toNat) : (setup s).getMem a = s.getMem a := by
  have ne (b : Nat) (small : b < 0x82000) : a ≠ BitVec.ofNat 64 b := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : b < 2^64)] at hn
    omega
  exact setup_frame s a (ne 0x81070 (by decide)) (ne 0x81078 (by decide))
    (ne 0x81080 (by decide)) (ne 0x81050 (by decide))
    (ne 0x81040 (by decide))

theorem reset_high (s : MachineState) (a : Word)
    (high : 0x82000 ≤ a.toNat) : (reset s).getMem a = s.getMem a := by
  apply GroupedBalancedKeygenReset67.reset_other s a
  intro eq
  have hn := congrArg BitVec.toNat eq
  have v : (0x81040#64 : Word).toNat = 0x81040 := by decide
  rw [v] at hn
  omega

theorem reset_low (s : MachineState) (a : Word)
    (ne : a ≠ 0x81040#64) : (reset s).getMem a = s.getMem a :=
  GroupedBalancedKeygenReset67.reset_other s a ne

theorem reset_ready_values (hash : Hash) (secretKey : SecretKey)
    (s : MachineState) (base ell k src dst : Nat)
    (pc : s.pc = 0x1470) (kBound : k ≤ 8)
    (srcCase : src = 0x82000 ∨ src = 0x82100)
    (count : s.getMem 0x81070#64 = BitVec.ofNat 64 k)
    (source : s.getMem 0x81078#64 = BitVec.ofNat 64 src)
    (destination : s.getMem 0x81080#64 = BitVec.ofNat 64 dst)
    (treeLevel : s.getMem 0x81050#64 = BitVec.ofNat 64 ell)
    (levelWord : s.getMem 0x81000 = BitVec.ofNat 64 (base+ell))
    (index1 : s.getMem 0x81010 = 0#64)
    (index2 : s.getMem 0x81018 = 0#64)
    (table : ∀ j : Nat, j < 2*k → ∀ i : Fin 2,
      s.getMem (Signing.wordAddress (src+16*j) i.val) =
        (root hash secretKey base ell j).extractLsb' (64*i.val) 64) :
    ∃ ready,
      Trace hash image s 4 4 0 0 ready ∧ ready.pc = 0x1480 ∧
      ready.getMem 0x81040#64 = 0#64 ∧
      ready.getMem 0x81070#64 = BitVec.ofNat 64 k ∧
      ready.getMem 0x81078#64 = BitVec.ofNat 64 src ∧
      ready.getMem 0x81080#64 = BitVec.ofNat 64 dst ∧
      ready.getMem 0x81050#64 = BitVec.ofNat 64 ell ∧
      ready.getMem 0x81000 = BitVec.ofNat 64 (base+ell) ∧
      ready.getMem 0x81010 = 0#64 ∧ ready.getMem 0x81018 = 0#64 ∧
      (∀ j : Nat, j < 2*k → ∀ i : Fin 2,
        ready.getMem (Signing.wordAddress (src+16*j) i.val) =
          (root hash secretKey base ell j).extractLsb' (64*i.val) 64) := by
  let ready := reset s
  refine ⟨ready,(GroupedBalancedKeygenReset67.reset_steps s pc).trace,
    GroupedBalancedKeygenReset67.reset_pc s pc,
    GroupedBalancedKeygenReset67.reset_counter s,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [reset_low s 0x81070#64 (by decide),count]
  · rw [reset_low s 0x81078#64 (by decide),source]
  · rw [reset_low s 0x81080#64 (by decide),destination]
  · rw [reset_low s 0x81050#64 (by decide),treeLevel]
  · rw [reset_low s 0x81000 (by decide),levelWord]
  · rw [reset_low s 0x81010 (by decide),index1]
  · rw [reset_low s 0x81018 (by decide),index2]
  · intro j jBound i
    rw [reset_high s (Signing.wordAddress (src+16*j) i.val)
      (table_word_high src j i srcCase (by omega))]
    exact table j jBound i

theorem tree_values (hash : Hash) (secretKey : SecretKey) (s : MachineState)
    (pc : s.pc = 0x1428)
    (levelWord : s.getMem 0x81000 = BitVec.ofNat 64 156)
    (index1 : s.getMem 0x81010 = 0#64)
    (index2 : s.getMem 0x81018 = 0#64)
    (leaves : ∀ j : Nat, j < 16 → ∀ i : Fin 2,
      s.getMem (Signing.wordAddress (0x82000+16*j) i.val) =
        (root hash secretKey 156 0 j).extractLsb' (64*i.val) 64) :
    ∃ final, Trace hash image s 1359 1464 15 15 final ∧
      final.pc = 0x1648 ∧
      final.getMem 0x81078#64 = 0x82000#64 ∧
      final.getMem 0x81050#64 = 4#64 ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress 0x82000 i.val) =
        (root hash secretKey 156 4 0).extractLsb' (64*i.val) 64) := by
  let s0 := setup s
  have t0 : Trace hash image s 22 22 0 0 s0 :=
    (GroupedBalancedKeygenTreeSetup67.setup_steps s pc).trace
  obtain ⟨c0,src0,dst0,ell0,idx0,_⟩ :=
    GroupedBalancedKeygenSetupControls67.setup_controls s
  have w0 : s0.getMem 0x81000 = BitVec.ofNat 64 (156+0) := by
    rw [setup_frame s 0x81000 (by decide) (by decide) (by decide)
      (by decide) (by decide),levelWord]
  have i10 : s0.getMem 0x81010 = 0#64 := by
    rw [setup_frame s 0x81010 (by decide) (by decide) (by decide)
      (by decide) (by decide),index1]
  have i20 : s0.getMem 0x81018 = 0#64 := by
    rw [setup_frame s 0x81018 (by decide) (by decide) (by decide)
      (by decide) (by decide),index2]
  have table0 : ∀ j : Nat, j < 16 → ∀ i : Fin 2,
      s0.getMem (Signing.wordAddress (0x82000+16*j) i.val) =
        (root hash secretKey 156 0 j).extractLsb' (64*i.val) 64 := by
    intro j jBound i
    rw [setup_high s (Signing.wordAddress (0x82000+16*j) i.val)
      (table_word_high 0x82000 j i (Or.inl rfl) jBound)]
    exact leaves j jBound i
  obtain ⟨s1,t1,pc1,c1,src1,dst1,ell1,w1,i11,i21,table1⟩ :=
    GroupedBalancedKeygenRootLevel67.level_values hash secretKey s0
      156 0 8 0x82000 0x82100
      (GroupedBalancedKeygenSetupControls67.setup_pc s pc)
      (by decide) (by decide) (Or.inl rfl) (Or.inr rfl) (by decide)
      idx0 (by simpa using c0) (by simpa using src0)
      (by simpa using dst0) (by simpa using ell0)
      w0 i10 i20 (by simpa using table0)
  have pc1' : s1.pc = 0x1470 := by simpa using pc1
  have c1' : s1.getMem 0x81070#64 = 4#64 := by simpa using c1
  obtain ⟨r1,u1,rpc1,ri1,rc1,rs1,rd1,re1,rw1,ri11,ri21,rt1⟩ :=
    reset_ready_values hash secretKey s1 156 1 4 0x82100 0x82000
      pc1' (by decide) (Or.inr rfl) c1'
      (by simpa using src1) (by simpa using dst1)
      (by simpa using ell1) (by simpa using w1) i11 i21
      (by simpa using table1)
  obtain ⟨s2,t2,pc2,c2,src2,dst2,ell2,w2,i12,i22,table2⟩ :=
    GroupedBalancedKeygenRootLevel67.level_values hash secretKey r1
      156 1 4 0x82100 0x82000
      rpc1 (by decide) (by decide) (Or.inr rfl) (Or.inl rfl) (by decide)
      ri1 rc1 rs1 rd1 re1 rw1 ri11 ri21 rt1
  have pc2' : s2.pc = 0x1470 := by simpa using pc2
  have c2' : s2.getMem 0x81070#64 = 2#64 := by simpa using c2
  obtain ⟨r2,u2,rpc2,ri2,rc2,rs2,rd2,re2,rw2,ri12,ri22,rt2⟩ :=
    reset_ready_values hash secretKey s2 156 2 2 0x82000 0x82100
      pc2' (by decide) (Or.inl rfl) c2'
      (by simpa using src2) (by simpa using dst2)
      (by simpa using ell2) (by simpa using w2) i12 i22
      (by simpa using table2)
  obtain ⟨s3,t3,pc3,c3,src3,dst3,ell3,w3,i13,i23,table3⟩ :=
    GroupedBalancedKeygenRootLevel67.level_values hash secretKey r2
      156 2 2 0x82000 0x82100
      rpc2 (by decide) (by decide) (Or.inl rfl) (Or.inr rfl) (by decide)
      ri2 rc2 rs2 rd2 re2 rw2 ri12 ri22 rt2
  have pc3' : s3.pc = 0x1470 := by simpa using pc3
  have c3' : s3.getMem 0x81070#64 = 1#64 := by simpa using c3
  obtain ⟨r3,u3,rpc3,ri3,rc3,rs3,rd3,re3,rw3,ri13,ri23,rt3⟩ :=
    reset_ready_values hash secretKey s3 156 3 1 0x82100 0x82000
      pc3' (by decide) (Or.inr rfl) c3'
      (by simpa using src3) (by simpa using dst3)
      (by simpa using ell3) (by simpa using w3) i13 i23
      (by simpa using table3)
  obtain ⟨final,t4,pc4,_,src4,_,ell4,_,_,_,table4⟩ :=
    GroupedBalancedKeygenRootLevel67.level_values hash secretKey r3
      156 3 1 0x82100 0x82000
      rpc3 (by decide) (by decide) (Or.inr rfl) (Or.inl rfl) (by decide)
      ri3 rc3 rs3 rd3 re3 rw3 ri13 ri23 rt3
  refine ⟨final,?_,by simpa using pc4,by simpa using src4,
    by simpa using ell4,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd,Nat.add_zero] using
      (((((((t0.trans t1).trans u1).trans t2).trans u2).trans t3).trans u3).trans t4)
  · intro i
    simpa [Signing.wordAddress] using table4 0 (by decide) i

#print axioms tree_values

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootTree67
