import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafH3Data67

/-! Iterate the completed H3 leaf store once the WOTS handoff is supplied. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperLeafH3Data67
open GroupedBalancedSignBottomStackSlots67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67Byte.image

structure Inv (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected witnessBase i : Nat)
    (s : MachineState) : Prop where
  data : After hash secretKey treeBase leafBase height selected i s
  heightWord : s.getMem 0x81060 = BitVec.ofNat 64 height
  witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase
  currentWitness : ∃ b : Nat,
    s.getMem 0x810f0 = BitVec.ofNat 64 b ∧
    0x20060 ≤ b ∧ b+16*67 ≤ 0x80000 ∧ b%8=0
  stack : s.getReg .x2 = 0xfff7e0 ∨ s.getReg .x2 = 0xfff700
  keyWords : ∀ j : Fin 4,
    s.getMem (Signing.wordAddress 0x20 j.val) =
      secretKey.extractLsb' (64*j.val) 64

def Handoff (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected witnessBase : Nat) : Prop :=
  ∀ (i : Nat) (s : MachineState), i < 2^height →
    Inv hash secretKey treeBase leafBase height selected witnessBase i s →
    ∃ (n c : Nat) (ready : MachineState),
      Trace hash image s n c 247 247 ready ∧
      Ready hash secretKey treeBase leafBase height selected i ready ∧
      ready.getMem 0x81060 = s.getMem 0x81060 ∧
      ready.getMem 0x810f8 = s.getMem 0x810f8 ∧
      ready.getMem 0x810f0 = s.getMem 0x810f0 ∧
      ready.getReg .x2 = s.getReg .x2 ∧
      (∀ j : Fin 4, ready.getMem (Signing.wordAddress 0x20 j.val) =
        s.getMem (Signing.wordAddress 0x20 j.val))

theorem one_step (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected witnessBase i : Nat)
    (s : MachineState)
    (hh : height = 3 ∨ height = 4)
    (aligned : leafBase % 2^height = 0)
    (bound : leafBase+2^height ≤ 2^160)
    (hi : i<2^height)
    (inv : Inv hash secretKey treeBase leafBase height selected witnessBase i s)
    (handoff : Handoff hash secretKey treeBase leafBase height
      selected witnessBase) :
    ∃ (n c : Nat) (next : MachineState),
      Trace hash image s n c 248 265 next ∧
      Inv hash secretKey treeBase leafBase height selected witnessBase
        (i+1) next := by
  obtain ⟨n,c,ready,wotsTrace,readyData,readyHeight,readyWitness,
    readyCurrent,readySp,readyKey⟩ :=
    handoff i s hi inv
  obtain ⟨next,h3Trace,after,frame,nextSp,nextLow,_nextDigits⟩ :=
    one_leaf hash secretKey treeBase leafBase height selected i ready
      hh aligned bound hi readyData
  have countSmall : (ready.getMem 0x810e0).toNat<1024 := by
    rw [readyData.count]
    simp only [BitVec.toNat_ofNat]
    have hi16 : i<16 := by rcases hh with rfl | rfl <;> omega
    rw [Nat.mod_eq_of_lt (by omega : i<2^64)]
    omega
  have stable (a : Word) (high : 0x81000 ≤ a.toNat)
      (low : a.toNat < 0x83000) (not08 : a≠0x81008)
      (notE0 : a≠0x810e0) : next.getMem a=ready.getMem a := by
    obtain ⟨ne0,ne8⟩ := GroupedBalancedSignBottomStackBound67.below_stack
      (ready.getMem 0x810e0) a countSmall low
    exact frame a high ne0 ne8 not08 notE0
  have nextHeight : next.getMem 0x81060 = BitVec.ofNat 64 height := by
    rw [stable 0x81060 (by decide) (by decide) (by decide) (by decide),
      readyHeight]
    exact inv.heightWord
  have nextWitness : next.getMem 0x810f8 = BitVec.ofNat 64 witnessBase := by
    rw [stable 0x810f8 (by decide) (by decide) (by decide) (by decide),
      readyWitness]
    exact inv.witness
  have nextCurrent : ∃ b : Nat,
      next.getMem 0x810f0 = BitVec.ofNat 64 b ∧
      0x20060 ≤ b ∧ b+16*67 ≤ 0x80000 ∧ b%8=0 := by
    obtain ⟨b,bword,bLower,bUpper,bAlign⟩ := inv.currentWitness
    refine ⟨b,?_,bLower,bUpper,bAlign⟩
    rw [stable 0x810f0 (by decide) (by decide)
      (by decide) (by decide),readyCurrent,bword]
  have nextStack : next.getReg .x2 = 0xfff7e0 ∨
      next.getReg .x2 = 0xfff700 := by
    rw [nextSp,readySp]
    exact inv.stack
  have nextKey : ∀ j : Fin 4,
      next.getMem (Signing.wordAddress 0x20 j.val) =
        secretKey.extractLsb' (64*j.val) 64 := by
    intro j
    rw [nextLow _ (by fin_cases j <;> decide),readyKey j]
    exact inv.keyWords j
  refine ⟨n+66,c+209,next,?_,⟨after,nextHeight,nextWitness,
    nextCurrent,nextStack,nextKey⟩⟩
  simpa [Nat.add_assoc] using wotsTrace.trans h3Trace

theorem run_prefix (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected witnessBase : Nat)
    (start : MachineState)
    (hh : height = 3 ∨ height = 4)
    (aligned : leafBase % 2^height = 0)
    (bound : leafBase+2^height ≤ 2^160)
    (initial : Inv hash secretKey treeBase leafBase height selected
      witnessBase 0 start)
    (handoff : Handoff hash secretKey treeBase leafBase height
      selected witnessBase) :
    ∀ i, i≤2^height →
      ∃ (n c : Nat) (final : MachineState),
        Trace hash image start n c (248*i) (265*i) final ∧
        Inv hash secretKey treeBase leafBase height selected witnessBase i
          final := by
  intro i hi
  induction i with
  | zero =>
      exact ⟨0,0,start,by simpa using
        (Trace.refl (hash := hash) (image := image) start),initial⟩
  | succ i ih =>
      have before : i≤2^height := by omega
      have stepBound : i<2^height := by omega
      obtain ⟨n,c,mid,pretrace,midInv⟩ := ih before
      obtain ⟨sn,sc,final,step,finalInv⟩ := one_step hash secretKey
        treeBase leafBase height selected witnessBase i mid hh aligned
        bound stepBound midInv handoff
      refine ⟨n+sn,c+sc,final,?_,finalInv⟩
      simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        using pretrace.trans step

theorem run_all (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected witnessBase : Nat)
    (start : MachineState)
    (hh : height = 3 ∨ height = 4)
    (aligned : leafBase % 2^height = 0)
    (bound : leafBase+2^height ≤ 2^160)
    (initial : Inv hash secretKey treeBase leafBase height selected
      witnessBase 0 start)
    (handoff : Handoff hash secretKey treeBase leafBase height
      selected witnessBase) :
    ∃ (n c : Nat) (final : MachineState),
      Trace hash image start n c (248*2^height) (265*2^height) final ∧
      final.pc=0x1c30 ∧
      final.getMem 0x81000=BitVec.ofNat 64 treeBase ∧
      final.getMem 0x81060=BitVec.ofNat 64 height ∧
      final.getMem 0x810f8=BitVec.ofNat 64 witnessBase ∧
      final.getMem 0x810d0=BitVec.ofNat 64 (2^height) ∧
      final.getMem 0x810e8=BitVec.ofNat 64 selected ∧
      (∀ w : Fin 3,
        final.getMem (Signing.wordAddress 0x810a8 w.val)=
          (BitVec.ofNat 192 leafBase).extractLsb' (64*w.val) 64) ∧
      (∀ j, j<2^height → ∀ w : Fin 2,
        final.getMem (slot j w.val)=
          (GroupedBalancedUpperTree67.leafRoot hash secretKey treeBase
            (leafBase+j)).extractLsb' (64*w.val) 64) ∧
      (final.getReg .x2=0xfff7e0 ∨ final.getReg .x2=0xfff700) := by
  obtain ⟨n,c,final,path,inv⟩ := run_prefix hash secretKey treeBase
    leafBase height selected witnessBase start hh aligned bound initial
    handoff (2^height) (by omega)
  refine ⟨n,c,final,path,?_,inv.data.tree,inv.heightWord,inv.witness,
    inv.data.limit,inv.data.chosen,inv.data.scratch,inv.data.previous,inv.stack⟩
  simpa using inv.data.pc

#print axioms one_step
#print axioms run_all
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafFold67
