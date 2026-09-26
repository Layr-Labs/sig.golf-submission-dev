import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafFold67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeControlFrame67

/-! Strengthened leaf fold preserving signer key, public key, and layer controls. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafPersistent67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperLeafH3Data67
open GroupedBalancedSignUpperLeafFold67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67Byte.image

def Persistent (a : Word) : Prop :=
  a.toNat < 0x100 ∨ GroupedBalancedSignUpperTreeControlFrame67.Safe a ∨
    0xfff700 ≤ a.toNat

def Handoff (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected witnessBase : Nat) : Prop :=
  ∀ (i : Nat) (s : MachineState), i < 2^height →
    GroupedBalancedSignUpperLeafFold67.Inv hash secretKey treeBase
      leafBase height selected witnessBase i s →
    ∃ (n c : Nat) (ready : MachineState),
      Trace hash image s n c 247 247 ready ∧
      Ready hash secretKey treeBase leafBase height selected i ready ∧
      ready.getMem 0x81060 = s.getMem 0x81060 ∧
      ready.getMem 0x810f8 = s.getMem 0x810f8 ∧
      ready.getMem 0x810f0 = s.getMem 0x810f0 ∧
      ready.getReg .x2 = s.getReg .x2 ∧
      (∀ j : Fin 4, ready.getMem (Signing.wordAddress 0x20 j.val) =
        s.getMem (Signing.wordAddress 0x20 j.val)) ∧
      (∀ a : Word, Persistent a → ready.getMem a=s.getMem a) ∧
      n ≤ 36122 ∧ c ≤ 41281

theorem one_step (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected witnessBase i : Nat)
    (s : MachineState)
    (hh : height = 3 ∨ height = 4)
    (aligned : leafBase % 2^height = 0)
    (bound : leafBase+2^height ≤ 2^160)
    (hi : i<2^height)
    (inv : GroupedBalancedSignUpperLeafFold67.Inv hash secretKey treeBase
      leafBase height selected witnessBase i s)
    (handoff : Handoff hash secretKey treeBase leafBase height
      selected witnessBase) :
    ∃ (n c : Nat) (next : MachineState),
      Trace hash image s n c 248 265 next ∧
      GroupedBalancedSignUpperLeafFold67.Inv hash secretKey treeBase
        leafBase height selected witnessBase (i+1) next ∧
      (∀ a : Word, Persistent a → next.getMem a=s.getMem a) ∧
      next.getReg .x2=s.getReg .x2 ∧
      n ≤ 36188 ∧ c ≤ 41490 := by
  obtain ⟨n,c,ready,wotsTrace,readyData,readyHeight,readyWitness,
    readyCurrent,readySp,readyKey,readyFrame,nBound,cBound⟩ := handoff i s hi inv
  obtain ⟨next,h3Trace,after,frame,nextSp,nextLow,_nextDigits⟩ :=
    GroupedBalancedSignUpperLeafH3Data67.one_leaf hash secretKey treeBase
      leafBase height selected i ready hh aligned bound hi readyData
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
    rw [stable 0x810f0 (by decide) (by decide) (by decide) (by decide),
      readyCurrent,bword]
  have nextStack : next.getReg .x2=0xfff7e0 ∨ next.getReg .x2=0xfff700 := by
    rw [nextSp,readySp]
    exact inv.stack
  have nextKey : ∀ j : Fin 4,
      next.getMem (Signing.wordAddress 0x20 j.val) =
        secretKey.extractLsb' (64*j.val) 64 := by
    intro j
    rw [nextLow _ (by fin_cases j <;> decide),readyKey j]
    exact inv.keyWords j
  have nextFrame : ∀ a : Word, Persistent a → next.getMem a=s.getMem a := by
    intro a ha
    have leafFrame : next.getMem a=ready.getMem a := by
      rcases ha with low | safe | table
      · exact nextLow a (by omega)
      · obtain ⟨high,below,_,_,ne08,_,_,_,_,_,_,_,_,_,_⟩ :=
          GroupedBalancedSignUpperTreeControlFrame67.safe_facts a safe
        have neE0 : a≠0x810e0 := by
          rcases safe with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        exact stable a high below ne08 neE0
      · have slotRange := GroupedBalancedSignBottomStackBound67.stack0_range
          (ready.getMem 0x810e0) countSmall
        have slot8 := GroupedBalancedSignBottomStackBound67.stack8_nat
          (ready.getMem 0x810e0) countSmall
        have ne0 : a≠GroupedBalancedSignBottomStackBound67.stack0
            (ready.getMem 0x810e0) := by
          intro eq
          have hn := congrArg BitVec.toNat eq
          omega
        have ne8 : a≠GroupedBalancedSignBottomStackBound67.stack0
            (ready.getMem 0x810e0)+8 := by
          intro eq
          have hn := congrArg BitVec.toNat eq
          rw [slot8] at hn
          omega
        have ne08 : a≠0x81008 := by
          intro eq
          have hn := congrArg BitVec.toNat eq
          simp at hn
          omega
        have neE0 : a≠0x810e0 := by
          intro eq
          have hn := congrArg BitVec.toNat eq
          simp at hn
          omega
        exact frame a (by omega) ne0 ne8 ne08 neE0
    exact leafFrame.trans (readyFrame a ha)
  refine ⟨n+66,c+209,next,?_,
    ⟨after,nextHeight,nextWitness,nextCurrent,nextStack,nextKey⟩,
    nextFrame,by rw [nextSp,readySp],by omega,by omega⟩
  simpa [Nat.add_assoc] using wotsTrace.trans h3Trace

theorem run_prefix (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected witnessBase : Nat)
    (start : MachineState)
    (hh : height = 3 ∨ height = 4)
    (aligned : leafBase % 2^height = 0)
    (bound : leafBase+2^height ≤ 2^160)
    (initial : GroupedBalancedSignUpperLeafFold67.Inv hash secretKey treeBase
      leafBase height selected witnessBase 0 start)
    (handoff : Handoff hash secretKey treeBase leafBase height
      selected witnessBase) :
    ∀ i, i≤2^height →
      ∃ (n c : Nat) (final : MachineState),
        Trace hash image start n c (248*i) (265*i) final ∧
        GroupedBalancedSignUpperLeafFold67.Inv hash secretKey treeBase
          leafBase height selected witnessBase i final ∧
        (∀ a : Word, Persistent a → final.getMem a=start.getMem a) ∧
        final.getReg .x2=start.getReg .x2 ∧
        n ≤ 36188*i ∧ c ≤ 41490*i := by
  intro i hi
  induction i with
  | zero =>
      exact ⟨0,0,start,by simpa using
        (Trace.refl (hash := hash) (image := image) start),initial,
        by intro a _; rfl,rfl,by omega,by omega⟩
  | succ i ih =>
      obtain ⟨n,c,mid,pretrace,midInv,midFrame,midSp,nBound,cBound⟩ := ih (by omega)
      obtain ⟨sn,sc,final,step,finalInv,stepFrame,stepSp,snBound,scBound⟩ := one_step hash
        secretKey treeBase leafBase height selected witnessBase i mid
        hh aligned bound (by omega) midInv handoff
      refine ⟨n+sn,c+sc,final,?_,finalInv,?_,stepSp.trans midSp,?_,?_⟩
      · simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using pretrace.trans step
      · intro a safe
        exact (stepFrame a safe).trans (midFrame a safe)
      · simp only [Nat.mul_succ]
        omega
      · simp only [Nat.mul_succ]
        omega

theorem run_all (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected witnessBase : Nat)
    (start : MachineState)
    (hh : height = 3 ∨ height = 4)
    (aligned : leafBase % 2^height = 0)
    (bound : leafBase+2^height ≤ 2^160)
    (initial : GroupedBalancedSignUpperLeafFold67.Inv hash secretKey treeBase
      leafBase height selected witnessBase 0 start)
    (handoff : Handoff hash secretKey treeBase leafBase height
      selected witnessBase) :
    ∃ (n c : Nat) (final : MachineState),
      Trace hash image start n c (248*2^height) (265*2^height) final ∧
      GroupedBalancedSignUpperLeafFold67.Inv hash secretKey treeBase
        leafBase height selected witnessBase (2^height) final ∧
      (∀ a : Word, Persistent a → final.getMem a=start.getMem a) ∧
      final.getReg .x2=start.getReg .x2 ∧
      n ≤ 36188*2^height ∧ c ≤ 41490*2^height := by
  exact run_prefix hash secretKey treeBase leafBase height selected
    witnessBase start hh aligned bound initial handoff (2^height) (by omega)

#print axioms one_step
#print axioms run_prefix
#print axioms run_all
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafPersistent67
