import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomHashStack67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafInvariant67

/-! The signer stack pointer survives every bottom-leaf iteration. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafStack67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

private abbrev image := GroupedBalancedSignImage67.image

theorem run_prefix_stack (hash : Hash) (secretKey : SecretKey)
    (base : Nat) (selected : Word) (start : MachineState)
    (hbase : base + 1024 ≤ 2^160)
    (halign : base % 1024 = 0)
    (initial : GroupedBalancedSignBottomLeafInvariant67.Inv
      hash secretKey base selected 0 start) :
    ∀ i : Nat, i ≤ 1024 →
      ∃ (n c : Nat) (finish : MachineState),
        Trace hash image start n c (2*i) (2*i) finish ∧
        GroupedBalancedSignBottomLeafInvariant67.Inv
          hash secretKey base selected i finish ∧
        (∀ a : Word,
          GroupedBalancedSignBottomLeafTickData67.StableAddress a →
            finish.getMem a = start.getMem a) ∧
        finish.getReg .x2 = start.getReg .x2 ∧
        n ≤ 166*i ∧ c ≤ 180*i ∧
        (∀ w : Fin 2, selected.toNat < i →
          finish.getMem (Signing.wordAddress 0x20080 w.val) =
            (GroupedBottomTree.secret hash secretKey
              (base+selected.toNat)).extractLsb' (64*w.val) 64) := by
  intro i hi
  induction i with
  | zero =>
    exact ⟨0,0,start,by simpa using
      (Trace.refl (hash := hash) (image := image) start),initial,
      by intro a _; rfl,rfl,by omega,by omega,
      by intro w h; omega⟩
  | succ i ih =>
    have hi0 : i < 1024 := by omega
    obtain ⟨n,c,mid,trace,midInv,midStable,midSp,nBound,cBound,midSeed⟩ :=
      ih (by omega)
    obtain ⟨next,step,nextInv,stepStable,selectedWords,skippedWords⟩ :=
      GroupedBalancedSignBottomLeafInvariant67.inv_step hash secretKey
        base selected i mid hbase halign hi0 midInv
    obtain ⟨midPc,midCount,midChosen,midLevel,midAddress,midKey,_⟩ := midInv
    have entryPc : mid.pc = 0x12cc := by simpa [hi0] using midPc
    have countBound : (mid.getMem 0x810e0).toNat < 1024 := by
      rw [midCount]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
      exact hi0
    have nextSp : next.getReg .x2 = mid.getReg .x2 :=
      GroupedBalancedSignBottomHashStack67.leaf_tick_sp hash secretKey
        (base+i) mid next entryPc countBound midLevel
        (midAddress hi0) midKey step
    refine ⟨n + (if mid.getMem 0x810e0 = mid.getMem 0x810e8 then 166 else 149),
      c + (if mid.getMem 0x810e0 = mid.getMem 0x810e8 then 180 else 163),
      next,?_,nextInv,?_,nextSp.trans midSp,?_,?_,?_⟩
    · simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        trace.trans step
    · intro a ha
      exact (stepStable a ha).trans (midStable a ha)
    · simp only [Nat.mul_succ]
      split_ifs <;> omega
    · simp only [Nat.mul_succ]
      split_ifs <;> omega
    · intro w picked
      by_cases atNow : selected.toNat = i
      · have choose : mid.getMem 0x810e0 = mid.getMem 0x810e8 := by
          rw [midCount,midChosen,←atNow]
          simp
        simpa [atNow] using selectedWords choose w
      · have skip : mid.getMem 0x810e0 ≠ mid.getMem 0x810e8 := by
          intro eq
          have hn := congrArg BitVec.toNat eq
          rw [midCount,midChosen] at hn
          simp only [BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : i < 2^64)] at hn
          exact atNow hn.symm
        exact (skippedWords skip w).trans (midSeed w (by omega))

theorem run_all_stack (hash : Hash) (secretKey : SecretKey)
    (base : Nat) (selected : Word) (start : MachineState)
    (hbase : base + 1024 ≤ 2^160)
    (halign : base % 1024 = 0)
    (initial : GroupedBalancedSignBottomLeafInvariant67.Inv
      hash secretKey base selected 0 start) :
    ∃ (n c : Nat) (finish : MachineState),
      Trace hash image start n c 2048 2048 finish ∧
      finish.pc = 0x14ec ∧
      (∀ j : Nat, j < 1024 →
        finish.getMem (GroupedBalancedSignBottomStackSlots67.slot j 0) =
          (GroupedBottomTree.leafRoot hash secretKey (base+j)).extractLsb' 0 64 ∧
        finish.getMem (GroupedBalancedSignBottomStackSlots67.slot j 1) =
          (GroupedBottomTree.leafRoot hash secretKey (base+j)).extractLsb' 64 64) ∧
      (∀ a : Word,
        GroupedBalancedSignBottomLeafTickData67.StableAddress a →
          finish.getMem a = start.getMem a) ∧
      finish.getReg .x2 = start.getReg .x2 ∧
      n ≤ 169984 ∧ c ≤ 184320 ∧
      (∀ w : Fin 2, selected.toNat < 1024 →
        finish.getMem (Signing.wordAddress 0x20080 w.val) =
          (GroupedBottomTree.secret hash secretKey
            (base+selected.toNat)).extractLsb' (64*w.val) 64) := by
  obtain ⟨n,c,finish,trace,inv,stable,stack,nBound,cBound,seedWords⟩ :=
    run_prefix_stack hash secretKey base selected start hbase halign initial
      1024 (by decide)
  refine ⟨n,c,finish,by simpa using trace,?_,?_,stable,stack,
    by omega,by omega,seedWords⟩
  · exact inv.1.trans (by decide)
  · exact inv.2.2.2.2.2.2

#print axioms run_all_stack
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafStack67
