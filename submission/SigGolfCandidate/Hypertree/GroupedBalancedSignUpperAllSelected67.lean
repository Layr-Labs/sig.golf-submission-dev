import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedOuterComplete67

/-! Every upper WOTS and sibling word survives all later signing groups. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperAllSelected67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperSchedule67
open GroupedBalancedSignUpperOuterInvariant67
open GroupedBalancedSignUpperSelectedOuterFold67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev slot := GroupedBalancedSignUpperH2WitnessFrame67.slot

def messageAfter (hash : Hash) (secretKey : SecretKey)
    (initialIndex : BitVec 192) (k : Nat) (message : BitVec 128) :
    Nat → BitVec 128
  | 0 => message
  | m+1 => groupRoot hash secretKey initialIndex (k+m)

private theorem wots_before (g last : Nat) (hg : g<last) (lastBound : last≤45)
    (chain : GroupedBalancedUpperTree67.ChainMixed) (w : Fin 2) :
    (slot (currentWitness g) chain w).toNat < currentWitness last := by
  have bound := witness_current_upper g (by omega : g≤45)
  have nat := GroupedBalancedSignUpperH2WitnessFrame67.slot_nat
    (currentWitness g) chain w (by have hc := chain.isLt; omega)
  have near : (slot (currentWitness g) chain w).toNat <
      currentWitness (g+1) := by
    rw [nat,witness_next]
    unfold GroupedBalancedSignUpperSchedule67.witnessBase
    have hc := chain.isLt
    have hw := w.isLt
    omega
  have mono := current_mono (g+1) (last-(g+1))
  have eq : g+1+(last-(g+1))=last := by omega
  rw [eq] at mono
  omega

private theorem sibling_before (g last level : Nat)
    (hg : g<last) (lastBound : last≤45) (hlevel : level<height g)
    (i : Fin 2) :
    (BitVec.ofNat 64 (witnessBase g+16*level+8*i.val)).toNat <
      currentWitness last := by
  have bound := witness_base_bound g (by omega : g<45)
  have nat : (BitVec.ofNat 64
      (witnessBase g+16*level+8*i.val)).toNat =
      witnessBase g+16*level+8*i.val := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by
      have hi := i.isLt
      omega)]
  have near : (BitVec.ofNat 64
      (witnessBase g+16*level+8*i.val)).toNat <
      currentWitness (g+1) := by
    rw [nat,witness_next]
    have hi := i.isLt
    omega
  have mono := current_mono (g+1) (last-(g+1))
  have eq : g+1+(last-(g+1))=last := by omega
  rw [eq] at mono
  omega

theorem run_from_all (hash : Hash) (secretKey : SecretKey)
    (initialIndex : BitVec 192) (initialBound : initialIndex.toNat<2^150)
    (k m : Nat) (hk : k+m≤44)
    (message : BitVec 128) (start : MachineState)
    (initial : Boundary hash secretKey initialIndex k message start) :
    ∃ (n c : Nat) (currentMessage : BitVec 128) (final : MachineState),
      Trace hash image start n c (callsFrom k m) (blocksFrom k m) final ∧
      Boundary hash secretKey initialIndex (k+m) currentMessage final ∧
      currentMessage = messageAfter hash secretKey initialIndex k message m ∧
      (∀ a : Word, a.toNat<currentWitness k →
        final.getMem a=start.getMem a) ∧
      (∀ g, k≤g → g<k+m →
        ∀ chain : GroupedBalancedUpperTree67.ChainMixed, ∀ w : Fin 2,
          final.getMem (slot (currentWitness g) chain w) =
            (GroupedBalancedUpperTree67.signValues hash secretKey
              (treeBase g) (indexAt initialIndex g).toNat
              (messageAfter hash secretKey initialIndex k message (g-k))
              chain).extractLsb' (64*w.val) 64) ∧
      (∀ g, k≤g → g<k+m → ∀ level, level<height g → ∀ i : Fin 2,
        final.getMem (BitVec.ofNat 64
          (witnessBase g+16*level+8*i.val))=
          (GroupedBalancedSignUpperTreeModel67.nodeAt hash (treeBase g)
            ((indexAt initialIndex g).toNat/2^height g*2^height g)
            (fun x => GroupedBalancedUpperTree67.leafRoot hash secretKey
              (treeBase g)
              ((indexAt initialIndex g).toNat/2^height g*2^height g+x))
            level
            (Nat.xor (((indexAt initialIndex g).toNat%2^height g)/2^level)
              1)).extractLsb' (64*i.val) 64) ∧
      n ≤ 603000*m ∧ c ≤ 703000*m := by
  induction m with
  | zero =>
      refine ⟨0,0,message,start,?_,by simpa using initial,rfl,?_,?_,?_,
        by omega,by omega⟩
      · simpa [callsFrom,blocksFrom] using
          (Trace.refl (hash := hash) (image := image) start)
      · intro a _; rfl
      · intro g _ impossible; omega
      · intro g _ impossible; omega
  | succ m ih =>
      have hk44 : k+m<44 := by omega
      obtain ⟨n,c,currentMessage,middle,path,boundary,messageEq,oldFrame,
        oldWots,oldSiblings,nBound,cBound⟩ := ih (by omega)
      obtain ⟨sn,sc,final,step,next,snBound,scBound,newWots,
        newSiblings,prior⟩ :=
        GroupedBalancedSignUpperSelectedOuterStep67.one_step hash secretKey
          initialIndex initialBound (k+m) hk44 currentMessage middle boundary
      refine ⟨n+sn,c+sc,groupRoot hash secretKey initialIndex (k+m),final,
        ?_,by simpa [Nat.add_assoc] using next,?_,?_,?_,?_,?_,?_⟩
      · have full := path.trans step
        simpa [callsFrom,blocksFrom,Finset.sum_range_succ,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using full
      · rfl
      · intro a ha
        have hmono := current_mono k m
        exact (prior a (by omega)).trans (oldFrame a ha)
      · intro g kg gBound chain w
        by_cases old : g<k+m
        · exact (prior _ (wots_before g (k+m) old (by omega) chain w)).trans
            (oldWots g kg old chain w)
        · have geq : g=k+m := by omega
          subst g
          have sub : k+m-k=m := by omega
          simpa only [sub,←messageEq] using newWots chain w
      · intro g kg gBound level hlevel i
        by_cases old : g<k+m
        · exact (prior _ (sibling_before g (k+m) level old (by omega)
            hlevel i)).trans (oldSiblings g kg old level hlevel i)
        · have geq : g=k+m := by omega
          subst g
          exact newSiblings level hlevel i
      · simp only [Nat.mul_succ]
        omega
      · simp only [Nat.mul_succ]
        omega

theorem all_groups_all (hash : Hash) (secretKey : SecretKey)
    (initialIndex : BitVec 192) (initialBound : initialIndex.toNat<2^150)
    (message : BitVec 128) (start : MachineState)
    (initial : Boundary hash secretKey initialIndex 0 message start) :
    ∃ (n c : Nat) (final : MachineState),
      Executes hash image start n ⟨.success,final,c,119475,127635⟩ ∧
      n ≤ 27135003 ∧ c ≤ 31635003 ∧
      (∀ a : Word, a.toNat<currentWitness 0 →
        final.getMem a=start.getMem a) ∧
      (∀ g, g<45 →
        ∀ chain : GroupedBalancedUpperTree67.ChainMixed, ∀ w : Fin 2,
          final.getMem (slot (currentWitness g) chain w) =
            (GroupedBalancedUpperTree67.signValues hash secretKey
              (treeBase g) (indexAt initialIndex g).toNat
              (messageAfter hash secretKey initialIndex 0 message g)
              chain).extractLsb' (64*w.val) 64) ∧
      (∀ g, g<45 → ∀ level, level<height g → ∀ i : Fin 2,
        final.getMem (BitVec.ofNat 64
          (witnessBase g+16*level+8*i.val))=
          (GroupedBalancedSignUpperTreeModel67.nodeAt hash (treeBase g)
            ((indexAt initialIndex g).toNat/2^height g*2^height g)
            (fun x => GroupedBalancedUpperTree67.leafRoot hash secretKey
              (treeBase g)
              ((indexAt initialIndex g).toNat/2^height g*2^height g+x))
            level
            (Nat.xor (((indexAt initialIndex g).toNat%2^height g)/2^level)
              1)).extractLsb' (64*i.val) 64) := by
  obtain ⟨n,c,currentMessage,middle,path,boundary,messageEq,frame,
    wots,siblings,nBound,cBound⟩ :=
    run_from_all hash secretKey initialIndex initialBound 0 44 (by decide)
      message start initial
  obtain ⟨sn,sc,final,last,snBound,scBound,lastWots,lastSiblings,prior⟩ :=
    GroupedBalancedSignUpperSelectedOuterComplete67.final_group
      hash secretKey initialIndex initialBound currentMessage middle boundary
  have hc : callsFrom 0 44=115492 := by decide
  have hb : blocksFrom 0 44=123380 := by decide
  have whole := path.then_executes last
  refine ⟨n+sn,c+sc,final,?_,by omega,by omega,?_,?_,?_⟩
  · simpa [Execution.charge,hc,hb] using whole
  · intro a ha
    have hmono := current_mono 0 44
    exact (prior a (by simpa using (show a.toNat<currentWitness (0+44)
      by omega))).trans (frame a ha)
  · intro g hg chain w
    by_cases old : g<44
    · have oldWord := wots g (by omega) (by simpa using old) chain w
      have before := wots_before g 44 old (by decide) chain w
      simpa only [Nat.sub_zero] using (prior _ before).trans oldWord
    · have geq : g=44 := by omega
      subst g
      have selected := lastWots chain w
      simpa only [Nat.sub_zero,←messageEq] using selected
  · intro g hg level hlevel i
    by_cases old : g<44
    · have oldWord := siblings g (by omega) (by simpa using old)
        level hlevel i
      exact (prior _ (sibling_before g 44 level old (by decide) hlevel i)).trans
        oldWord
    · have geq : g=44 := by omega
      subst g
      exact lastSiblings level hlevel i

#print axioms run_from_all
#print axioms all_groups_all
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperAllSelected67
