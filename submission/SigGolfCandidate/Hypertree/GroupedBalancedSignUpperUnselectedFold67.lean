import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperUnselectedChain67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperChainFold67

/-! All WOTS chains of an unselected upper leaf preserve the signature
buffer below 0x80000. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperUnselectedFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree GroupedBalancedUpperTree67
open GroupedBalancedSignUpperEndpointAddresses67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
noncomputable section
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev h1 := GroupedBalancedSignUpperCost67.h1Prefix
private abbrev h2 := GroupedBalancedSignUpperCost67.h2Prefix
private abbrev ChainInv := GroupedBalancedSignUpperChainFold67.Inv

structure Inv (hash : Hash) (secretKey : SecretKey)
    (base leaf : Nat) (start : MachineState) (i : Nat)
    (s : MachineState) : Prop where
  chain : ChainInv hash secretKey base leaf start i s
  unselected : s.getMem 0x810e0≠s.getMem 0x810e8
  lowFrame : ∀ a : Word, a.toNat<0x80000 →
    s.getMem a=start.getMem a
  digitFrame : ∀ a : Word, 0x80600≤a.toNat → a.toNat<0x80800 →
    s.getMem a=start.getMem a

theorem initial (hash : Hash) (secretKey : SecretKey)
    (base leaf : Nat) (start : MachineState)
    (pc : start.pc=0x1760)
    (counter : start.getMem 0x81030=0)
    (keyWords : ∀ j : Fin 4,
      start.getMem (Signing.wordAddress 0x20 j.val)=
        secretKey.extractLsb' (64*j.val) 64)
    (unselected : start.getMem 0x810e0≠start.getMem 0x810e8) :
    Inv hash secretKey base leaf start 0 start := by
  refine ⟨GroupedBalancedSignUpperChainFold67.initial hash secretKey
    base leaf start pc counter keyWords,unselected,?_,?_⟩
  · intros; rfl
  · intros; rfl

theorem one_step (hash : Hash) (secretKey : SecretKey)
    (base leaf witnessBase i : Nat) (start s : MachineState)
    (hi : i<67)
    (inv : Inv hash secretKey base leaf start i s)
    (baseBound : base<256)
    (level : start.getMem 0x81000=BitVec.ofNat 64 base)
    (address : ∀ w : Fin 3,
      start.getMem (Signing.wordAddress 0x81008 w.val)=
        (BitVec.ofNat 192 leaf).extractLsb' (64*w.val) 64)
    (witness : start.getMem 0x810f0=BitVec.ofNat 64 witnessBase)
    (witnessLower : 0x20060≤witnessBase)
    (witnessBound : witnessBase+16*67≤0x80000)
    (aligned : witnessBase%8=0) :
    ∃ (n c : Nat) (next : MachineState),
      Trace hash image s n c
        ((if i%2=0 then 1 else 0)+
          maxDigit (⟨i,hi⟩ : ChainMixed))
        ((if i%2=0 then 1 else 0)+
          maxDigit (⟨i,hi⟩ : ChainMixed)) next ∧
      Inv hash secretKey base leaf start (i+1) next ∧
      n ≤ 527 ∧ c ≤ 604 := by
  let chain : ChainMixed := ⟨i,hi⟩
  have spc : s.pc=0x1760 := by simpa [hi] using inv.chain.pc
  have slevel : s.getMem 0x81000=BitVec.ofNat 64 base := by
    rw [inv.chain.controls 0x81000 (by decide) (by decide) (by decide)]
    exact level
  have saddr : ∀ w : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 w.val)=
        (BitVec.ofNat 192 leaf).extractLsb' (64*w.val) 64 := by
    intro w
    rw [inv.chain.controls _ (by fin_cases w <;> decide)
      (by fin_cases w <;> decide) (by fin_cases w <;> decide)]
    exact address w
  obtain ⟨seeded,seedTrace,seedPc,seedX19,seedSp,seedWords,
    seedCache,seedHigh,seedMiddle,seedLow,seedDigit⟩ :=
    GroupedBalancedSignUpperSeedData67.seed hash secretKey base leaf chain
      s spc inv.chain.counter slevel saddr inv.chain.keyWords
      inv.chain.cache
  have seedCounter : seeded.getMem 0x81030=BitVec.ofNat 64 i := by
    rw [seedHigh 0x81030 (by decide),inv.chain.counter]
  have seedEntry : GroupedBalancedSignUpperH2StartData67.Entry seeded
      base leaf witnessBase chain (secret hash secretKey base leaf chain) := by
    refine ⟨seedPc,?_,?_,?_,?_,?_,?_⟩
    · rw [seedHigh 0x81000 (by decide),slevel]
    · intro w
      rw [seedHigh _ (by fin_cases w <;> decide)]
      exact saddr w
    · exact seedCounter
    · exact seedX19
    · rw [seedHigh 0x810f0 (by decide),
        inv.chain.controls 0x810f0 (by decide) (by decide) (by decide)]
      exact witness
    · exact seedWords
  have unselectedSeed : seeded.getMem 0x810e0≠
      seeded.getMem 0x810e8 := by
    rw [seedHigh 0x810e0 (by decide),
      seedHigh 0x810e8 (by decide)]
    exact inv.unselected
  obtain ⟨hn,hc,next,h2Trace,nextPc,nextCounter,nextWords,
    nextSp,nextUnselected,h2Frame,h2LowFrame,hnBound,hcBound⟩ :=
    GroupedBalancedSignUpperUnselectedChain67.one_chain hash seeded
      base leaf witnessBase chain (secret hash secretKey base leaf chain)
      seedEntry unselectedSeed baseBound witnessLower
      (by have := hi; omega) aligned
  have nextCache (w : Fin 2) :
      next.getMem (Signing.wordAddress 0x80d10 w.val) =
        (secretPair hash secretKey base leaf (i/2)).extractLsb'
          (128+64*w.val) 64 := by
    have hHigh : 0x80600≤
        (Signing.wordAddress 0x80d10 w.val).toNat := by
      fin_cases w <;> decide
    have hStep : Signing.wordAddress 0x80d10 w.val≠0x81038 := by
      fin_cases w <;> decide
    have hCounter : Signing.wordAddress 0x80d10 w.val≠0x81030 := by
      fin_cases w <;> decide
    rw [h2Frame (Signing.wordAddress 0x80d10 w.val) hHigh hStep
      hCounter (cache_ne_slot i hi w (0 : Fin 2))
      (cache_ne_slot i hi w (1 : Fin 2))]
    exact seedCache w
  have nextControls : ∀ a : Word, 0x81000≤a.toNat →
      a≠0x81030 → a≠0x81038 → next.getMem a=start.getMem a := by
    intro a high ne30 ne38
    rw [h2Frame a (by omega) ne38 ne30
      (high_ne_slot a i hi high 0)
      (high_ne_slot a i hi high 1),seedHigh a high,
      inv.chain.controls a high ne30 ne38]
  have nextEndpoints : ∀ (j : ChainMixed), j.val < i+1 →
      ∀ (w : Fin 2),
      next.getMem (Signing.wordAddress (0x80800+16*j.val) w.val) =
        (endpoint hash secretKey base leaf j).extractLsb'
          (64*w.val) 64 := by
    intro j hj w
    have jBound := j.isLt
    by_cases same : j.val=i
    · have chainEq : j=chain := Fin.ext same
      subst j
      rw [nextWords w]
      rfl
    · have prior : j.val < i := by omega
      let a := Signing.wordAddress (0x80800+16*j.val) w.val
      have frame := h2Frame a (slot_high j.val jBound w)
        (slot_ne_step j.val jBound w) (slot_ne_counter j.val jBound w)
        (slot_ne j.val i jBound hi same w 0)
        (slot_ne j.val i jBound hi same w 1)
      rw [frame,seedMiddle a (by rw [slot_nat j.val jBound w]; omega)
        (slot_before_cache j.val jBound w)]
      exact inv.chain.endpoints j prior w
  have nextLowAll : ∀ a : Word, a.toNat<0x80000 →
      next.getMem a=start.getMem a := by
    intro a low
    rw [h2LowFrame a low,seedLow a low,inv.lowFrame a low]
  have nextDigits : ∀ a : Word, 0x80600≤a.toNat →
      a.toNat<0x80800 → next.getMem a=start.getMem a := by
    intro a low high
    have ne38 : a≠0x81038 := by
      intro eq; subst a
      have numeric : (0x81038 : Word).toNat=0x81038 := by decide
      rw [numeric] at high
      omega
    have ne30 : a≠0x81030 := by
      intro eq; subst a
      have numeric : (0x81030 : Word).toNat=0x81030 := by decide
      rw [numeric] at high
      omega
    have neSlot (w : Fin 2) :
        a≠Signing.wordAddress (0x80800+16*i) w.val := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      rw [slot_nat i hi w] at hn
      omega
    rw [h2Frame a low ne38 ne30 (neSlot 0) (neSlot 1),
      seedDigit a low high,inv.digitFrame a low high]
  have nextKey : ∀ w : Fin 4,
      next.getMem (Signing.wordAddress 0x20 w.val)=
        secretKey.extractLsb' (64*w.val) 64 := by
    intro w
    let a := Signing.wordAddress 0x20 w.val
    have low : a.toNat<0x80000 := by fin_cases w <;> decide
    rw [h2LowFrame a low,seedLow a low]
    exact inv.chain.keyWords w
  have nextLowWords : ∀ a : Word, a.toNat<0x100 →
      next.getMem a=start.getMem a := by
    intro a low
    exact nextLowAll a (by omega)
  have nextChain : ChainInv hash secretKey base leaf start (i+1) next := by
    refine ⟨?_,?_,?_,nextKey,nextLowWords,?_,nextEndpoints,
      nextControls⟩
    · change next.pc = (if i+1<67 then 0x1760 else 0x1afc)
      change next.pc = (if i+1=67 then 0x1afc else 0x1760) at nextPc
      rw [nextPc]
      by_cases last : i+1=67
      · simp [last]
      · have lt : i+1<67 := by omega
        simp [lt,last]
    · simpa [chain] using nextCounter
    · rw [nextSp,seedSp,inv.chain.stack]
    · intro parity w
      have even : i%2=0 := by omega
      have divEq : (i+1)/2=i/2 := by omega
      rw [divEq]
      exact nextCache w
  refine ⟨(if i%2=0 then 127 else 26)+hn,
    (if i%2=0 then 134 else 26)+hc,next,?_,
      ⟨nextChain,nextUnselected,nextLowAll,nextDigits⟩,
      by split_ifs <;> omega,by split_ifs <;> omega⟩
  simpa [chain,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    seedTrace.trans h2Trace

theorem run_prefix (hash : Hash) (secretKey : SecretKey)
    (base leaf witnessBase : Nat) (start : MachineState)
    (baseBound : base<256)
    (level : start.getMem 0x81000=BitVec.ofNat 64 base)
    (address : ∀ w : Fin 3,
      start.getMem (Signing.wordAddress 0x81008 w.val)=
        (BitVec.ofNat 192 leaf).extractLsb' (64*w.val) 64)
    (witness : start.getMem 0x810f0=BitVec.ofNat 64 witnessBase)
    (witnessLower : 0x20060≤witnessBase)
    (witnessBound : witnessBase+16*67≤0x80000)
    (aligned : witnessBase%8=0)
    (initial : Inv hash secretKey base leaf start 0 start) :
    ∀ i : Nat, i≤67 →
      ∃ (n c : Nat) (final : MachineState),
        Trace hash image start n c (h1 i+h2 i) (h1 i+h2 i) final ∧
        Inv hash secretKey base leaf start i final ∧
        n ≤ 527*i ∧ c ≤ 604*i := by
  intro i hi
  induction i with
  | zero =>
      exact ⟨0,0,start,by simpa [h1,h2,
        GroupedBalancedSignUpperCost67.h1Prefix,
        GroupedBalancedSignUpperCost67.h2Prefix] using
        (Trace.refl (hash := hash) (image := image) start),initial,
        by omega,by omega⟩
  | succ i ih =>
      obtain ⟨n,c,mid,pretrace,midInv,nBound,cBound⟩ := ih (by omega)
      obtain ⟨sn,sc,final,step,finalInv,snBound,scBound⟩ :=
        one_step hash secretKey base leaf witnessBase i start mid
          (by omega) midInv baseBound level address witness
          witnessLower witnessBound aligned
      refine ⟨n+sn,c+sc,final,?_,finalInv,by omega,by omega⟩
      have both := pretrace.trans step
      simpa only [h1,h2,GroupedBalancedSignUpperCost67.h1_succ,
        GroupedBalancedSignUpperCost67.h2_succ i (by omega),
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using both

theorem run_all_copy (hash : Hash) (secretKey : SecretKey)
    (base leaf witnessBase : Nat) (start : MachineState)
    (baseBound : base<256)
    (level : start.getMem 0x81000=BitVec.ofNat 64 base)
    (address : ∀ w : Fin 3,
      start.getMem (Signing.wordAddress 0x81008 w.val)=
        (BitVec.ofNat 192 leaf).extractLsb' (64*w.val) 64)
    (witness : start.getMem 0x810f0=BitVec.ofNat 64 witnessBase)
    (witnessLower : 0x20060≤witnessBase)
    (witnessBound : witnessBase+16*67≤0x80000)
    (aligned : witnessBase%8=0)
    (initial : Inv hash secretKey base leaf start 0 start) :
    ∃ (n c : Nat) (ready : MachineState),
      Trace hash image start n c 247 247 ready ∧
      ready.pc=0x1b28 ∧
      ready.getMem 0x810e0≠ready.getMem 0x810e8 ∧
      (∀ j : Fin 134,
        ready.getMem (Signing.wordAddress 0x80020 j.val)=
          (endpoint hash secretKey base leaf
            ⟨j.val/2,by have := j.isLt; omega⟩).extractLsb'
              (64*(j.val%2)) 64) ∧
      (∀ a : Word, 0x81000≤a.toNat → a≠0x81030 → a≠0x81038 →
        ready.getMem a=start.getMem a) ∧
      ready.getReg .x2=start.getReg .x2 ∧
      (∀ w : Fin 4,
        ready.getMem (Signing.wordAddress 0x20 w.val)=
          secretKey.extractLsb' (64*w.val) 64) ∧
      (∀ a : Word, a.toNat<0x80000 →
        ready.getMem a=start.getMem a) ∧
      (∀ a : Word, 0x80600≤a.toNat → a.toNat<0x80800 →
        ready.getMem a=start.getMem a) ∧
      n ≤ 36118 ∧ c ≤ 41277 := by
  obtain ⟨n,c,table,path,inv,nBound,cBound⟩ :=
    run_prefix hash secretKey base leaf witnessBase start baseBound
      level address witness witnessLower witnessBound aligned initial
      67 (by omega)
  have calls : h1 67+h2 67=247 :=
    GroupedBalancedSignUpperCost67.total
  have tablePc : table.pc=0x1afc := by simpa using inv.chain.pc
  obtain ⟨ready,copy,readyPc,copyWords,copyFrame,copySp⟩ :=
    GroupedBalancedSignUpperEndpointCopy67.copy_all table tablePc
  have full : Trace hash image start (n+809) (c+809) 247 247 ready := by
    simpa [calls] using path.trans
      (copy.trace (hash := hash))
  have copyLow (a : Word) (low : a.toNat<0x80000) :
      ready.getMem a=table.getMem a := by
    apply copyFrame a
    intro i hi eq
    have hn := congrArg BitVec.toNat eq
    simp only [Signing.wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80020+8*i<2^64)] at hn
    omega
  have copyHigh (a : Word) (high : 0x81000≤a.toNat) :
      ready.getMem a=table.getMem a := by
    apply copyFrame a
    intro i hi eq
    have hn := congrArg BitVec.toNat eq
    simp only [Signing.wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80020+8*i<2^64)] at hn
    omega
  have copyDigits (a : Word) (low : 0x80600≤a.toNat) :
      ready.getMem a=table.getMem a := by
    apply copyFrame a
    intro i hi eq
    have hn := congrArg BitVec.toNat eq
    simp only [Signing.wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80020+8*i<2^64)] at hn
    omega
  refine ⟨n+809,c+809,ready,full,readyPc,?_,?_,?_,?_,?_,?_,?_,
    by omega,by omega⟩
  · rw [copyHigh 0x810e0 (by decide),
      copyHigh 0x810e8 (by decide)]
    exact inv.unselected
  · intro j
    let ch : ChainMixed := ⟨j.val/2,by have := j.isLt; omega⟩
    let w : Fin 2 := ⟨j.val%2,by omega⟩
    have jEq : 2*ch.val+w.val=j.val := by
      dsimp [ch,w]
      omega
    have addressEq : Signing.wordAddress (0x80800+16*ch.val) w.val =
        Signing.wordAddress 0x80800 j.val := by
      rw [slot_eq_flat ch.val w,jEq]
    rw [copyWords j.val j.isLt,←addressEq]
    exact inv.chain.endpoints ch ch.isLt w
  · intro a high ne30 ne38
    rw [copyHigh a high]
    exact inv.chain.controls a high ne30 ne38
  · rw [copySp,inv.chain.stack]
  · intro w
    have low : (Signing.wordAddress 0x20 w.val).toNat<0x80000 := by
      fin_cases w <;> decide
    rw [copyLow _ low]
    exact inv.chain.keyWords w
  · intro a low
    rw [copyLow a low]
    exact inv.lowFrame a low
  · intro a low high
    rw [copyDigits a low]
    exact inv.digitFrame a low high

#print axioms one_step
#print axioms run_all_copy
end
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperUnselectedFold67
