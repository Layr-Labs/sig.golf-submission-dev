import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperWotsSelectedFold67

/-! The selected upper leaf records every WOTS prefix while the endpoint
table is computed. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedPriorFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree GroupedBalancedUpperTree67
open GroupedBalancedSignUpperEndpointAddresses67
open GroupedBalancedSignUpperWitnessSlots67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
noncomputable section
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev witnessSlot := GroupedBalancedSignUpperH2WitnessFrame67.slot
private abbrev digitAddress :=
  GroupedBalancedSignUpperH2WitnessFrame67.digitAddress
private abbrev ChainInv := GroupedBalancedSignUpperChainFold67.Inv
private abbrev h1 := GroupedBalancedSignUpperCost67.h1Prefix
private abbrev h2 := GroupedBalancedSignUpperCost67.h2Prefix

structure Inv (hash : Hash) (secretKey : SecretKey)
    (base leaf witnessBase : Nat) (message : Reference.Digest)
    (start : MachineState) (i : Nat) (s : MachineState) : Prop where
  chain : ChainInv hash secretKey base leaf start i s
  selected : s.getMem 0x810e0=s.getMem 0x810e8
  digits : ∀ j : ChainMixed,
    s.getByte (digitAddress j)=
      BitVec.ofNat 8 (digit message j).val
  witnesses : ∀ j : ChainMixed, j.val < i → ∀ w : Fin 2,
    s.getMem (witnessSlot witnessBase j w)=
      (signValues hash secretKey base leaf message j).extractLsb'
        (64*w.val) 64
  priorFrame : ∀ a : Word, a.toNat<witnessBase →
    s.getMem a=start.getMem a

theorem initial (hash : Hash) (secretKey : SecretKey)
    (base leaf witnessBase : Nat) (message : Reference.Digest)
    (start : MachineState)
    (pc : start.pc=0x1760)
    (counter : start.getMem 0x81030=0)
    (keyWords : ∀ j : Fin 4,
      start.getMem (Signing.wordAddress 0x20 j.val)=
        secretKey.extractLsb' (64*j.val) 64)
    (selected : start.getMem 0x810e0=start.getMem 0x810e8)
    (digits : ∀ j : ChainMixed,
      start.getByte (digitAddress j)=
        BitVec.ofNat 8 (digit message j).val) :
    Inv hash secretKey base leaf witnessBase message start 0 start := by
  refine ⟨GroupedBalancedSignUpperChainFold67.initial hash secretKey
    base leaf start pc counter keyWords,selected,digits,?_,?_⟩
  · intro j hj
    omega
  · intro a low
    rfl

theorem one_step (hash : Hash) (secretKey : SecretKey)
    (base leaf witnessBase i : Nat) (message : Reference.Digest)
    (start s : MachineState)
    (hi : i<67)
    (inv : Inv hash secretKey base leaf witnessBase message start i s)
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
      Inv hash secretKey base leaf witnessBase message start (i+1) next ∧
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
    seedCache,seedHigh,seedMiddle,seedLow,seedDigitFrame⟩ :=
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
  have selectedSeed : seeded.getMem 0x810e0=seeded.getMem 0x810e8 := by
    rw [seedHigh 0x810e0 (by decide),
      seedHigh 0x810e8 (by decide)]
    exact inv.selected
  have digitSeed : seeded.getByte (digitAddress chain)=
      BitVec.ofNat 8 (digit message chain).val := by
    rw [digit_region_frame s seeded chain seedDigitFrame]
    exact inv.digits chain
  obtain ⟨hn,hc,next,h2Trace,nextPc,nextWitness,nextCounter,
    nextWords,nextSp,h2Frame,h2LowFrame,hnBound,hcBound⟩ :=
    GroupedBalancedSignUpperH2SelectedChain67.selected_chain hash seeded
      base leaf witnessBase chain (secret hash secretKey base leaf chain)
      (digit message chain).val seedEntry baseBound witnessLower
      (by have := hi; omega) aligned selectedSeed digitSeed
      (GroupedBalancedChecksum67.digit_le_max message chain)
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
  have nextEndpoints : ∀ (j : ChainMixed), j.val < i+1 → ∀ (w : Fin 2),
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
  have nextKeyWords : ∀ w : Fin 4,
      next.getMem (Signing.wordAddress 0x20 w.val)=
        secretKey.extractLsb' (64*w.val) 64 := by
    intro w
    let a := Signing.wordAddress 0x20 w.val
    have low : a.toNat<0x100 := by fin_cases w <;> decide
    have outside (j : Fin 2) : a≠witnessSlot witnessBase chain j := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      have bound : 0x20060≤
          (witnessSlot witnessBase chain j).toNat :=
        (slot_bound witnessBase chain j witnessLower witnessBound).1
      omega
    rw [h2LowFrame a (by omega) (outside 0) (outside 1),
      seedLow a (by omega)]
    exact inv.chain.keyWords w
  have nextLowWords : ∀ a : Word, a.toNat<0x100 →
      next.getMem a=start.getMem a := by
    intro a low
    have outside (j : Fin 2) : a≠witnessSlot witnessBase chain j := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      have bound : 0x20060≤
          (witnessSlot witnessBase chain j).toNat :=
        (slot_bound witnessBase chain j witnessLower witnessBound).1
      omega
    rw [h2LowFrame a (by omega) (outside 0) (outside 1),
      seedLow a (by omega),inv.chain.lowWords a low]
  have nextChain : ChainInv hash secretKey base leaf start (i+1) next := by
    refine ⟨?_,?_,?_,nextKeyWords,nextLowWords,?_,nextEndpoints,
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
  have nextSelected : next.getMem 0x810e0=next.getMem 0x810e8 := by
    have e0 := h2Frame 0x810e0 (by decide) (by decide) (by decide)
      (high_ne_slot 0x810e0 i hi (by decide) 0)
      (high_ne_slot 0x810e0 i hi (by decide) 1)
    have e8 := h2Frame 0x810e8 (by decide) (by decide) (by decide)
      (high_ne_slot 0x810e8 i hi (by decide) 0)
      (high_ne_slot 0x810e8 i hi (by decide) 1)
    rw [e0,e8]
    exact selectedSeed
  have nextDigits : ∀ j : ChainMixed,
      next.getByte (digitAddress j)=
        BitVec.ofNat 8 (digit message j).val := by
    intro j
    rw [digit_frame seeded next chain j h2Frame,
      digit_region_frame s seeded j seedDigitFrame]
    exact inv.digits j
  have nextWitnesses : ∀ j : ChainMixed, j.val < i+1 → ∀ w : Fin 2,
      next.getMem (witnessSlot witnessBase j w)=
        (signValues hash secretKey base leaf message j).extractLsb'
          (64*w.val) 64 := by
    intro j hj w
    by_cases same : j.val=i
    · have chainEq : j=chain := Fin.ext same
      subst j
      simpa only [signValues] using nextWitness w
    · have prior : j.val < i := by omega
      rw [prior_frame seeded next witnessBase chain j w witnessLower
        witnessBound prior h2LowFrame,
        seedLow _ (slot_bound witnessBase j w witnessLower
          witnessBound).2]
      exact inv.witnesses j prior w
  refine ⟨(if i%2=0 then 127 else 26)+hn,
    (if i%2=0 then 134 else 26)+hc,next,?_,
      ⟨nextChain,nextSelected,nextDigits,nextWitnesses,?_⟩,
      by split_ifs <;> omega,by split_ifs <;> omega⟩
  · simpa [chain,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      seedTrace.trans h2Trace
  · intro a low
    have outside (j : Fin 2) : a≠witnessSlot witnessBase chain j := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      have bound : witnessBase≤
          (witnessSlot witnessBase chain j).toNat := by
        have slot := slot_bound witnessBase chain j witnessLower witnessBound
        have slotNat := GroupedBalancedSignUpperH2WitnessFrame67.slot_nat
          witnessBase chain j (by have := hi; omega)
        rw [slotNat]
        omega
      omega
    rw [h2LowFrame a (by omega) (outside 0) (outside 1),
      seedLow a (by omega)]
    exact inv.priorFrame a low


theorem run_prefix (hash : Hash) (secretKey : SecretKey)
    (base leaf witnessBase : Nat) (message : Reference.Digest)
    (start : MachineState)
    (baseBound : base<256)
    (level : start.getMem 0x81000=BitVec.ofNat 64 base)
    (address : ∀ w : Fin 3,
      start.getMem (Signing.wordAddress 0x81008 w.val)=
        (BitVec.ofNat 192 leaf).extractLsb' (64*w.val) 64)
    (witness : start.getMem 0x810f0=BitVec.ofNat 64 witnessBase)
    (witnessLower : 0x20060≤witnessBase)
    (witnessBound : witnessBase+16*67≤0x80000)
    (aligned : witnessBase%8=0)
    (initial : Inv hash secretKey base leaf witnessBase message
      start 0 start) :
    ∀ i : Nat, i≤67 →
      ∃ (n c : Nat) (final : MachineState),
        Trace hash image start n c (h1 i+h2 i) (h1 i+h2 i) final ∧
        Inv hash secretKey base leaf witnessBase message start i final ∧
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
        one_step hash secretKey base leaf witnessBase i message start mid
          (by omega) midInv baseBound level address witness
          witnessLower witnessBound aligned
      refine ⟨n+sn,c+sc,final,?_,finalInv,by omega,by omega⟩
      have both := pretrace.trans step
      simpa only [h1,h2,GroupedBalancedSignUpperCost67.h1_succ,
        GroupedBalancedSignUpperCost67.h2_succ i (by omega),
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using both

theorem run_all_copy (hash : Hash) (secretKey : SecretKey)
    (base leaf witnessBase : Nat) (message : Reference.Digest)
    (start : MachineState)
    (baseBound : base<256)
    (level : start.getMem 0x81000=BitVec.ofNat 64 base)
    (address : ∀ w : Fin 3,
      start.getMem (Signing.wordAddress 0x81008 w.val)=
        (BitVec.ofNat 192 leaf).extractLsb' (64*w.val) 64)
    (witness : start.getMem 0x810f0=BitVec.ofNat 64 witnessBase)
    (witnessLower : 0x20060≤witnessBase)
    (witnessBound : witnessBase+16*67≤0x80000)
    (aligned : witnessBase%8=0)
    (initial : Inv hash secretKey base leaf witnessBase message
      start 0 start) :
    ∃ (n c : Nat) (ready : MachineState),
      Trace hash image start n c 247 247 ready ∧
      ready.pc=0x1b28 ∧
      (∀ j : ChainMixed, ∀ w : Fin 2,
        ready.getMem (witnessSlot witnessBase j w)=
          (signValues hash secretKey base leaf message j).extractLsb'
            (64*w.val) 64) ∧
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
      (∀ a : Word, a.toNat<0x100 →
        ready.getMem a=start.getMem a) ∧
      (∀ a : Word, a.toNat<witnessBase →
        ready.getMem a=start.getMem a) ∧
      n ≤ 36118 ∧ c ≤ 41277 := by
  obtain ⟨n,c,table,path,inv,nBound,cBound⟩ :=
    run_prefix hash secretKey base leaf witnessBase message start
      baseBound level address witness witnessLower witnessBound aligned
      initial 67 (by omega)
  have calls : h1 67+h2 67=247 :=
    GroupedBalancedSignUpperCost67.total
  have tablePc : table.pc=0x1afc := by simpa using inv.chain.pc
  obtain ⟨ready,copy,readyPc,copyWords,copyFrame,copySp⟩ :=
    GroupedBalancedSignUpperEndpointCopy67.copy_all table tablePc
  have full : Trace hash image start (n+809) (c+809) 247 247 ready := by
    simpa [calls] using path.trans
      (copy.trace (hash := hash))
  refine ⟨n+809,c+809,ready,full,readyPc,?_,?_,?_,?_,?_,?_,?_,
    by omega,by omega⟩
  · intro j w
    rw [copy_frame table ready witnessBase j w witnessLower
      witnessBound copyFrame]
    exact inv.witnesses j j.isLt w
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
    have outside : ∀ i, i<134 →
        a≠Signing.wordAddress 0x80020 i := by
      intro i hi eq
      have hn := congrArg BitVec.toNat eq
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80020+8*i<2^64)] at hn
      omega
    rw [copyFrame a outside]
    exact inv.chain.controls a high ne30 ne38
  · rw [copySp,inv.chain.stack]
  · intro w
    have outside : ∀ i, i<134 →
        Signing.wordAddress 0x20 w.val≠Signing.wordAddress 0x80020 i := by
      intro i hi eq
      have hn := congrArg BitVec.toNat eq
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x20+8*w.val<2^64),
        Nat.mod_eq_of_lt (by omega : 0x80020+8*i<2^64)] at hn
      have := w.isLt
      omega
    rw [copyFrame _ outside]
    exact inv.chain.keyWords w
  · intro a low
    have outside : ∀ i, i<134 →
        a≠Signing.wordAddress 0x80020 i := by
      intro i hi eq
      have hn := congrArg BitVec.toNat eq
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80020+8*i<2^64)] at hn
      omega
    rw [copyFrame a outside]
    exact inv.chain.lowWords a low

  · intro a low
    have outside : ∀ i, i<134 →
        a≠Signing.wordAddress 0x80020 i := by
      intro i hi eq
      have hn := congrArg BitVec.toNat eq
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80020+8*i<2^64)] at hn
      omega
    rw [copyFrame a outside]
    exact inv.priorFrame a low

#print axioms run_all_copy
end
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedPriorFrame67
