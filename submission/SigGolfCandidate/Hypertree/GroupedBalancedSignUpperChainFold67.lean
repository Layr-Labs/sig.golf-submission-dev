import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2OneChain67
import SigGolfCandidate.Hypertree.KeygenCopyX2X19
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperEndpointAddresses67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperEndpointCopy67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperChainFold67. -/
section
/-! Copy all 134 WOTS endpoint words into the H3 leaf input. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperEndpointCopy67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def setupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x81)
  let s := execInstrBr s (.ADDI .x6 .x6 0x800)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x20)
  execInstrBr s (.ADDI .x10 .x0 134)

private theorem setup_code :
    Keygen.instructionAt image 0x1afc = some (.base (.LUI .x6 0x81)) ∧
    Keygen.instructionAt image 0x1b00 = some (.base (.ADDI .x6 .x6 0x800)) ∧
    Keygen.instructionAt image 0x1b04 = some (.base (.LUI .x7 0x80)) ∧
    Keygen.instructionAt image 0x1b08 = some (.base (.ADDI .x7 .x7 0x20)) ∧
    Keygen.instructionAt image 0x1b0c = some (.base (.ADDI .x10 .x0 134)) := by
  decide

theorem setup_steps (s : MachineState) (pc : s.pc = 0x1afc) :
    OrdinarySteps image s 5 (setupState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x81)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x800)
  let s3 := execInstrBr s2 (.LUI .x7 0x80)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0x20)
  obtain ⟨c0,c1,c2,c3,c4⟩ := setup_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x81)) 4
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x800)) 3
  · simpa [Keygen.fetch_at,s1,execInstrBr,pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x80)) 2
  · simpa [Keygen.fetch_at,s1,s2,execInstrBr,pc] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0x20)) 1
  · simpa [Keygen.fetch_at,s1,s2,s3,execInstrBr,pc] using c3
  · rfl
  apply OrdinarySteps.step s4 (setupState s) _ (.base (.ADDI .x10 .x0 134)) 0
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,execInstrBr,pc] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem copy_code : Keygen.CopyCode image 0x1b10 := by decide

theorem copy_inv (s : MachineState) (pc : s.pc = 0x1afc) :
    Keygen.CopyInvariant 0x1b10 0x80800 0x80020 134 134 (setupState s) := by
  unfold Keygen.CopyInvariant setupState
  simp [execInstrBr,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,signExtend12,pc]

theorem copy_all (s : MachineState) (pc : s.pc = 0x1afc) :
    ∃ final, OrdinarySteps image s 809 final ∧ final.pc = 0x1b28 ∧
      (∀ i, i < 134 → final.getMem (Signing.wordAddress 0x80020 i) =
        s.getMem (Signing.wordAddress 0x80800 i)) ∧
      (∀ a, (∀ i, i < 134 → a ≠ Signing.wordAddress 0x80020 i) →
        final.getMem a = s.getMem a) ∧
      final.getReg .x2 = s.getReg .x2 := by
  let begun := setupState s
  obtain ⟨final,loop,done,words,frame,x19,sp⟩ :=
    KeygenCopyX2X19.copy_all_x19_x2 image 0x1b10 copy_code
      0x80800 0x80020 134 begun (copy_inv s pc)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final,?_,done.2.2.1,?_,?_,?_⟩
  · have full := Keygen.ordinary_trans image s begun final 5 804
      (setup_steps s pc) loop
    simpa only [show 804+5=809 by decide] using full
  · intro i hi
    rw [words i hi]
    simp [begun,setupState,execInstrBr]
  · intro a outside
    rw [frame a outside]
    simp [begun,setupState,execInstrBr]
  · rw [sp]
    simp [begun,setupState,execInstrBr,MachineState.getReg_setReg_ne]

#print axioms copy_all
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperEndpointCopy67

end

/-! Iterate every upper WOTS chain while retaining the endpoint table. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperChainFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree GroupedBalancedUpperTree67
open GroupedBalancedSignUpperEndpointAddresses67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
noncomputable section
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev h1 := GroupedBalancedSignUpperCost67.h1Prefix
private abbrev h2 := GroupedBalancedSignUpperCost67.h2Prefix

structure Inv (hash : Hash) (secretKey : SecretKey)
    (base leaf : Nat) (start : MachineState) (i : Nat)
    (s : MachineState) : Prop where
  pc : s.pc = if i<67 then 0x1760 else 0x1afc
  counter : s.getMem 0x81030 = BitVec.ofNat 64 i
  stack : s.getReg .x2 = start.getReg .x2
  keyWords : ∀ j : Fin 4,
    s.getMem (Signing.wordAddress 0x20 j.val) =
      secretKey.extractLsb' (64*j.val) 64
  lowWords : ∀ a : Word, a.toNat < 0x100 →
    s.getMem a=start.getMem a
  cache : i%2=1 → ∀ w : Fin 2,
    s.getMem (Signing.wordAddress 0x80d10 w.val) =
      (secretPair hash secretKey base leaf (i/2)).extractLsb'
        (128+64*w.val) 64
  endpoints : ∀ (j : ChainMixed), j.val < i → ∀ (w : Fin 2),
    s.getMem (Signing.wordAddress (0x80800+16*j.val) w.val) =
      (endpoint hash secretKey base leaf j).extractLsb'
        (64*w.val) 64
  controls : ∀ a : Word, 0x81000 ≤ a.toNat → a≠0x81030 →
    a≠0x81038 → s.getMem a=start.getMem a

theorem initial (hash : Hash) (secretKey : SecretKey)
    (base leaf : Nat) (start : MachineState)
    (pc : start.pc=0x1760)
    (counter : start.getMem 0x81030=0)
    (keyWords : ∀ j : Fin 4,
      start.getMem (Signing.wordAddress 0x20 j.val)=
        secretKey.extractLsb' (64*j.val) 64) :
    Inv hash secretKey base leaf start 0 start := by
  refine ⟨by simpa using pc,by simpa using counter,rfl,
    keyWords,?_,?_,?_,?_⟩
  · intros
    rfl
  · intro h
    omega
  · intro j hj
    omega
  · intros
    rfl

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
  have spc : s.pc=0x1760 := by simpa [hi] using inv.pc
  have slevel : s.getMem 0x81000=BitVec.ofNat 64 base := by
    rw [inv.controls 0x81000 (by decide) (by decide) (by decide)]
    exact level
  have saddr : ∀ w : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 w.val)=
        (BitVec.ofNat 192 leaf).extractLsb' (64*w.val) 64 := by
    intro w
    rw [inv.controls _ (by fin_cases w <;> decide)
      (by fin_cases w <;> decide) (by fin_cases w <;> decide)]
    exact address w
  obtain ⟨seeded,seedTrace,seedPc,seedX19,seedSp,seedWords,
    seedCache,seedHigh,seedMiddle,seedLow,_seedDigitFrame⟩ :=
    GroupedBalancedSignUpperSeedData67.seed hash secretKey base leaf chain
      s spc inv.counter slevel saddr inv.keyWords inv.cache
  have seedCounter : seeded.getMem 0x81030=BitVec.ofNat 64 i := by
    rw [seedHigh 0x81030 (by decide),inv.counter]
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
        inv.controls 0x810f0 (by decide) (by decide) (by decide)]
      exact witness
    · exact seedWords
  obtain ⟨hn,hc,next,h2Trace,nextPc,nextCounter,nextWords,nextSp,
    nextKey,h2Frame,h2LowFrame,hnBound,hcBound⟩ :=
    GroupedBalancedSignUpperH2OneChain67.one_chain hash seeded base leaf
      witnessBase chain (secret hash secretKey base leaf chain) seedEntry
      baseBound witnessLower (by have := hi; omega) aligned
  have nextCache (w : Fin 2) :
      next.getMem (Signing.wordAddress 0x80d10 w.val) =
        (secretPair hash secretKey base leaf (i/2)).extractLsb'
          (128+64*w.val) 64 := by
    have hHigh : 0x80600 ≤
        (Signing.wordAddress 0x80d10 w.val).toNat := by
      fin_cases w <;> decide
    have hStep : Signing.wordAddress 0x80d10 w.val≠0x81038 := by
      fin_cases w <;> decide
    have hCounter : Signing.wordAddress 0x80d10 w.val≠0x81030 := by
      fin_cases w <;> decide
    rw [h2Frame (Signing.wordAddress 0x80d10 w.val) hHigh hStep hCounter
      (cache_ne_slot i hi w (0 : Fin 2))
      (cache_ne_slot i hi w (1 : Fin 2))]
    exact seedCache w
  have nextControls : ∀ a : Word, 0x81000 ≤ a.toNat →
      a≠0x81030 → a≠0x81038 → next.getMem a=start.getMem a := by
    intro a high ne30 ne38
    rw [h2Frame a (by omega) ne38 ne30
      (high_ne_slot a i hi high 0)
      (high_ne_slot a i hi high 1),seedHigh a high,
      inv.controls a high ne30 ne38]
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
      exact inv.endpoints j prior w
  have nextKeyWords : ∀ w : Fin 4,
      next.getMem (Signing.wordAddress 0x20 w.val)=
        secretKey.extractLsb' (64*w.val) 64 := by
    intro w
    rw [nextKey w,seedLow _ (by fin_cases w <;> decide)]
    exact inv.keyWords w
  have nextLowWords : ∀ a : Word, a.toNat<0x100 →
      next.getMem a=start.getMem a := by
    intro a low
    have noWitness (w : Fin 2) :
        a≠Signing.wordAddress (witnessBase+16*i) w.val := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      have small : witnessBase+16*i+8*w.val<2^64 := by
        have := w.isLt
        omega
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt small] at hn
      omega
    rw [h2LowFrame a (by omega) (noWitness 0) (noWitness 1),
      seedLow a (by omega),inv.lowWords a low]
  have nextInv : Inv hash secretKey base leaf start (i+1) next := by
    refine ⟨?_,?_,?_,nextKeyWords,nextLowWords,?_,nextEndpoints,
      nextControls⟩
    · change next.pc = (if i+1<67 then 0x1760 else 0x1afc)
      change next.pc = (if i+1=67 then 0x1afc else 0x1760) at nextPc
      rw [nextPc]
      by_cases last : i+1=67
      · have notLt : ¬ i+1<67 := by omega
        simp [last,notLt]
      · have lt : i+1<67 := by omega
        simp [lt,last]
    · simpa [chain] using nextCounter
    · rw [nextSp,seedSp,inv.stack]
    · intro parity w
      have even : i%2=0 := by omega
      have divEq : (i+1)/2=i/2 := by omega
      rw [divEq]
      exact nextCache w
  refine ⟨(if i%2=0 then 127 else 26)+hn,
    (if i%2=0 then 134 else 26)+hc,next,?_,nextInv,?_,?_⟩
  · simpa [chain,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      seedTrace.trans h2Trace
  · split_ifs <;> omega
  · split_ifs <;> omega

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
      refine ⟨n+sn,c+sc,final,?_,finalInv,?_,?_⟩
      · have both := pretrace.trans step
        simpa only [h1,h2,GroupedBalancedSignUpperCost67.h1_succ,
          GroupedBalancedSignUpperCost67.h2_succ i (by omega),
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using both
      · omega
      · omega

theorem run_all (hash : Hash) (secretKey : SecretKey)
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
    ∃ (n c : Nat) (final : MachineState),
      Trace hash image start n c 247 247 final ∧
      final.pc=0x1afc ∧
      final.getMem 0x81030=BitVec.ofNat 64 67 ∧
      final.getReg .x2=start.getReg .x2 ∧
      (∀ j : ChainMixed, ∀ w : Fin 2,
        final.getMem (Signing.wordAddress (0x80800+16*j.val) w.val)=
          (endpoint hash secretKey base leaf j).extractLsb' (64*w.val) 64) ∧
      (∀ a : Word, 0x81000≤a.toNat → a≠0x81030 → a≠0x81038 →
        final.getMem a=start.getMem a) ∧
      (∀ w : Fin 4,
        final.getMem (Signing.wordAddress 0x20 w.val)=
          secretKey.extractLsb' (64*w.val) 64) ∧
      (∀ a : Word, a.toNat<0x100 →
        final.getMem a=start.getMem a) ∧
      n ≤ 35309 ∧ c ≤ 40468 := by
  obtain ⟨n,c,final,path,inv,nBound,cBound⟩ :=
    run_prefix hash secretKey base leaf witnessBase start baseBound level
      address witness witnessLower witnessBound aligned initial 67 (by omega)
  have calls : h1 67+h2 67=247 :=
    GroupedBalancedSignUpperCost67.total
  refine ⟨n,c,final,by simpa [calls] using path,?_,inv.counter,
    inv.stack,?_,inv.controls,inv.keyWords,inv.lowWords,
    by omega,by omega⟩
  · simpa using inv.pc
  · intro j w
    exact inv.endpoints j j.isLt w

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
      ready.getReg .x2=start.getReg .x2 ∧
      (∀ j : Fin 134,
        ready.getMem (Signing.wordAddress 0x80020 j.val)=
          (endpoint hash secretKey base leaf
            ⟨j.val/2,by have := j.isLt; omega⟩).extractLsb'
              (64*(j.val%2)) 64) ∧
      (∀ a : Word, 0x81000≤a.toNat → a≠0x81030 → a≠0x81038 →
        ready.getMem a=start.getMem a) ∧
      (∀ w : Fin 4,
        ready.getMem (Signing.wordAddress 0x20 w.val)=
          secretKey.extractLsb' (64*w.val) 64) ∧
      (∀ a : Word, a.toNat<0x100 →
        ready.getMem a=start.getMem a) ∧
      n ≤ 36118 ∧ c ≤ 41277 := by
  obtain ⟨n,c,table,path,tablePc,counter,tableSp,tableWords,
    tableControls,tableKey,tableLow,nBound,cBound⟩ := run_all hash secretKey base leaf
      witnessBase start baseBound level address witness witnessLower
      witnessBound aligned initial
  obtain ⟨ready,copy,readyPc,copyWords,copyFrame,copySp⟩ :=
    GroupedBalancedSignUpperEndpointCopy67.copy_all table tablePc
  have full : Trace hash image start (n+809) (c+809) 247 247 ready := by
    simpa only [Nat.add_zero] using path.trans
      (copy.trace (hash := hash))
  refine ⟨n+809,c+809,ready,full,readyPc,?_,?_,?_,?_,?_,
    by omega,by omega⟩
  · rw [copySp,tableSp]
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
    exact tableWords ch w
  · intro a high ne30 ne38
    have outside : ∀ i, i<134 → a≠Signing.wordAddress 0x80020 i := by
      intro i hi eq
      have hn := congrArg BitVec.toNat eq
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80020+8*i<2^64)] at hn
      omega
    rw [copyFrame a outside,tableControls a high ne30 ne38]
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
    exact tableKey w
  · intro a low
    have outside : ∀ i, i<134 → a≠Signing.wordAddress 0x80020 i := by
      intro i hi eq
      have hn := congrArg BitVec.toNat eq
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80020+8*i<2^64)] at hn
      omega
    rw [copyFrame a outside,tableLow a low]

#print axioms one_step
#print axioms run_all
#print axioms run_all_copy
end
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperChainFold67
