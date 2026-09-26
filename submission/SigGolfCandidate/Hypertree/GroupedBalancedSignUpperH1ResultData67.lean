import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1Answer67

/-! The paired H1 result is cached at 0x80d00 before parity selection. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1ResultData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev prepared := GroupedBalancedSignUpperH1Query67.prepared

theorem prepared_high_frame (s : MachineState) (a : Word)
    (high : 0x81000 ≤ a.toNat) :
    (prepared s).getMem a=s.getMem a := by
  let h := GroupedBalancedSignUpperH1Header67.headerState s
  let i := GroupedBalancedSignUpperH1Index67.indexState h
  change (GroupedBalancedSignUpperH1Ready67.readyState i).getMem a = _
  rw [GroupedBalancedSignUpperH1Ready67.ready_frame i a,
    GroupedBalancedSignUpperH1Index67.index_frame h a
      (by intro eq; subst a; simp [BitVec.toNat_ofNat] at high)
      (by intro eq; subst a; simp [BitVec.toNat_ofNat] at high)
      (by intro eq; subst a; simp [BitVec.toNat_ofNat] at high),
    GroupedBalancedSignUpperH1Header67.header_frame s a
      (by intro eq; subst a; simp [BitVec.toNat_ofNat] at high)]

theorem prepared_middle_frame (s : MachineState) (a : Word)
    (middle : 0x80800 ≤ a.toNat) :
    (prepared s).getMem a=s.getMem a := by
  let h := GroupedBalancedSignUpperH1Header67.headerState s
  let i := GroupedBalancedSignUpperH1Index67.indexState h
  change (GroupedBalancedSignUpperH1Ready67.readyState i).getMem a = _
  rw [GroupedBalancedSignUpperH1Ready67.ready_frame i a,
    GroupedBalancedSignUpperH1Index67.index_frame h a
      (by intro eq; subst a; simp [BitVec.toNat_ofNat] at middle)
      (by intro eq; subst a; simp [BitVec.toNat_ofNat] at middle)
      (by intro eq; subst a; simp [BitVec.toNat_ofNat] at middle),
    GroupedBalancedSignUpperH1Header67.header_frame s a
      (by intro eq; subst a; simp [BitVec.toNat_ofNat] at middle)]

theorem prepared_low_frame (s : MachineState) (a : Word)
    (low : a.toNat < 0x80000) :
    (prepared s).getMem a=s.getMem a := by
  let h := GroupedBalancedSignUpperH1Header67.headerState s
  let i := GroupedBalancedSignUpperH1Index67.indexState h
  change (GroupedBalancedSignUpperH1Ready67.readyState i).getMem a = _
  rw [GroupedBalancedSignUpperH1Ready67.ready_frame i a,
    GroupedBalancedSignUpperH1Index67.index_frame h a
      (by intro eq; subst a; simp [BitVec.toNat_ofNat] at low)
      (by intro eq; subst a; simp [BitVec.toNat_ofNat] at low)
      (by intro eq; subst a; simp [BitVec.toNat_ofNat] at low),
    GroupedBalancedSignUpperH1Header67.header_frame s a
      (by intro eq; subst a; simp [BitVec.toNat_ofNat] at low)]

theorem prepared_digit_frame (s : MachineState) (a : Word)
    (low : 0x80600 ≤ a.toNat) (high : a.toNat < 0x80800) :
    (prepared s).getMem a=s.getMem a := by
  let h := GroupedBalancedSignUpperH1Header67.headerState s
  let i := GroupedBalancedSignUpperH1Index67.indexState h
  change (GroupedBalancedSignUpperH1Ready67.readyState i).getMem a = _
  rw [GroupedBalancedSignUpperH1Ready67.ready_frame i a,
    GroupedBalancedSignUpperH1Index67.index_frame h a
      (by intro eq; subst a; simp [BitVec.toNat_ofNat] at low)
      (by intro eq; subst a; simp [BitVec.toNat_ofNat] at low)
      (by intro eq; subst a; simp [BitVec.toNat_ofNat] at low),
    GroupedBalancedSignUpperH1Header67.header_frame s a
      (by intro eq; subst a; simp [BitVec.toNat_ofNat] at low)]

theorem hash_high_frame (hash : Hash) (s : MachineState) (a : Word)
    (high : 0x81000 ≤ a.toNat) :
    (writeHash (prepared s) (hash (hashInput (prepared s)))).getMem a =
      s.getMem a := by
  have regs := GroupedBalancedSignUpperH1Ready67.ready_regs
    (GroupedBalancedSignUpperH1Index67.indexState
      (GroupedBalancedSignUpperH1Header67.headerState s))
  rw [Signing.hash_answer_frame (prepared s) _ regs.2.2.1 a]
  · exact prepared_high_frame s a high
  · intro i eq
    have hn := congrArg BitVec.toNat eq
    simp only [Signing.wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80300+8*i.val<2^64)] at hn
    omega

theorem hash_middle_frame (hash : Hash) (s : MachineState) (a : Word)
    (middle : 0x80800 ≤ a.toNat) :
    (writeHash (prepared s) (hash (hashInput (prepared s)))).getMem a =
      s.getMem a := by
  have regs := GroupedBalancedSignUpperH1Ready67.ready_regs
    (GroupedBalancedSignUpperH1Index67.indexState
      (GroupedBalancedSignUpperH1Header67.headerState s))
  rw [Signing.hash_answer_frame (prepared s) _ regs.2.2.1 a]
  · exact prepared_middle_frame s a middle
  · intro i eq
    have hn := congrArg BitVec.toNat eq
    simp only [Signing.wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80300+8*i.val<2^64)] at hn
    omega

theorem hash_low_frame (hash : Hash) (s : MachineState) (a : Word)
    (low : a.toNat < 0x80000) :
    (writeHash (prepared s) (hash (hashInput (prepared s)))).getMem a =
      s.getMem a := by
  have regs := GroupedBalancedSignUpperH1Ready67.ready_regs
    (GroupedBalancedSignUpperH1Index67.indexState
      (GroupedBalancedSignUpperH1Header67.headerState s))
  rw [Signing.hash_answer_frame (prepared s) _ regs.2.2.1 a]
  · exact prepared_low_frame s a low
  · intro i eq
    have hn := congrArg BitVec.toNat eq
    simp only [Signing.wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80300+8*i.val<2^64)] at hn
    omega

theorem hash_digit_frame (hash : Hash) (s : MachineState) (a : Word)
    (low : 0x80600 ≤ a.toNat) (high : a.toNat < 0x80800) :
    (writeHash (prepared s) (hash (hashInput (prepared s)))).getMem a =
      s.getMem a := by
  have regs := GroupedBalancedSignUpperH1Ready67.ready_regs
    (GroupedBalancedSignUpperH1Index67.indexState
      (GroupedBalancedSignUpperH1Header67.headerState s))
  rw [Signing.hash_answer_frame (prepared s) _ regs.2.2.1 a]
  · exact prepared_digit_frame s a low high
  · intro i eq
    have hn := congrArg BitVec.toNat eq
    simp only [Signing.wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80300+8*i.val<2^64)] at hn
    omega

theorem prepared_x19 (s : MachineState) :
    (prepared s).getReg .x19=s.getReg .x19 := by
  simp [prepared,GroupedBalancedSignUpperH1Query67.prepared,
    GroupedBalancedSignUpperH1Ready67.readyState,
    GroupedBalancedSignUpperH1Index67.indexState,
    GroupedBalancedSignUpperH1Header67.headerState,
    execInstrBr,MachineState.getReg_setReg_ne]

theorem prepared_x2 (s : MachineState) :
    (prepared s).getReg .x2=s.getReg .x2 := by
  simp [prepared,GroupedBalancedSignUpperH1Query67.prepared,
    GroupedBalancedSignUpperH1Ready67.readyState,
    GroupedBalancedSignUpperH1Index67.indexState,
    GroupedBalancedSignUpperH1Header67.headerState,
    execInstrBr,MachineState.getReg_setReg_ne]

theorem answer_high_frame (s final : MachineState) (a : Word)
    (high : 0x81000 ≤ a.toNat) (ne30 : a≠0x81030)
    (frame : ∀ a, a≠0x81030 →
      (∀ i, i<4 → a≠Signing.wordAddress 0x80d00 i) →
      final.getMem a=s.getMem a) :
    final.getMem a=s.getMem a := by
  apply frame a ne30
  intro i hi eq
  have hn := congrArg BitVec.toNat eq
  have small : 0x80d00+8*i<2^64 := by omega
  simp only [Signing.wordAddress,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small] at hn
  omega

theorem run (hash : Hash) (secretKey : SecretKey)
    (base leaf pair : Nat) (s : MachineState)
    (pc : s.pc=0x17b0)
    (level : s.getMem 0x81000=BitVec.ofNat 64 base)
    (pairWord : s.getMem 0x81030=BitVec.ofNat 64 pair)
    (address : ∀ j : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 j.val)=
        (BitVec.ofNat 192 leaf).extractLsb' (64*j.val) 64)
    (keyWords : ∀ j : Fin 4,
      s.getMem (Signing.wordAddress 0x80020 j.val)=
        secretKey.extractLsb' (64*j.val) 64) :
    ∃ final : MachineState,
      Trace hash image s 71 78 1 1 final ∧
      final.pc=0x1884 ∧
      final.getReg .x19=s.getReg .x19 ∧
      final.getReg .x2=s.getReg .x2 ∧
      final.getMem 0x81030=s.getReg .x19 ∧
      (∀ j : Fin 4,
        final.getMem (Signing.wordAddress 0x80d00 j.val)=
          (GroupedBalancedUpperTree67.secretPair hash secretKey base leaf pair).extractLsb'
            (64*j.val) 64) ∧
      (∀ a : Word, 0x81000 ≤ a.toNat → a≠0x81030 →
        final.getMem a=s.getMem a) ∧
      (∀ a : Word, 0x80800 ≤ a.toNat → a.toNat < 0x80d00 →
        final.getMem a=s.getMem a) ∧
      (∀ a : Word, a.toNat < 0x80000 → final.getMem a=s.getMem a) ∧
      (∀ a : Word, 0x80600 ≤ a.toNat → a.toNat < 0x80800 →
        final.getMem a=s.getMem a) := by
  let answered := writeHash (prepared s) (hash (hashInput (prepared s)))
  have first := GroupedBalancedSignUpperH1Query67.secret_call hash s pc
  have answeredPc : answered.pc=0x184c := by
    change (prepared s).pc+4=0x184c
    rw [GroupedBalancedSignUpperH1Query67.prepared_pc s pc]
    decide
  obtain ⟨final,copy,finalPc,x19,sp,chain,words,copyFrame⟩ :=
    GroupedBalancedSignUpperH1Answer67.answer_copy answered answeredPc
  refine ⟨final,?_,finalPc,?_,?_,chain,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceAdd] using first.trans
      (OrdinarySteps.trace (hash := hash) copy)
  · rw [x19,Keygen.hash_registers,prepared_x19]
  · rw [sp,Keygen.hash_registers,prepared_x2]
  · intro j
    rw [words j.val j.isLt]
    exact GroupedBalancedSignUpperH1Query67.secret_answer hash s
      secretKey base leaf pair level pairWord address keyWords j
  · intro a high ne30
    rw [answer_high_frame answered final a high ne30 copyFrame]
    exact hash_high_frame hash s a high
  · intro a middle beforeCache
    rw [copyFrame a (by
      intro eq
      subst a
      simp [BitVec.toNat_ofNat] at beforeCache) (by
      intro i hi eq
      have hn := congrArg BitVec.toNat eq
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80d00+8*i<2^64)] at hn
      omega)]
    exact hash_middle_frame hash s a middle
  · intro a low
    rw [copyFrame a (by
      intro eq
      subst a
      simp [BitVec.toNat_ofNat] at low) (by
      intro i hi eq
      have hn := congrArg BitVec.toNat eq
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80d00+8*i<2^64)] at hn
      omega)]
    exact hash_low_frame hash s a low
  · intro a low high
    rw [copyFrame a (by
      intro eq
      subst a
      have numeric : (0x81030 : Word).toNat=0x81030 := by decide
      rw [numeric] at high
      omega) (by
      intro i hi eq
      have hn := congrArg BitVec.toNat eq
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80d00+8*i<2^64)] at hn
      omega)]
    exact hash_digit_frame hash s a low high

#print axioms run
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1ResultData67
