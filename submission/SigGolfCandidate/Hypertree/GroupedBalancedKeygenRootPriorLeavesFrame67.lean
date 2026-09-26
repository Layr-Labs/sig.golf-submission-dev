import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsChainsFold67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafRestart67

/-! Prior keygen leaf words and the loaded secret survive later leaf executions. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootPriorLeavesFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenCacheTick67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

def SafeFrame (n : Nat) (before after : MachineState) : Prop :=
  ∀ a : Word,
    (a.toNat < 0x20060 ∨
      (0x82000 ≤ a.toNat ∧ a.toNat < 0x82000+16*n)) →
    after.getMem a = before.getMem a

theorem SafeFrame.refl (n : Nat) (s : MachineState) : SafeFrame n s s := by
  intro _ _
  rfl

theorem SafeFrame.trans {s t u : MachineState} {n : Nat}
    (first : SafeFrame n s t) (second : SafeFrame n t u) :
    SafeFrame n s u := by
  intro a safeAddress
  rw [second a safeAddress,first a safeAddress]

theorem LowFrame.toSafe {s t : MachineState} (n : Nat)
    (frame : LowFrame s t) : SafeFrame n s t := by
  intro a safeAddress
  rcases safeAddress with low | ⟨high,_⟩
  · exact frame a (Or.inl low)
  · exact frame a (Or.inr high)

theorem header_protected (s : MachineState) (a : Word)
    (safeAddress : a.toNat < 0x20060 ∨ 0x82000 ≤ a.toNat) :
    (GroupedBalancedKeygenLeafHeader67.headerState s).getMem a = s.getMem a := by
  have h0 : a ≠ 0x80000#64 :=
    protected_ne a safeAddress 0x80000 (by decide) (by decide) (by decide)
  have h8 : a ≠ 0x80008#64 :=
    protected_ne a safeAddress 0x80008 (by decide) (by decide) (by decide)
  have h10 : a ≠ 0x80010#64 :=
    protected_ne a safeAddress 0x80010 (by decide) (by decide) (by decide)
  have h18 : a ≠ 0x80018#64 :=
    protected_ne a safeAddress 0x80018 (by decide) (by decide) (by decide)
  simp [GroupedBalancedKeygenLeafHeader67.headerState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    h0,h8,h10,h18]

theorem copy_header_low (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x131c)
    (trace : Trace hash image s 844 987 1 18 final) :
    LowFrame s final := by
  obtain ⟨copied,first,copiedPC,_,copyFrame⟩ :=
    GroupedBalancedKeygenLeafCopy67.copy_leaf_words s pc
  let ready := GroupedBalancedKeygenLeafHeader67.headerState copied
  have second : Trace hash image copied 34 34 0 0 ready :=
    (GroupedBalancedKeygenLeafHeader67.header_steps copied copiedPC).trace
  have readyPC := GroupedBalancedKeygenLeafHeader67.header_pc copied copiedPC
  have readyRegs := GroupedBalancedKeygenLeafHeader67.header_regs copied
  let made := writeHash ready (hash (hashInput ready))
  have third : Trace hash image ready 1 144 1 18 made :=
    GroupedBalancedKeygenLeafHash67.hash_trace hash ready readyPC readyRegs
  have total : Trace hash image s 844 987 1 18 made := by
    simpa only [Nat.reduceAdd] using (first.trace.trans second).trans third
  have same : final = made := Trace.deterministic trace total
  rw [same]
  intro a safeAddress
  have copiedLow : copied.getMem a = s.getMem a := by
    apply copyFrame a
    intro i hi
    simpa only [Signing.wordAddress] using
      protected_ne a safeAddress (0x80020+8*i)
        (by omega) (by omega) (by omega)
  have readyLow : ready.getMem a = copied.getMem a :=
    header_protected copied a safeAddress
  have madeLow : made.getMem a = ready.getMem a := by
    apply Signing.hash_answer_frame ready (hash (hashInput ready)) readyRegs.2.2.2
    intro i
    simpa only [Signing.wordAddress] using
      protected_ne a safeAddress (0x80300+8*i.val)
        (by omega) (by have := i.isLt; omega)
        (by have := i.isLt; omega)
  exact madeLow.trans (readyLow.trans copiedLow)

theorem store_safe (s : MachineState) (n : Nat)
    (bound : n < 16)
    (counter : s.getMem 0x81008#64 = BitVec.ofNat 64 n) :
    SafeFrame n s (GroupedBalancedKeygenLeafStore67.storeState s) := by
  intro a safeAddress
  have upper : a.toNat < 0x82000+16*n := by
    rcases safeAddress with low | ⟨_,prior⟩ <;> omega
  have neCounter : a ≠ 0x81008#64 := by
    intro eq
    have value := congrArg BitVec.toNat eq
    rcases safeAddress with low | ⟨high,_⟩
    · have v : (0x81008#64 : Word).toNat = 0x81008 := by decide
      rw [v] at value
      omega
    · have v : (0x81008#64 : Word).toNat = 0x81008 := by decide
      rw [v] at value
      omega
  have start : (s.getMem 0x81008#64 <<< 4) + 0x82000#64 =
      BitVec.ofNat 64 (0x82000+16*n) := by
    rw [counter,KeygenDomain.shift_ofNat]
    simp [BitVec.ofNat_add,Nat.mul_comm,BitVec.add_comm]
  have next : (s.getMem 0x81008#64 <<< 4) + 0x82000#64 + 8#64 =
      BitVec.ofNat 64 (0x82000+16*n+8) := by
    rw [start]
    simp [BitVec.ofNat_add]
  have neStart : a ≠ (s.getMem 0x81008#64 <<< 4) + 0x82000#64 := by
    rw [start]
    intro eq
    have value := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x82000+16*n < 2^64)] at value
    omega
  have neNext : a ≠ (s.getMem 0x81008#64 <<< 4) + 0x82000#64 + 8#64 := by
    rw [next]
    intro eq
    have value := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x82000+16*n+8 < 2^64)] at value
    omega
  rw [GroupedBalancedKeygenLeafStore67.store_mem,
    if_neg neCounter,if_neg neNext,if_neg neStart]

theorem one_leaf_safe (hash : Hash) (s final : MachineState) (n : Nat)
    (pc : s.pc = 0x131c) (bound : n < 16)
    (counter : s.getMem 0x81008#64 = BitVec.ofNat 64 n)
    (trace : Trace hash image s 865 1008 1 18 final) :
    SafeFrame n s final := by
  obtain ⟨hashed,first,hashedPC,highFrame⟩ :=
    GroupedBalancedKeygenLeafHash67.copy_header_hash hash s pc
  have firstFrame := copy_header_low hash s hashed pc first
  have hashedCounter : hashed.getMem 0x81008#64 = BitVec.ofNat 64 n := by
    rw [highFrame 0x81008#64 (by decide)]
    exact counter
  obtain ⟨safe,safeNext⟩ :=
    GroupedBalancedKeygenLeafStore67.store_accesses hashed n bound hashedCounter
  let made := GroupedBalancedKeygenLeafStore67.storeState hashed
  have second : Trace hash image hashed 21 21 0 0 made :=
    (GroupedBalancedKeygenLeafStore67.store_steps hashed hashedPC safe safeNext).trace
  have total : Trace hash image s 865 1008 1 18 made := by
    simpa only [Nat.reduceAdd] using first.trans second
  have same : final = made := Trace.deterministic trace total
  rw [same]
  exact (LowFrame.toSafe n firstFrame).trans
    (store_safe hashed n bound hashedCounter)

theorem restart_safe (s : MachineState) (n : Nat) :
    SafeFrame n s (GroupedBalancedKeygenLeafRestart67.restartState s) := by
  intro a safeAddress
  apply GroupedBalancedKeygenLeafRestart67.restart_other s a
  intro eq
  have value := congrArg BitVec.toNat eq
  rcases safeAddress with low | ⟨high,_⟩
  · have v : (0x81030 : Word).toNat = 0x81030 := by decide
    rw [v] at value
    omega
  · have v : (0x81030 : Word).toNat = 0x81030 := by decide
    rw [v] at value
    omega

theorem leaf_before_restart_safe (hash : Hash) (s final : MachineState) (n : Nat)
    (pc : s.pc = 0x1050) (bound : n < 16)
    (counter : s.getMem 0x81030 = 0)
    (leaf : s.getMem 0x81008#64 = BitVec.ofNat 64 n)
    (level : s.getMem 0x81000 = 156)
    (trace : Trace hash image s 11850 13722 248 265 final) :
    SafeFrame n s final := by
  obtain ⟨chains,first,chainsPC,_,chainsLevel,chainsLeaf⟩ :=
    GroupedBalancedKeygenChainsFold67.all_chains hash s pc counter level
  have chainFrame :=
    (GroupedBalancedKeygenRootControlsChainsFold67.all_chains_control
      hash s chains pc counter level first).2
  have chainsCounter : chains.getMem 0x81008#64 = BitVec.ofNat 64 n :=
    chainsLeaf.trans leaf
  obtain ⟨made,second,_,_,_⟩ :=
    GroupedBalancedKeygenOneLeaf67.one_leaf hash chains n chainsPC
      bound chainsCounter chainsLevel
  have suffixFrame := one_leaf_safe hash chains made n chainsPC
    bound chainsCounter second
  have total : Trace hash image s 11850 13722 248 265 made := by
    simpa only [Nat.reduceAdd] using first.trans second
  have same : final = made := Trace.deterministic trace total
  rw [same]
  exact (LowFrame.toSafe n chainFrame).trans suffixFrame

theorem regular_leaf_safe (hash : Hash) (s final : MachineState) (n : Nat)
    (pc : s.pc = 0x1050) (bound : n < 15)
    (counter : s.getMem 0x81030 = 0)
    (leaf : s.getMem 0x81008#64 = BitVec.ofNat 64 n)
    (level : s.getMem 0x81000 = 156)
    (trace : Trace hash image s 11854 13726 248 265 final) :
    SafeFrame n s final := by
  obtain ⟨chains,first,chainsPC,_,chainsLevel,chainsLeaf⟩ :=
    GroupedBalancedKeygenChainsFold67.all_chains hash s pc counter level
  have chainsCounter : chains.getMem 0x81008#64 = BitVec.ofNat 64 n :=
    chainsLeaf.trans leaf
  obtain ⟨stored,second,storedPC,_,_⟩ :=
    GroupedBalancedKeygenOneLeaf67.one_leaf hash chains n chainsPC
      (by omega) chainsCounter chainsLevel
  have prefixTrace : Trace hash image s 11850 13722 248 265 stored := by
    simpa only [Nat.reduceAdd] using first.trans second
  have prefixFrame := leaf_before_restart_safe hash s stored n pc
    (by omega) counter leaf level prefixTrace
  have restartPC : stored.pc = 0x1040 := by
    simpa [show n ≠ 15 by omega] using storedPC
  let made := GroupedBalancedKeygenLeafRestart67.restartState stored
  have third : Trace hash image stored 4 4 0 0 made :=
    (GroupedBalancedKeygenLeafRestart67.restart_steps stored restartPC).trace
  have total : Trace hash image s 11854 13726 248 265 made := by
    simpa only [Nat.reduceAdd] using prefixTrace.trans third
  have same : final = made := Trace.deterministic trace total
  rw [same]
  exact prefixFrame.trans (restart_safe stored n)

theorem last_leaf_safe (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 0)
    (leaf : s.getMem 0x81008#64 = 15#64)
    (level : s.getMem 0x81000 = 156)
    (trace : Trace hash image s 11850 13722 248 265 final) :
    SafeFrame 15 s final :=
  leaf_before_restart_safe hash s final 15 pc (by decide)
    counter (by simpa using leaf) level trace

#print axioms copy_header_low
#print axioms one_leaf_safe
#print axioms regular_leaf_safe
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootPriorLeavesFrame67
