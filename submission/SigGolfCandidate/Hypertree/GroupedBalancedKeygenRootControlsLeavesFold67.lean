import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsEndpoint67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafRestart67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsChainsFold67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeavesFold67


/-! The H3 leaf hash and store preserve both high tree-address words. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsSuffix67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenRootControlsTick67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem one_leaf_control (hash : Hash) (s final : MachineState) (n : Nat)
    (pc : s.pc = 0x131c) (bound : n < 16)
    (counter : s.getMem 0x81008#64 = BitVec.ofNat 64 n)
    (trace : Trace hash image s 865 1008 1 18 final) :
    ControlFrame s final := by
  obtain ⟨hashed,first,hashedPC,highFrame⟩ :=
    GroupedBalancedKeygenLeafHash67.copy_header_hash hash s pc
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
  constructor
  · rw [GroupedBalancedKeygenLeafStore67.store_below_frame hashed n bound
      hashedCounter 0x81010 (by decide) (by decide)]
    exact highFrame 0x81010 (by decide)
  · rw [GroupedBalancedKeygenLeafStore67.store_below_frame hashed n bound
      hashedCounter 0x81018 (by decide) (by decide)]
    exact highFrame 0x81018 (by decide)

theorem restart_control (s : MachineState) :
    ControlFrame s (GroupedBalancedKeygenLeafRestart67.restartState s) := by
  constructor
  · exact GroupedBalancedKeygenLeafRestart67.restart_other s 0x81010 (by decide)
  · exact GroupedBalancedKeygenLeafRestart67.restart_other s 0x81018 (by decide)

#print axioms one_leaf_control
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsSuffix67


/-! The keygen address words remain zero until the H4 tree begins. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsLeavesFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenRootControlsTick67
open GroupedBalancedKeygenRootControlsChainsFold67
open GroupedBalancedKeygenRootControlsSuffix67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem regular_leaf_control (hash : Hash) (s final : MachineState) (n : Nat)
    (pc : s.pc = 0x1050) (bound : n < 15)
    (counter : s.getMem 0x81030 = 0)
    (leaf : s.getMem 0x81008#64 = BitVec.ofNat 64 n)
    (level : s.getMem 0x81000 = 156)
    (trace : Trace hash image s 11854 13726 248 265 final) :
    ControlFrame s final := by
  obtain ⟨chains,first,chainsPC,_,chainsLevel,chainsLeaf⟩ :=
    GroupedBalancedKeygenChainsFold67.all_chains hash s pc counter level
  have firstFrame := all_chains_control hash s chains pc counter level first
  have chainsCounter : chains.getMem 0x81008#64 = BitVec.ofNat 64 n :=
    chainsLeaf.trans leaf
  obtain ⟨stored,second,storedPC,_,_⟩ :=
    GroupedBalancedKeygenOneLeaf67.one_leaf hash chains n chainsPC
      (by omega) chainsCounter chainsLevel
  have secondFrame := one_leaf_control hash chains stored n chainsPC
    (by omega) chainsCounter second
  have restartPC : stored.pc = 0x1040 := by
    simpa [show n ≠ 15 by omega] using storedPC
  let made := GroupedBalancedKeygenLeafRestart67.restartState stored
  have third : Trace hash image stored 4 4 0 0 made :=
    (GroupedBalancedKeygenLeafRestart67.restart_steps stored restartPC).trace
  have total : Trace hash image s 11854 13726 248 265 made := by
    simpa only [Nat.reduceAdd] using (first.trans second).trans third
  have same : final = made := Trace.deterministic trace total
  rw [same]
  exact (firstFrame.1.trans secondFrame).trans (restart_control stored)

theorem last_leaf_control (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 0)
    (leaf : s.getMem 0x81008#64 = 15#64)
    (level : s.getMem 0x81000 = 156)
    (trace : Trace hash image s 11850 13722 248 265 final) :
    ControlFrame s final := by
  obtain ⟨chains,first,chainsPC,_,chainsLevel,chainsLeaf⟩ :=
    GroupedBalancedKeygenChainsFold67.all_chains hash s pc counter level
  have firstFrame := all_chains_control hash s chains pc counter level first
  have chainsCounter : chains.getMem 0x81008#64 = 15#64 :=
    chainsLeaf.trans leaf
  obtain ⟨made,second,_,_,_⟩ :=
    GroupedBalancedKeygenOneLeaf67.one_leaf hash chains 15 chainsPC
      (by decide) (by simpa using chainsCounter) chainsLevel
  have secondFrame := one_leaf_control hash chains made 15 chainsPC
    (by decide) (by simpa using chainsCounter) second
  have total : Trace hash image s 11850 13722 248 265 made := by
    simpa only [Nat.reduceAdd] using first.trans second
  have same : final = made := Trace.deterministic trace total
  rw [same]
  exact firstFrame.1.trans secondFrame

theorem regular_leaves_control (hash : Hash) (s final : MachineState) (k : Nat)
    (bound : k ≤ 15) (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 0)
    (leaf : s.getMem 0x81008#64 = 0)
    (level : s.getMem 0x81000 = 156)
    (trace : Trace hash image s (11854*k) (13726*k)
      (248*k) (265*k) final) :
    ControlFrame s final := by
  induction k generalizing final with
  | zero =>
      have same : final = s := Trace.deterministic trace (Trace.refl s)
      rw [same]
      exact ControlFrame.refl s
  | succ k ih =>
      obtain ⟨mid,first,midPC,midCounter,midLeaf,midLevel⟩ :=
        GroupedBalancedKeygenLeavesFold67.regular_leaves hash s k
          (by omega) pc counter leaf level
      have firstFrame := ih mid (by omega) first
      obtain ⟨made,second,_,_,_,_⟩ :=
        GroupedBalancedKeygenLeavesFold67.regular_leaf hash mid k
          midPC (by omega) midCounter midLeaf midLevel
      have secondFrame := regular_leaf_control hash mid made k
        midPC (by omega) midCounter midLeaf midLevel second
      have total : Trace hash image s (11854*(k+1)) (13726*(k+1))
          (248*(k+1)) (265*(k+1)) made := by
        simpa only [Nat.mul_succ,Nat.add_comm] using first.trans second
      have same : final = made := Trace.deterministic trace total
      rw [same]
      exact firstFrame.trans secondFrame

theorem sixteen_leaves_control (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 0)
    (leaf : s.getMem 0x81008#64 = 0)
    (level : s.getMem 0x81000 = 156)
    (trace : Trace hash image s 189660 219612 3968 4240 final) :
    ControlFrame s final := by
  obtain ⟨mid,first,midPC,midCounter,midLeaf,midLevel⟩ :=
    GroupedBalancedKeygenLeavesFold67.regular_leaves hash s 15
      (by decide) pc counter leaf level
  have firstFrame := regular_leaves_control hash s mid 15
    (by decide) pc counter leaf level first
  obtain ⟨made,second,_,_,_⟩ :=
    GroupedBalancedKeygenLeavesFold67.last_leaf hash mid
      midPC midCounter (by simpa using midLeaf) midLevel
  have secondFrame := last_leaf_control hash mid made midPC midCounter
    (by simpa using midLeaf) midLevel second
  have total : Trace hash image s 189660 219612 3968 4240 made := by
    simpa only [Nat.reduceMul,Nat.reduceAdd] using first.trans second
  have same : final = made := Trace.deterministic trace total
  rw [same]
  exact firstFrame.trans secondFrame

theorem entry_sixteen_controls (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x1000)
    (trace : Trace hash image s 189680 219632 3968 4240 final) :
    final.getMem 0x81010 = 0 ∧ final.getMem 0x81018 = 0 := by
  let entry := GroupedBalancedKeygenPrefix67.entryState s
  have first : Trace hash image s 20 20 0 0 entry :=
    GroupedBalancedKeygenPrefix67.entry_trace hash s pc
  obtain ⟨entryLevel,entryLeaf,entry10,entry18,entryCounter⟩ :=
    GroupedBalancedKeygenPrefix67.entry_words s
  obtain ⟨made,second,_,_,_⟩ :=
    GroupedBalancedKeygenLeavesFold67.sixteen_leaves hash entry
      (GroupedBalancedKeygenPrefix67.entry_pc s pc)
      entryCounter entryLeaf entryLevel
  have frame := sixteen_leaves_control hash entry made
    (GroupedBalancedKeygenPrefix67.entry_pc s pc)
    entryCounter entryLeaf entryLevel second
  have total : Trace hash image s 189680 219632 3968 4240 made := by
    simpa only [Nat.reduceAdd] using first.trans second
  have same : final = made := Trace.deterministic trace total
  rw [same]
  exact ⟨frame.1.trans entry10,frame.2.trans entry18⟩

#print axioms sixteen_leaves_control
#print axioms entry_sixteen_controls
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsLeavesFold67
