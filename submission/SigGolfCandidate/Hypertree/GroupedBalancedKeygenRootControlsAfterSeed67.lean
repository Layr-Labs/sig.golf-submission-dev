import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsEndpoint67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenCacheChainStep67

/-! Compose an H1 seed trace with the H2 endpoint control frame. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsAfterSeed67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenRootControlsTick67
open GroupedBalancedKeygenRootControlsEndpoint67
open GroupedBalancedKeygenCacheTick67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem regular_after_seed (hash : Hash) (s ready final : MachineState)
    (n steps cycles calls blocks : Nat)
    (small : n < 65)
    (seedTrace : Trace hash image s steps cycles calls blocks ready)
    (seedFrame : ControlFrame s ready)
    (pc : ready.pc = 0x11d8)
    (counter : ready.getMem 0x81030 = BitVec.ofNat 64 n)
    (index : ready.getReg .x19 = BitVec.ofNat 64 n)
    (fullTrace : Trace hash image s (steps+86) (cycles+107)
      (calls+3) (blocks+3) final) :
    ControlFrame s final := by
  obtain ⟨made,stepTrace,_,_,_,_,_⟩ :=
    GroupedBalancedKeygenChainStep67.regular_step hash ready n pc small counter index
  have madeTrace : Trace hash image s (steps+86) (cycles+107)
      (calls+3) (blocks+3) made := seedTrace.trans stepTrace
  have same : final = made := Trace.deterministic fullTrace madeTrace
  rw [same]
  exact seedFrame.trans
    (regular_step_control hash ready made n pc small counter index stepTrace)

theorem special65_after_seed (hash : Hash) (s ready final : MachineState)
    (steps cycles calls blocks : Nat)
    (seedTrace : Trace hash image s steps cycles calls blocks ready)
    (seedFrame : ControlFrame s ready)
    (pc : ready.pc = 0x11d8)
    (counter : ready.getMem 0x81030 = 65#64)
    (index : ready.getReg .x19 = 65#64)
    (fullTrace : Trace hash image s (steps+105) (cycles+161)
      (calls+8) (blocks+8) final) :
    ControlFrame s final := by
  obtain ⟨made,stepTrace,_,_,_,_,_⟩ :=
    GroupedBalancedKeygenChainStep67.special65_step hash ready pc counter index
  have madeTrace : Trace hash image s (steps+105) (cycles+161)
      (calls+8) (blocks+8) made := seedTrace.trans stepTrace
  have same : final = made := Trace.deterministic fullTrace madeTrace
  rw [same]
  exact seedFrame.trans
    (special65_step_control hash ready made pc counter index stepTrace)

theorem special66_after_seed (hash : Hash) (s ready final : MachineState)
    (steps cycles calls blocks : Nat)
    (seedTrace : Trace hash image s steps cycles calls blocks ready)
    (seedFrame : ControlFrame s ready)
    (pc : ready.pc = 0x11d8)
    (counter : ready.getMem 0x81030 = 66#64)
    (index : ready.getReg .x19 = 66#64)
    (fullTrace : Trace hash image s (steps+114) (cycles+184)
      (calls+10) (blocks+10) final) :
    ControlFrame s final := by
  obtain ⟨made,stepTrace,_,_,_,_,_⟩ :=
    GroupedBalancedKeygenChainStep67.special66_step hash ready pc counter index
  have madeTrace : Trace hash image s (steps+114) (cycles+184)
      (calls+10) (blocks+10) made := seedTrace.trans stepTrace
  have same : final = made := Trace.deterministic fullTrace madeTrace
  rw [same]
  exact seedFrame.trans
    (special66_step_control hash ready made pc counter index stepTrace)

theorem regular_after_seed_low (hash : Hash) (s ready final : MachineState)
    (n steps cycles calls blocks : Nat) (small : n < 65)
    (seedTrace : Trace hash image s steps cycles calls blocks ready)
    (seedLow : LowFrame s ready)
    (pc : ready.pc = 0x11d8)
    (counter : ready.getMem 0x81030 = BitVec.ofNat 64 n)
    (index : ready.getReg .x19 = BitVec.ofNat 64 n)
    (fullTrace : Trace hash image s (steps+86) (cycles+107)
      (calls+3) (blocks+3) final) :
    LowFrame s final := by
  obtain ⟨made,stepTrace,_,_,_,_,_⟩ :=
    GroupedBalancedKeygenChainStep67.regular_step hash ready n pc small counter index
  have madeTrace : Trace hash image s (steps+86) (cycles+107)
      (calls+3) (blocks+3) made := seedTrace.trans stepTrace
  have same : final = made := Trace.deterministic fullTrace madeTrace
  rw [same]
  exact seedLow.trans
    (GroupedBalancedKeygenCacheChainStep67.regular_step_low
      hash ready made n pc small counter index stepTrace)

theorem special65_after_seed_low (hash : Hash) (s ready final : MachineState)
    (steps cycles calls blocks : Nat)
    (seedTrace : Trace hash image s steps cycles calls blocks ready)
    (seedLow : LowFrame s ready)
    (pc : ready.pc = 0x11d8)
    (counter : ready.getMem 0x81030 = 65#64)
    (index : ready.getReg .x19 = 65#64)
    (fullTrace : Trace hash image s (steps+105) (cycles+161)
      (calls+8) (blocks+8) final) :
    LowFrame s final := by
  obtain ⟨made,stepTrace,_,_,_,_,_⟩ :=
    GroupedBalancedKeygenChainStep67.special65_step hash ready pc counter index
  have madeTrace : Trace hash image s (steps+105) (cycles+161)
      (calls+8) (blocks+8) made := seedTrace.trans stepTrace
  have same : final = made := Trace.deterministic fullTrace madeTrace
  rw [same]
  exact seedLow.trans
    (GroupedBalancedKeygenCacheChainStep67.special65_step_low
      hash ready made pc counter index stepTrace)

theorem special66_after_seed_low (hash : Hash) (s ready final : MachineState)
    (steps cycles calls blocks : Nat)
    (seedTrace : Trace hash image s steps cycles calls blocks ready)
    (seedLow : LowFrame s ready)
    (pc : ready.pc = 0x11d8)
    (counter : ready.getMem 0x81030 = 66#64)
    (index : ready.getReg .x19 = 66#64)
    (fullTrace : Trace hash image s (steps+114) (cycles+184)
      (calls+10) (blocks+10) final) :
    LowFrame s final := by
  obtain ⟨made,stepTrace,_,_,_,_,_⟩ :=
    GroupedBalancedKeygenChainStep67.special66_step hash ready pc counter index
  have madeTrace : Trace hash image s (steps+114) (cycles+184)
      (calls+10) (blocks+10) made := seedTrace.trans stepTrace
  have same : final = made := Trace.deterministic fullTrace madeTrace
  rw [same]
  exact seedLow.trans
    (GroupedBalancedKeygenCacheChainStep67.special66_step_low
      hash ready made pc counter index stepTrace)

#print axioms regular_after_seed
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsAfterSeed67
