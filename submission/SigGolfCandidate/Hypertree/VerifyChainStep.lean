import SigGolfCandidate.Hypertree.VerifyHoistHash
import SigGolfCandidate.Hypertree.ChainLoopControl

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing ChainLoopControl
set_option maxRecDepth 4096

structure ChainData (s : MachineState) (level tree : Nat) (side : Bool) (chain : Reference.Chain)
    (step : Nat) (value : Reference.Digest) : Prop where
  levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level
  leafEq : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side)
  chainEq : s.getMem 0x80430 = BitVec.ofNat 64 chain.val
  stepEq : s.getMem 0x80438 = BitVec.ofNat 64 step
  indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) = (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64
  valueEq : ∀ i : Fin 2, s.getMem (wordAddress 0x80510 i.val) = value.extractLsb' (64*i.val) 64

def OutsideChainWork (a : Word) : Prop :=
  (∀ i : Fin 8, a ≠ wordAddress 0x80000 i.val) ∧
  (∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val) ∧
  (∀ i : Fin 4, a ≠ wordAddress 0x80510 i.val) ∧ a ≠ 0x80438

/-- Shared signer-side state transfer through the five-instruction chain test. -/
theorem ChainData.check (s : MachineState) (level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (step : Nat)
    (value : Reference.Digest)
    (data : ChainData s level tree side chain step value) :
    ChainData (ChainLoopControl.check s) level tree side chain step value := by
  constructor
  · simpa only [check_mem] using data.levelEq
  · simpa only [check_mem] using data.leafEq
  · simpa only [check_mem] using data.chainEq
  · simpa only [check_mem] using data.stepEq
  · intro i; simpa only [check_mem] using data.indexEq i
  · intro i; simpa only [check_mem] using data.valueEq i

/-- One in-place verifier HASH iteration at the hoisted loop entry. -/
theorem chain_tick (hash : Hash) (s : MachineState) (level tree step : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x1934) (small : step < 7) (levelBound : level < 256)
    (data : Hoist.LoopData s level tree side chain step value) :
    ∃ next, Trace hash verify s 4 11 1 1 next ∧
      next.pc = (if step+1 = 7 then 0x1944 else 0x1934) ∧
      Hoist.LoopData next level tree side chain (step+1)
        (Reference.chainHash hash level tree side chain step value) ∧
      next.getReg .x1 = s.getReg .x1 ∧ next.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → next.getMem a = s.getMem a) := by
  have tickCode : Hoist.TickCode verify := by unfold Hoist.TickCode; decide
  refine ⟨Hoist.tickState hash s,
    Hoist.tick_block verify hash tickCode s pc data.serviceEq data.srcEq
      data.lenEq data.dstEq,
    Hoist.tick_pc hash s step pc data.stepReg data.sevenReg small,
    Hoist.tick_data hash s level tree step side chain value small levelBound data,
    Hoist.tick_regs hash s .x1 (by decide),
    Hoist.tick_regs hash s .x2 (by decide), ?_⟩
  intro a outside
  apply Hoist.tick_frame hash s a data.srcEq data.dstEq
  refine ⟨?_, ?_⟩
  · simpa [wordAddress] using outside.1 (0 : Fin 8)
  · intro i
    have h := outside.1 ⟨i.val+4, by have := i.isLt; omega⟩
    simpa [wordAddress, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- info: 'SigGolfCandidate.Hypertree.Verifying.chain_tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chain_tick

end SigGolfCandidate.Hypertree.Verifying
