import SigGolfCandidate.Hypertree.VerifyLeafLoop
import SigGolfCandidate.Hypertree.VerifyLeafDirect
import SigGolfCandidate.Hypertree.VerifyNode
import SigGolfCandidate.Hypertree.KeygenLeafEntry

/-! Inlined from SigGolfCandidate.Hypertree.VerifyUpperLeaf; its only importer was SigGolfCandidate.Hypertree.VerifyLeafPrologue. -/
section
namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

theorem verify_leaf_hash_code : VerifyLeafDirect.Code verify 0x1690 := by decide

def OutsideUpperLeaf (side : Bool) (a : Word) : Prop :=
  OutsideLeafWork a ∧ ∀ i : Fin 2, a ≠ KeygenSavePublic.wordAddress side i.val

/-- All verifier chains, leaf compression, public-slot write, and the actual saved return. -/
theorem upper_leaf_body (hash : Hash) (s : MachineState) (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (values : Reference.Chain → Reference.Digest)
    (small : level < 160)
    (pc : s.pc = 0x1490) (data : LeafData s level tree side base message values)
    (counter : s.getMem 0x80430 = 0) (sp : s.getReg .x2 = 0xffffe0)
    (aligned : base % 8 = 0) (bound : base+736 ≤ 0x80000) :
    ∃ final steps cycles calls, Trace hash verify s steps cycles (calls+1) (calls+12) final ∧
      steps ≤ 33225 ∧ cycles ≤ 35574 ∧ calls ≤ 322 ∧
      final.pc = s.getMem 0xffffe0 &&& ~~~1#64 ∧ final.getReg .x2 = 0xfffff0 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.compressLeaf hash level tree side (recoveredEndpoint hash level tree side message values)).extractLsb' (64*i.val) 64) ∧
      (∀ a, OutsideUpperLeaf side a → final.getMem a = s.getMem a) := by
  obtain ⟨ready, steps, cycles, calls, loop, hsteps, hcycles, hcalls, readyPC, _,
    readyData, endpoints, _, readySP, loopFrame⟩ := recover_all_chains hash s level tree side base message values
      small pc data counter aligned bound
  have words : ∀ i : Fin 92, ready.getMem (wordAddress 0x80800 i.val) =
      VerifyLeafHeaderDirect.endpointWord (recoveredEndpoint hash level tree side message values) i := by
    intro i
    have addr : KeygenEndpoint.endpointAddress (i.val/2) (i.val%2) = wordAddress 0x80800 i.val := by
      unfold KeygenEndpoint.endpointAddress wordAddress
      apply congrArg (BitVec.ofNat 64)
      omega
    rw [← addr]
    exact endpoints ⟨i.val/2, by have := i.isLt; omega⟩ ⟨i.val%2, by omega⟩
  have stack : ready.getReg .x2 = 0xffffe0 := readySP.trans sp
  obtain ⟨final, suffix, finalPC, finalSP, output, suffixFrame⟩ := VerifyLeafDirect.compute_return verify hash 0x1690
    verify_leaf_hash_code leaf_return_code ready readyPC level tree side
    (recoveredEndpoint hash level tree side message values) readyData.levelEq readyData.leafEq readyData.indexEq words
    (by rw [stack]; decide) (by rw [stack]; decide) (by rw [stack]; decide)
    (by rw [stack]; cases side <;> decide)
  refine ⟨final, steps+59, cycles+154, calls, loop.trans suffix, by omega, by omega, hcalls, ?_, ?_, output, ?_⟩
  · rw [finalPC, stack, loopFrame _ (by unfold OutsideLeafWork; decide)]
  · rw [finalSP, stack]; rfl
  · intro a outside
    exact (suffixFrame a outside.1.2.2.2.2.2.2 outside.1.2.1 outside.2).trans (loopFrame a outside.1)

/-- info: 'SigGolfCandidate.Hypertree.Verifying.upper_leaf_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms upper_leaf_body

end SigGolfCandidate.Hypertree.Verifying

end

namespace SigGolfCandidate.Hypertree.VerifyLeafPrologue
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing Verifying
set_option maxRecDepth 4096

theorem entry_code : KeygenLeafEntry.Code verify 0x1460 792 := by decide

def ready (s : MachineState) : MachineState := KeygenLeafEntry.state (enterState s) 792

theorem frame (s : MachineState) (sp : s.getReg .x2 = 0xfffff0)
    (a : Word) (hs : a ≠ 0xffffe0) (hc : a ≠ 0x80430) (ht : a ≠ 0x80438) :
    (ready s).getMem a = s.getMem a := by
  unfold ready
  rw [KeygenLeafEntry.mem, if_neg ht, if_neg hc, enter_mem, sp]
  exact if_neg hs

theorem stack (s : MachineState) (sp : s.getReg .x2 = 0xfffff0) :
    (ready s).getReg .x2 = 0xffffe0 := by
  unfold ready
  rw [(KeygenLeafEntry.stack _ _).2, enter_sp, sp]
  rfl

theorem saved (s : MachineState) (sp : s.getReg .x2 = 0xfffff0) :
    (ready s).getMem 0xffffe0 = s.getReg .x1 := by
  unfold ready
  rw [KeygenLeafEntry.mem, if_neg (by decide), if_neg (by decide), enter_mem, sp, if_pos (by decide)]

theorem pc (s : MachineState) (pc : s.pc = 0x1458) (sp : s.getReg .x2 = 0xfffff0)
    (level : Nat) (nonzero : BitVec.ofNat 64 level ≠ 0) (levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level) :
    (ready s).pc = 0x1490 := by
  have eq : (enterState s).getMem 0x80400 = BitVec.ofNat 64 level := by
    rw [enter_mem, sp, if_neg (by decide)]
    exact levelEq
  unfold ready
  rw [KeygenLeafEntry.pc, eq, if_neg nonzero, enter_pc, pc]
  rfl

theorem counter (s : MachineState) : (ready s).getMem 0x80430 = 0 := by
  unfold ready
  rw [KeygenLeafEntry.mem, if_neg (by decide), if_pos rfl]

theorem context (s : MachineState) (sp : s.getReg .x2 = 0xfffff0)
    (level tree : Nat) (side : Bool) (base : Nat) (message : Reference.Digest) (signature : Reference.LayerSignature)
    (data : LeafData s level tree side base message signature.values) (bound : base+736 ≤ 0x80000) :
    LeafData (ready s) level tree side base message signature.values := by
  constructor
  · rw [frame s sp _ (by decide) (by decide) (by decide)]; exact data.levelEq
  · rw [frame s sp _ (by decide) (by decide) (by decide)]; exact data.leafEq
  · rw [frame s sp _ (by decide) (by decide) (by decide)]; exact data.pointerEq
  · intro i
    rw [frame s sp _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact data.indexEq i
  · intro chain i
    have low : (BitVec.ofNat 64 (base+16*chain.val+8*i.val)).toNat < 0x80000 := by
      have hc := chain.isLt
      have hi := i.isLt
      change (base+16*chain.val+8*i.val) % 2^64 < 0x80000
      omega
    rw [frame s sp]
    · exact data.valueEq chain i
    · intro eq; rw [eq] at low; change 0xffffe0 < 0x80000 at low; omega
    · intro eq; rw [eq] at low; change 0x80430 < 0x80000 at low; omega
    · intro eq; rw [eq] at low; change 0x80438 < 0x80000 at low; omega
  · intro chain
    rw [getByte_word (ready s) 0x80600 chain.val (by decide) (by have := chain.isLt; omega),
      frame s sp _ (by fin_cases chain <;> decide) (by fin_cases chain <;> decide) (by fin_cases chain <;> decide),
      ← getByte_word s 0x80600 chain.val (by decide) (by have := chain.isLt; omega)]
    exact data.digitEq chain

theorem block (s : MachineState) (pc : s.pc = 0x1458) (sp : s.getReg .x2 = 0xfffff0) :
    OrdinarySteps verify s 14 (ready s) := by
  have entered := enter_block verify 0x1458 leaf_enter_code s pc (by rw [sp]; decide)
  have epc : (enterState s).pc = 0x1460 := by rw [enter_pc, pc]; rfl
  have entry := KeygenLeafEntry.block verify 0x1460 792 entry_code (enterState s) epc
  exact ordinary_trans verify _ _ _ 2 12 entered entry

end SigGolfCandidate.Hypertree.VerifyLeafPrologue
