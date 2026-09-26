import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeHashReady67
import SigGolfCandidate.Hypertree.KeygenNode
import SigGolfCandidate.Hypertree.GroupedBottomTree
import SigGolfCandidate.Hypertree.KeygenDomain

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeH4Prelude67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeH4Query67. -/
section
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeH4Prelude67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
private abbrev image := GroupedBalancedSignImage67.image
def preludeState (s : MachineState) : MachineState :=
  GroupedBalancedSignBottomTreeHashReady67.readyState
    (GroupedBalancedSignBottomTreeHeaderMid67.middleState
      (GroupedBalancedSignBottomTreeTag67.tagState s))
theorem prelude_steps (s : MachineState) (pc : s.pc = 0x1f50) :
    OrdinarySteps image s 33 (preludeState s) := by
  let first := GroupedBalancedSignBottomTreeTag67.tagState s
  let second := GroupedBalancedSignBottomTreeHeaderMid67.middleState first
  have a := GroupedBalancedSignBottomTreeTag67.tag_steps s pc
  have b := GroupedBalancedSignBottomTreeHeaderMid67.middle_steps first
    (GroupedBalancedSignBottomTreeTag67.tag_pc s pc)
  have c := GroupedBalancedSignBottomTreeHashReady67.ready_steps second
    (GroupedBalancedSignBottomTreeHeaderMid67.middle_pc first
      (GroupedBalancedSignBottomTreeTag67.tag_pc s pc))
  have ab := Keygen.ordinary_trans image s first second 9 12 a b
  have abc := Keygen.ordinary_trans image s second (preludeState s) 21 12
    (by simpa only [show 12 + 9 = 21 by decide] using ab) c
  simpa only [show 12 + 21 = 33 by decide] using abc
theorem prelude_pc (s : MachineState) (pc : s.pc = 0x1f50) :
    (preludeState s).pc = 0x1fd4 := by
  exact GroupedBalancedSignBottomTreeHashReady67.ready_pc
    (GroupedBalancedSignBottomTreeHeaderMid67.middleState
      (GroupedBalancedSignBottomTreeTag67.tagState s))
    (GroupedBalancedSignBottomTreeHeaderMid67.middle_pc
      (GroupedBalancedSignBottomTreeTag67.tagState s)
      (GroupedBalancedSignBottomTreeTag67.tag_pc s pc))
theorem prelude_header (s : MachineState) (i : Fin 4) :
    (preludeState s).getMem (Signing.wordAddress 0x80000 i.val) =
      if i.val = 0 then 4 + (s.getMem 0x81000 <<< 8)
      else s.getMem (Signing.wordAddress 0x81000 i.val) := by
  fin_cases i <;>
    simp [preludeState,GroupedBalancedSignBottomTreeHashReady67.readyState,
      GroupedBalancedSignBottomTreeHeaderMid67.middleState,
      GroupedBalancedSignBottomTreeTag67.tagState,
      Signing.wordAddress,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem prelude_frame (s : MachineState) (a : Word)
    (h0 : a ≠ 0x80000) (h1 : a ≠ 0x80008)
    (h2 : a ≠ 0x80010) (h3 : a ≠ 0x80018) :
    (preludeState s).getMem a = s.getMem a := by
  change a ≠ 524288#64 at h0
  change a ≠ 524296#64 at h1
  change a ≠ 524304#64 at h2
  change a ≠ 524312#64 at h3
  simp [preludeState,GroupedBalancedSignBottomTreeHashReady67.readyState,
    GroupedBalancedSignBottomTreeHeaderMid67.middleState,
    GroupedBalancedSignBottomTreeTag67.tagState,
    execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,h0,h1,h2,h3]
theorem prelude_hash_args (s : MachineState) :
    (preludeState s).getReg .x10 = 0x80000 ∧
    (preludeState s).getReg .x11 = 512 ∧
    (preludeState s).getReg .x12 = 0x80300 ∧
    (preludeState s).getReg .x5 = 1 := by
  simp [preludeState,GroupedBalancedSignBottomTreeHashReady67.readyState,
    GroupedBalancedSignBottomTreeHeaderMid67.middleState,
    GroupedBalancedSignBottomTreeTag67.tagState,
    execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]
#print axioms prelude_steps
#print axioms prelude_header
#print axioms prelude_frame
#print axioms prelude_hash_args
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeH4Prelude67

end

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeH4Query67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
private abbrev image := GroupedBalancedSignImage67.image
private abbrev prelude := GroupedBalancedSignBottomTreeH4Prelude67.preludeState
theorem node_words (staged : MachineState) (level tree : Nat)
    (left right : Reference.Digest)
    (levelWord : staged.getMem 0x81000 = BitVec.ofNat 64 level)
    (address : ∀ i : Fin 3,
      staged.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (leftWords : ∀ i : Fin 2,
      staged.getMem (Signing.wordAddress 0x80020 i.val) =
        left.extractLsb' (64*i.val) 64)
    (rightWords : ∀ i : Fin 2,
      staged.getMem (Signing.wordAddress 0x80030 i.val) =
        right.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 8, (prelude staged).getMem
      (Signing.wordAddress 0x80000 i.val) =
        KeygenNode.inputWord level tree left right i := by
  intro i
  fin_cases i
  · have h := GroupedBalancedSignBottomTreeH4Prelude67.prelude_header staged (0 : Fin 4)
    rw [levelWord] at h
    rw [KeygenDomain.shift_ofNat level 8] at h
    simpa [Signing.wordAddress,KeygenNode.inputWord,BitVec.ofNat_add] using h
  · have h := GroupedBalancedSignBottomTreeH4Prelude67.prelude_header staged (1 : Fin 4)
    simpa [Signing.wordAddress,KeygenNode.inputWord] using h.trans (address 0)
  · have h := GroupedBalancedSignBottomTreeH4Prelude67.prelude_header staged (2 : Fin 4)
    simpa [Signing.wordAddress,KeygenNode.inputWord] using h.trans (address 1)
  · have h := GroupedBalancedSignBottomTreeH4Prelude67.prelude_header staged (3 : Fin 4)
    simpa [Signing.wordAddress,KeygenNode.inputWord] using h.trans (address 2)
  · rw [GroupedBalancedSignBottomTreeH4Prelude67.prelude_frame staged _
      (by decide) (by decide) (by decide) (by decide)]
    simpa [Signing.wordAddress,KeygenNode.inputWord] using leftWords 0
  · rw [GroupedBalancedSignBottomTreeH4Prelude67.prelude_frame staged _
      (by decide) (by decide) (by decide) (by decide)]
    simpa [Signing.wordAddress,KeygenNode.inputWord] using leftWords 1
  · rw [GroupedBalancedSignBottomTreeH4Prelude67.prelude_frame staged _
      (by decide) (by decide) (by decide) (by decide)]
    simpa [Signing.wordAddress,KeygenNode.inputWord] using rightWords 0
  · rw [GroupedBalancedSignBottomTreeH4Prelude67.prelude_frame staged _
      (by decide) (by decide) (by decide) (by decide)]
    simpa [Signing.wordAddress,KeygenNode.inputWord] using rightWords 1
theorem node_query (staged : MachineState) (level tree : Nat)
    (left right : Reference.Digest)
    (levelWord : staged.getMem 0x81000 = BitVec.ofNat 64 level)
    (address : ∀ i : Fin 3,
      staged.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (leftWords : ∀ i : Fin 2,
      staged.getMem (Signing.wordAddress 0x80020 i.val) =
        left.extractLsb' (64*i.val) 64)
    (rightWords : ∀ i : Fin 2,
      staged.getMem (Signing.wordAddress 0x80030 i.val) =
        right.extractLsb' (64*i.val) 64) :
    hashInput (prelude staged) =
      Reference.packed (KeygenNode.payload level tree left right) := by
  obtain ⟨source,bits,_,_⟩ :=
    GroupedBalancedSignBottomTreeH4Prelude67.prelude_hash_args staged
  exact KeygenNode.query_eq (prelude staged) level tree left right
    source bits (node_words staged level tree left right levelWord address leftWords rightWords)
theorem node_answer (hash : Hash) (staged : MachineState) (level tree : Nat)
    (left right : Reference.Digest)
    (levelWord : staged.getMem 0x81000 = BitVec.ofNat 64 level)
    (address : ∀ i : Fin 3,
      staged.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (leftWords : ∀ i : Fin 2,
      staged.getMem (Signing.wordAddress 0x80020 i.val) =
        left.extractLsb' (64*i.val) 64)
    (rightWords : ∀ i : Fin 2,
      staged.getMem (Signing.wordAddress 0x80030 i.val) =
        right.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (writeHash (prelude staged) (hash (hashInput (prelude staged)))).getMem
          (Signing.wordAddress 0x80300 i.val) =
        (GroupedBottomTree.node hash level tree left right).extractLsb'
          (64*i.val) 64 := by
  obtain ⟨source,bits,destination,_⟩ :=
    GroupedBalancedSignBottomTreeH4Prelude67.prelude_hash_args staged
  have words := node_words staged level tree left right
    levelWord address leftWords rightWords
  intro i
  simpa only [GroupedBottomTree.node,Reference.node] using
    (KeygenNode.node_answer hash (prelude staged) level tree left right
      source bits destination words i)
theorem node_call (hash : Hash) (staged : MachineState)
    (pc : staged.pc = 0x1f50) :
    Trace hash image staged 34 41 1 1
      (writeHash (prelude staged) (hash (hashInput (prelude staged)))) := by
  have steps := GroupedBalancedSignBottomTreeH4Prelude67.prelude_steps staged pc
  have readyPc := GroupedBalancedSignBottomTreeH4Prelude67.prelude_pc staged pc
  have code : fetch image (prelude staged) = some (.base .ECALL) := by
    have raw : Keygen.instructionAt image 0x1fd4 = some (.base .ECALL) := by decide
    simpa only [Keygen.fetch_at,readyPc] using raw
  obtain ⟨source,bits,destination,service⟩ :=
    GroupedBalancedSignBottomTreeH4Prelude67.prelude_hash_args staged
  have valid := Keygen.hash_arguments (prelude staged) 512 source bits destination (by decide)
  have len : (hashInput (prelude staged)).1 = 512 := by
    simp [hashInput,bits]
  have call : Trace hash image (prelude staged) 1 8 1 1
      (writeHash (prelude staged) (hash (hashInput (prelude staged)))) := by
    simpa [len,compressions] using
      Trace.hash (prelude staged) _ 0 0 0 0 code service valid (Trace.refl _)
  simpa only [Nat.reduceAdd] using
    (OrdinarySteps.trace (hash := hash) steps).trans call
#print axioms node_words
#print axioms node_answer
#print axioms node_call
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeH4Query67
