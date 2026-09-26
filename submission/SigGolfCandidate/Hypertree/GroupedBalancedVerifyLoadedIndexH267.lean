import SigGolfCandidate.Hypertree.GroupedBalancedVerifyIndexH2Frame67

/-! The loaded H5 index remains in the verifier scratch words after H2. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedIndexH267
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67ByteSign.submission

theorem loaded_h2_index (hash : Hash) (message : Message)
    (pk : PublicKey) (wire : Bytes 50848)
    (initial : MachineState)
    (loaded : initialState program .verify (message,pk,wire) = some initial)
    (pc : initial.pc = 0x1000) :
    ∃ final,
      Trace hash image initial 207 229 2 3 final ∧
      final.pc = 0x1264 ∧
      ((final.getMem 0x81018 ++ final.getMem 0x81010 ++
        final.getMem 0x81008) : BitVec 192).toNat =
          (Reference.indexOf hash message
            (GroupedBalancedWire67.decode wire).randomizer).toNat := by
  obtain ⟨before,prefixRun,beforePC,_,indexEq⟩ :=
    GroupedBalancedVerifyIndexPrelude67.loaded_prelude_index
      hash message pk wire initial loaded pc
  obtain ⟨final,h2Run,finalPC,frame⟩ :=
    GroupedBalancedVerifyIndexH2Frame67.h2_index_frame hash before beforePC
  refine ⟨final,?_,finalPC,?_⟩
  · simpa only [Nat.reduceAdd] using prefixRun.trans h2Run
  · have lo : final.getMem 0x81008 = before.getMem 0x81008 := by
      simpa [Signing.wordAddress] using frame (0 : Fin 3)
    have hi : final.getMem 0x81010 = before.getMem 0x81010 := by
      simpa [Signing.wordAddress] using frame (1 : Fin 3)
    have top : final.getMem 0x81018 = before.getMem 0x81018 := by
      simpa [Signing.wordAddress] using frame (2 : Fin 3)
    rw [lo,hi,top]
    exact indexEq

#print axioms loaded_h2_index
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedIndexH267
