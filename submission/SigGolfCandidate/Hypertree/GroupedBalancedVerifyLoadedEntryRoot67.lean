import SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRootRound67

/-! The loaded verifier reaches its first upper group with the exact bottom
root and bottom-tree index computed from the decoded wire. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedEntryRoot67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67ByteSign.submission
private abbrev currentIndex := GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex
private abbrev currentRoot := GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot
private abbrev Low := GroupedBalancedVerifyStackGlobal67.LowFrame

theorem loaded_group_entry_root_index (hash : Hash) (message : Message)
    (pk : PublicKey) (wire : Bytes 50848) :
    ∃ initial entry n,
      initialState program .verify (message,pk,wire) = some initial ∧
      n ≤ 1856 ∧
      Trace hash image initial n (n+92) 12 13 entry ∧
      entry.pc = 0x1514 ∧
      entry.getReg .x2 = 0xfff700 ∧
      GroupedBalancedVerifyByteContract67.Tables entry ∧
      Low initial entry ∧
      entry.getMem 0x81048 = 0x2c7d0 ∧
      entry.getMem 0x81058 = 0 ∧
      entry.getMem 0x81060 = 3 ∧
      entry.getMem 0x81000 = 10 ∧
      (currentIndex entry).toNat =
        GroupedMixedIndex.bottomTree
          (Reference.indexOf hash message
            (GroupedBalancedWire67.decode wire).randomizer) ∧
      currentRoot entry =
        GroupedBottomTree.recover hash 10
          (GroupedMixedIndex.bottomTree
            (Reference.indexOf hash message
              (GroupedBalancedWire67.decode wire).randomizer))
          (Reference.indexOf hash message
            (GroupedBalancedWire67.decode wire).randomizer).toNat
          (GroupedBalancedWire67.decode wire).bottom := by
  exact GroupedBalancedVerifyLoadedEntryRootConditional67.loaded_group_entry_of_round
    hash message pk wire
    (GroupedBalancedVerifyBottomRootRound67.loaded_root_round
      hash message pk wire)

#print axioms loaded_group_entry_root_index
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedEntryRoot67
