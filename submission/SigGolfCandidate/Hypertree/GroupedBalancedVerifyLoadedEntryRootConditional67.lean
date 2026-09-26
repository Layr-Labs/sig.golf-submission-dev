import SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRootStep67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedStartRoot67

/-! A single loaded entry carries both bottom root and path index once each
H4 round is known to compute its reference node. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedEntryRootConditional67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyTreeHighFrame67
open GroupedBalancedVerifyBottomRootFoldCore67
open GroupedBalancedVerifyBottomRootStep67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67ByteSign.submission
private abbrev wide := GroupedBalancedVerifyBottomIndexArithmetic67.wide
private abbrev currentIndex := GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex
private abbrev currentRoot := GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot
private abbrev Low := GroupedBalancedVerifyStackGlobal67.LowFrame

def LoadedRootRound (hash : Hash) (message : Message)
    (pk : PublicKey) (wire : Bytes 50848) : Prop :=
  ∀ initial start : MachineState,
    initialState program .verify (message,pk,wire) = some initial →
    Trace hash image initial 218 240 2 3 start →
    RootRound hash
      (Reference.indexOf hash message
        (GroupedBalancedWire67.decode wire).randomizer)
      (GroupedBalancedWire67.decode wire).bottom initial start

theorem loaded_group_entry_of_round (hash : Hash) (message : Message)
    (pk : PublicKey) (wire : Bytes 50848)
    (functional : LoadedRootRound hash message pk wire) :
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
  obtain ⟨initial,loaded,initialPC⟩ :=
    initialState_exists program GroupedBalancedProgram67ByteSign.admissible
      .verify (message,pk,wire)
  obtain ⟨start,startRun,startPC,startPointer,startCounter,startIndex⟩ :=
    GroupedBalancedVerifyLoadedIndexStart67.loaded_start_index
      hash message pk wire initial loaded initialPC
  let index := Reference.indexOf hash message
    (GroupedBalancedWire67.decode wire).randomizer
  let witness := (GroupedBalancedWire67.decode wire).bottom
  obtain ⟨startBase,startSafe,startLow⟩ :=
    GroupedBalancedVerifyLoadedStartRoot67.start_fields
      hash message pk wire initial start loaded startRun
  have startRoot : RootWords start
      (GroupedBalancedVerifyBottomRootAt67.rootAt hash index witness 0) :=
    GroupedBalancedVerifyLoadedStartRoot67.start_root
      hash message pk wire initial start loaded initialPC startRun
  have startState : RootState hash index witness initial start start 0 := by
    refine ⟨?_,?_,?_,?_,?_,startLow,safe_refl start,startRoot⟩
    · simpa [GroupedBalancedVerifyTreeH4Fold67.loopPC] using startPC
    · simpa [GroupedBalancedVerifyTreeH4Fold67.ptrAt] using startPointer
    · simpa [GroupedBalancedVerifyTreeH4Fold67.countAt] using startCounter
    · simp
    · simpa using startIndex
  have step := roundStep_of_rootRound hash index witness initial start
    (functional initial start loaded startRun)
  obtain ⟨m,tree,mBound,treeRun,treeState⟩ :=
    rounds_of_step hash index witness initial start startState step 10 (by decide)
  obtain ⟨treePC,treePointer,_,treeBase,treeIndex,treeLow,treeSafe,
    treeRoot⟩ := treeState
  let entry := GroupedBalancedVerifyTreePost67.postState tree
  have postRun := GroupedBalancedVerifyTreePost67.post_steps tree
    (by simpa [GroupedBalancedVerifyTreeH4Fold67.loopPC] using treePC)
  have postPC := GroupedBalancedVerifyTreePost67.post_pc tree
    (by simpa [GroupedBalancedVerifyTreeH4Fold67.loopPC] using treePC)
  have safe := safe_trans (safe_trans startSafe treeSafe)
    (GroupedBalancedVerifyTreeLoadedDecoderSafe67.post_safe tree)
  have low := treeLow.trans
    (GroupedBalancedVerifyTreeLoadedDecoderSafe67.post_low tree)
  obtain ⟨group,height⟩ :=
    GroupedBalancedVerifyTreePost67.post_controls tree
  have finalIndex : currentIndex tree = wide index >>> 10 := by
    have h0 := treeIndex (0 : Fin 3)
    have h1 := treeIndex (1 : Fin 3)
    have h2 := treeIndex (2 : Fin 3)
    change tree.getMem 0x81008 = (wide index >>> 10).extractLsb' 0 64 at h0
    change tree.getMem 0x81010 = (wide index >>> 10).extractLsb' 64 64 at h1
    change tree.getMem 0x81018 = (wide index >>> 10).extractLsb' 128 64 at h2
    let x := wide index >>> 10
    change tree.getMem 0x81018 ++ tree.getMem 0x81010 ++
      tree.getMem 0x81008 = x
    rw [h2,h1,h0]
    calc
      (x.extractLsb' 128 64 ++ x.extractLsb' 64 64) ++
          x.extractLsb' 0 64 =
          x.extractLsb' 64 128 ++ x.extractLsb' 0 64 := by
            rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
              (x := x) (start₁ := 64) (len₁ := 64)
              (start₂ := 128) (len₂ := 64) (by decide)]
      _ = x := BitVec.extractLsb'_append_extractLsb'
  have finalRoot : currentRoot tree =
      GroupedBalancedVerifyBottomRootAt67.rootAt hash index witness 10 := by
    have lowWord := treeRoot (0 : Fin 2)
    have highWord := treeRoot (1 : Fin 2)
    change tree.getMem 0x80500 = _ at lowWord
    change tree.getMem 0x80508 = _ at highWord
    unfold currentRoot GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot
    rw [highWord,lowWord]
    exact BitVec.extractLsb'_append_extractLsb'
  refine ⟨initial,entry,m+226,loaded,by omega,?_,postPC,?_,?_,low,
    ?_,group,height,?_,?_,?_⟩
  · have all := (startRun.trans treeRun).trans postRun.trace
    simpa [entry,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all
  · exact safe.2.trans
      (GroupedBalancedVerifyEntry67.loaded_sp (message,pk,wire)
        initial loaded)
  · exact tables_of_high safe.1
      (GroupedBalancedVerifyByteContract67.initial_tables
        (message,pk,wire) initial loaded)
  · rw [GroupedBalancedVerifyTreePost67.post_mem tree 0x81048
      (by decide) (by decide),treePointer]
    decide
  · rw [GroupedBalancedVerifyTreePost67.post_mem tree 0x81000
      (by decide) (by decide),treeBase,startBase]
    decide
  · simp only [currentIndex,
      GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex]
    rw [GroupedBalancedVerifyTreePost67.post_mem tree 0x81018
        (by decide) (by decide),
      GroupedBalancedVerifyTreePost67.post_mem tree 0x81010
        (by decide) (by decide),
      GroupedBalancedVerifyTreePost67.post_mem tree 0x81008
        (by decide) (by decide)]
    change (currentIndex tree).toNat = _
    rw [finalIndex]
    exact GroupedBalancedVerifyBottomIndexArithmetic67.ten_shifted_tree index
  · change currentRoot entry = _
    have postRoot : currentRoot entry = currentRoot tree := by
      unfold currentRoot GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot
      change ((GroupedBalancedVerifyTreePost67.postState tree).getMem 0x80508 ++
          (GroupedBalancedVerifyTreePost67.postState tree).getMem 0x80500) =
        (tree.getMem 0x80508 ++ tree.getMem 0x80500)
      rw [GroupedBalancedVerifyTreePost67.post_mem tree 0x80508
          (by decide) (by decide),
        GroupedBalancedVerifyTreePost67.post_mem tree 0x80500
          (by decide) (by decide)]
    rw [postRoot]
    rw [finalRoot,GroupedBalancedVerifyBottomRootAt67.rootAt_ten]

#print axioms loaded_group_entry_of_round
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedEntryRootConditional67
