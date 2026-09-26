import SigGolfCandidate.Hypertree.GroupedBalancedVerifyGroupFold67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyFinalGroup67
import SigGolfCandidate.Hypertree.GroupedBalancedProgram67ByteSign
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedEntryRoot67

/-! The loaded direct67 verifier executes its complete 45-group path. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedComplete67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67ByteSign.submission
open GroupedBalancedVerifyGroupFold67
private abbrev Low := GroupedBalancedVerifyStackGlobal67.LowFrame

theorem initial_group (hash : Hash) (entry : MachineState)
    (pc : entry.pc = 0x1514)
    (stack : entry.getReg .x2 = 0xfff700)
    (tables : GroupedBalancedVerifyByteContract67.Tables entry)
    (ptr : entry.getMem 0x81048 = 0x2c7d0)
    (group : entry.getMem 0x81058 = 0)
    (height : entry.getMem 0x81060 = 3)
    (base : entry.getMem 0x81000 = 10) :
    GroupState hash entry
      (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat
      0 entry := by
  refine ⟨pc,stack,tables,
    GroupedBalancedVerifyStackGlobal67.LowFrame.refl entry,
    ?_,?_,?_,?_,?_,rfl⟩
  · change entry.getMem 0x81048 = (0x2c7d0 : Word)
    exact ptr
  · simpa using group
  · change entry.getMem 0x81060 = (3 : Word)
    exact height
  · change entry.getMem 0x81000 = (10 : Word)
    exact base
  · simpa [leaf_zero] using
      (GroupedBalancedVerifyTreeLoadedDecoderSafe67.current_index_words entry)

theorem loaded_fold (hash : Hash)
    (input : Input program.sizes .verify) :
    ∃ initial entry mid prefixSteps steps cycles,
      initialState program .verify input = some initial ∧
      prefixSteps ≤ 1856 ∧
      Trace hash image initial (prefixSteps+steps)
        (prefixSteps+92+cycles)
        (12+callsAt hash entry
          (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat 44)
        (13+blocksAt hash entry
          (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat 44)
        mid ∧
      cycles ≤ 150820 ∧ steps ≤ cycles ∧
      Low initial entry ∧
      (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat =
        GroupedMixedIndex.bottomTree
          (Reference.indexOf hash input.1
            (GroupedBalancedWire67.decode input.2.2).randomizer) ∧
      GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot entry =
        GroupedBottomTree.recover hash 10
          (GroupedMixedIndex.bottomTree
            (Reference.indexOf hash input.1
              (GroupedBalancedWire67.decode input.2.2).randomizer))
          (Reference.indexOf hash input.1
            (GroupedBalancedWire67.decode input.2.2).randomizer).toNat
          (GroupedBalancedWire67.decode input.2.2).bottom ∧
      GroupState hash entry
        (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat
        44 mid := by
  rcases input with ⟨message,pk,wire⟩
  obtain ⟨initial,entry,prefixSteps,loaded,prefixBound,prefixRun,
    pc,stack,tables,low,ptr,group,height,base,indexEq,rootEq⟩ :=
    GroupedBalancedVerifyLoadedEntryRoot67.loaded_group_entry_root_index
      hash message pk wire
  have initialState := initial_group hash entry pc stack tables ptr group height base
  obtain ⟨mid,steps,cycles,run,bound,stepsBound,state⟩ :=
    fold hash entry
      (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat
      (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).isLt
      initialState 44 (by decide)
  have cycleBound : cycles ≤ 150820 := by
    have height : accumulatedHeight 44 = 146 := by decide
    rw [height] at bound
    omega
  refine ⟨initial,entry,mid,prefixSteps,steps,cycles,loaded,prefixBound,
    ?_,cycleBound,stepsBound,low,indexEq,rootEq,state⟩
  simpa only [Nat.add_assoc] using prefixRun.trans run

theorem loaded_complete (hash : Hash)
    (input : Input program.sizes .verify) :
    ∃ initial entry final steps cycles,
      initialState program .verify input = some initial ∧
      steps ≤ 161393 ∧ cycles ≤ 156325 ∧
      Executes hash image initial steps
        ⟨if rootAt hash entry
            (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat
            45 = GroupedBalancedVerifyFinalGroup67.publicKeyDigest initial
          then .success else .failure,
          final, cycles,
          12+callsAt hash entry
            (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat
            45,
          13+blocksAt hash entry
            (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat
            45⟩ ∧
      Low initial entry ∧
      (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat =
        GroupedMixedIndex.bottomTree
          (Reference.indexOf hash input.1
            (GroupedBalancedWire67.decode input.2.2).randomizer) ∧
      GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot entry =
        GroupedBottomTree.recover hash 10
          (GroupedMixedIndex.bottomTree
            (Reference.indexOf hash input.1
              (GroupedBalancedWire67.decode input.2.2).randomizer))
          (Reference.indexOf hash input.1
            (GroupedBalancedWire67.decode input.2.2).randomizer).toNat
          (GroupedBalancedWire67.decode input.2.2).bottom := by
  obtain ⟨initial,entry,mid,prefixSteps,steps,cycles,loaded,prefixBound,
    prefixRun,cycleBound,stepBound,entryLow,indexEq,rootEq,midState⟩ :=
    loaded_fold hash input
  let leaf0 :=
    (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat
  obtain ⟨pc,stack,tables,midLow,ptr,group,height,base,index,
    root⟩ := midState
  have finalRoot :
      GroupedBalancedVerifyFinalGroup67.recoveredRoot hash mid
        (baseAt 44) (leafAt leaf0 44) (startAt 44) (heightAt 44) =
        rootAt hash entry leaf0 45 := by
    have frame := GroupedBalancedVerifyWireFrame67.group_root_frame
      hash entry mid (baseAt 44) (leafAt leaf0 44)
      (startAt 44) (heightAt 44) (rootAt hash entry leaf0 44)
      (wire_bound 44 (by decide)) midLow
    change advanceRoot hash mid (baseAt 44) (leafAt leaf0 44)
        (startAt 44) (heightAt 44)
        (GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot mid) =
      advanceRoot hash entry (baseAt 44) (leafAt leaf0 44)
        (startAt 44) (heightAt 44) (rootAt hash entry leaf0 44)
    rw [root]
    exact frame
  have pkEq : GroupedBalancedVerifyFinalGroup67.publicKeyDigest mid =
      GroupedBalancedVerifyFinalGroup67.publicKeyDigest initial := by
    simp only [GroupedBalancedVerifyFinalGroup67.publicKeyDigest]
    rw [midLow 0x48 (by decide),midLow 0x40 (by decide),
      entryLow 0x48 (by decide),entryLow 0x40 (by decide)]
  obtain ⟨extra,finalSteps,finalCycles,final,extraBound,
    finalCycleBound,finalTotalBound,finalStepBound,finalRun⟩ :=
    GroupedBalancedVerifyFinalGroup67.final_group hash mid
      (baseAt 44) (leafAt leaf0 44) (startAt 44) (heightAt 44)
      pc stack (by simpa using group) base index ptr height tables
      (height_choice 44) (start_aligned 44)
      (wire_bound 44 (by decide)) (base_bound 44 (by decide))
      (leaf_bound leaf0 44
        (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).isLt)
  let message := rootAt hash entry leaf0 44
  let n := 1+GroupedBalancedVerifyNonfinalGroup67.decoderCost message+
    (4*GroupedBalancedChecksum67.suffixCost message+1281+
      finalSteps)+extra
  let c := 1+GroupedBalancedVerifyNonfinalGroup67.decoderCost message+
    (11*GroupedBalancedChecksum67.suffixCost message+1281+
      finalCycles)+extra
  have finalRun' : Executes hash image mid n
      ⟨if rootAt hash entry leaf0 45 =
          GroupedBalancedVerifyFinalGroup67.publicKeyDigest initial
        then .success else .failure,
        final,c,
        GroupedBalancedChecksum67.suffixCost message+1+heightAt 44,
        GroupedBalancedChecksum67.suffixCost message+18+heightAt 44⟩ := by
    simpa only [n,c,message,root,finalRoot,pkEq] using finalRun
  have fullRun := prefixRun.then_executes finalRun'
  have costBound : c ≤ 3557 := by
    rw [root] at finalTotalBound
    dsimp [c,message]
    have h : heightAt 44 = 4 := by decide
    rw [h] at finalTotalBound
    omega
  have fuelBound : prefixSteps+steps+n ≤ 161393 := by
    have h : n ≤ c := by
      simpa only [n,c,message,root] using finalStepBound
    omega
  have totalBound : prefixSteps+92+cycles+c ≤ 156325 := by omega
  have calls45 : callsAt hash entry leaf0 45 =
      callsAt hash entry leaf0 44+
        GroupedBalancedChecksum67.suffixCost message+1+heightAt 44 := rfl
  have blocks45 : blocksAt hash entry leaf0 45 =
      blocksAt hash entry leaf0 44+
        GroupedBalancedChecksum67.suffixCost message+18+heightAt 44 := rfl
  refine ⟨initial,entry,final,prefixSteps+steps+n,
    prefixSteps+92+cycles+c,loaded,fuelBound,totalBound,?_,entryLow,
    indexEq,rootEq⟩
  simpa only [leaf0,message,n,c,Execution.charge,calls45,blocks45,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using fullRun

#print axioms loaded_complete

end SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedComplete67
