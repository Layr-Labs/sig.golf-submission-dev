import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomBoundSelected67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperAllSelected67
import SigGolfCandidate.Hypertree.GroupedBalancedSignStoredBytes67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignLoadedAllSelected67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignLoadedWire67. -/
section
/-! The loaded byte signer retains every selected bottom and upper witness word. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignLoadedAllSelected67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperSchedule67
open GroupedBalancedSignUpperOuterInvariant67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev byteSubmission := GroupedBalancedProgram67ByteSign.submission
private abbrev initialIndex :=
  GroupedBalancedSignByteLoadedBoundary67.initialIndex
private abbrev bottomRoot :=
  GroupedBalancedSignByteLoadedBoundary67.bottomRoot
private abbrev wotsSlot := GroupedBalancedSignUpperH2WitnessFrame67.slot
private abbrev pathSlot := GroupedBalancedSignBottomSelectedLevels67.pathSlot
private abbrev siblingNode := GroupedBalancedSignBottomSelectedLevels67.siblingNode

theorem loaded_all_witnesses (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    ∃ initial final : MachineState, ∃ steps cycles : Nat,
      initialState byteSubmission .sign (secretKey,cache,message) =
        some initial ∧
      Executes hash image initial steps
        ⟨.success,final,cycles,122548,130710⟩ ∧
      steps ≤ 27392745 ∧ cycles ≤ 31914272 ∧
      (∀ i : Fin 4,
        final.getMem (Signing.wordAddress 0x20060 i.val) =
          (Reference.randomizer hash secretKey message).extractLsb'
            (64*i.val) 64) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x20080 i.val) =
          (GroupedBottomTree.secret hash secretKey
            (Reference.indexOf hash message
              (Reference.randomizer hash secretKey message)).toNat).extractLsb'
                (64*i.val) 64) ∧
      (∀ level, level<10 → ∀ i : Fin 2,
        final.getMem (pathSlot level i) =
          (siblingNode hash secretKey
            (GroupedBalancedSignBottomAddress67.leafIndex
              (Reference.indexOf hash message
                (Reference.randomizer hash secretKey message)))
            ((Reference.indexOf hash message
              (Reference.randomizer hash secretKey message)).extractLsb'
                0 10).toNat level).extractLsb' (64*i.val) 64) ∧
      (∀ g, g<45 →
        ∀ chain : GroupedBalancedUpperTree67.ChainMixed, ∀ w : Fin 2,
          final.getMem (wotsSlot (currentWitness g) chain w) =
            (GroupedBalancedUpperTree67.signValues hash secretKey
              (treeBase g) (indexAt (initialIndex hash secretKey message) g).toNat
              (GroupedBalancedSignUpperAllSelected67.messageAfter hash secretKey
                (initialIndex hash secretKey message) 0
                (bottomRoot hash secretKey message) g)
              chain).extractLsb' (64*w.val) 64) ∧
      (∀ g, g<45 → ∀ level, level<height g → ∀ i : Fin 2,
        final.getMem (BitVec.ofNat 64
          (witnessBase g+16*level+8*i.val))=
          (GroupedBalancedSignUpperTreeModel67.nodeAt hash (treeBase g)
            ((indexAt (initialIndex hash secretKey message) g).toNat /
              2^height g*2^height g)
            (fun x => GroupedBalancedUpperTree67.leafRoot hash secretKey
              (treeBase g)
              ((indexAt (initialIndex hash secretKey message) g).toNat /
                2^height g*2^height g+x))
            level
            (Nat.xor (((indexAt (initialIndex hash secretKey message) g).toNat %
              2^height g)/2^level) 1)).extractLsb' (64*i.val) 64) := by
  obtain ⟨initial,upper,prefixSteps,prefixCycles,loaded,prefixTrace,
    boundary,indexBound,prefixStepBound,prefixCycleBound,
    randomWords,seedWords,pathWords⟩ :=
    GroupedBalancedSignBottomBoundSelected67.loaded_boundary_bounded_selected
      hash secretKey cache message
  obtain ⟨upperSteps,upperCycles,final,suffix,upperStepBound,
    upperCycleBound,lowFrame,wotsWords,siblingWords⟩ :=
    GroupedBalancedSignUpperAllSelected67.all_groups_all hash secretKey
      (initialIndex hash secretKey message) indexBound
      (bottomRoot hash secretKey message) upper boundary
  refine ⟨initial,final,prefixSteps+upperSteps,prefixCycles+upperCycles,
    loaded,?_,by omega,by omega,?_,?_,?_,?_,?_⟩
  · simpa only [Execution.charge,Nat.reduceAdd] using
      prefixTrace.then_executes suffix
  · intro i
    exact (lowFrame _ (by fin_cases i <;> decide)).trans (randomWords i)
  · intro i
    exact (lowFrame _ (by fin_cases i <;> decide)).trans (seedWords i)
  · intro level hlevel i
    have below : (pathSlot level i).toNat<currentWitness 0 := by
      change (BitVec.ofNat 64 (0x20090+16*level+8*i.val)).toNat <
        0x20130
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by
        have hi := i.isLt
        omega)]
      have hi := i.isLt
      omega
    exact (lowFrame _ below).trans (pathWords level hlevel i)
  · exact wotsWords
  · exact siblingWords

#print axioms loaded_all_witnesses
end SigGolfCandidate.Hypertree.GroupedBalancedSignLoadedAllSelected67

end

/-! The completed byte signer stores the canonical functional signature wire. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignLoadedWire67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedScheme67 GroupedBalancedWire67
open GroupedBalancedSignUpperSchedule67
set_option maxRecDepth 32768
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev byteSubmission := GroupedBalancedProgram67ByteSign.submission
private abbrev signature (hash : Hash) (secretKey : SecretKey)
    (message : Message) := GroupedBalancedScheme67.sign hash secretKey message

theorem loaded_wire (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    ∃ initial final : MachineState, ∃ steps cycles : Nat,
      initialState byteSubmission .sign (secretKey,cache,message) =
        some initial ∧
      Executes hash image initial steps
        ⟨.success,final,cycles,122548,130710⟩ ∧
      steps ≤ 27392745 ∧ cycles ≤ 31914272 ∧
      readBuffer final 0x20060 50848 =
        wire (signature hash secretKey message) := by
  obtain ⟨initial,final,steps,cycles,loaded,run,stepsBound,cyclesBound,
    randomWords,seedWords,bottomWords,upperLeaves,upperSiblings⟩ :=
    GroupedBalancedSignLoadedAllSelected67.loaded_all_witnesses
      hash secretKey cache message
  have output : readBuffer final 0x20060 50848 =
      wire (signature hash secretKey message) := by
    apply GroupedBalancedSignStoredBytes67.read_signature final
      (signature hash secretKey message)
    · intro i
      simpa only [signature,GroupedBalancedScheme67.sign] using randomWords i
    · intro i
      have a := GroupedBalancedSignWireFields67.signed_bottom_seed_word
        hash secretKey message i
      have b := GroupedBalancedSignWireFields67.bottom_seed_word
        (signature hash secretKey message) i
      exact (seedWords i).trans (a.symm.trans b)
    · intro level hlevel i
      have address :
          GroupedBalancedSignBottomSelectedLevels67.pathSlot level i =
          BitVec.ofNat 64 (0x20080+16*(level+1)+8*i.val) := by
        unfold GroupedBalancedSignBottomSelectedLevels67.pathSlot
        exact congrArg (BitVec.ofNat 64) (by omega)
      have machine := bottomWords level hlevel i
      change final.getMem
        (GroupedBalancedSignBottomSelectedLevels67.pathSlot level i) = _
        at machine
      rw [address] at machine
      have a :=
        GroupedBalancedSignLayersSchedule67.signed_bottom_sibling_node_word
          hash secretKey message level hlevel i
      have b := GroupedBalancedSignWireFields67.bottom_sibling_word
        (signature hash secretKey message) level hlevel i
      exact machine.trans (a.symm.trans b)
    · intro k hk chain i
      have hk45 : k<45 := by
        simpa only [GroupedBalancedScheme67.heights_length] using hk
      have startEq : currentWitness k =
          0x20130+GroupedBalancedWireUpper67.upperSize (Heights.take k) := by
        have start := GroupedBalancedSignWireUpperFields67.wire_upper_start
          k (by omega)
        omega
      have address : BitVec.ofNat 64
          (0x20130+GroupedBalancedWireUpper67.upperSize (Heights.take k)+
            16*chain.val+8*i.val) =
          GroupedBalancedSignUpperH2WitnessFrame67.slot
            (currentWitness k) chain i := by
        simp only [GroupedBalancedSignUpperH2WitnessFrame67.slot,
          Signing.wordAddress,startEq]
      have machine := upperLeaves k hk45 chain i
      change final.getMem
        (GroupedBalancedSignUpperH2WitnessFrame67.slot
          (currentWitness k) chain i) = _ at machine
      rw [←address] at machine
      have a := GroupedBalancedSignLayersSchedule67.signed_upper_leaf_word
        hash secretKey message k hk45 chain i
      have b := GroupedBalancedSignWireUpperFields67.wire_upper_leaf_word
        (signature hash secretKey message) k hk chain i
      exact machine.trans (a.symm.trans b)
    · intro k hk level hlevel i
      have hk45 : k<45 := by
        simpa only [GroupedBalancedScheme67.heights_length] using hk
      have levelBound : level<height k := by
        simpa only [GroupedBalancedSignLayersSchedule67.fixed_height_get
          k hk] using hlevel
      have startEq : currentWitness k =
          0x20130+GroupedBalancedWireUpper67.upperSize (Heights.take k) := by
        have start := GroupedBalancedSignWireUpperFields67.wire_upper_start
          k (by omega)
        omega
      have address : BitVec.ofNat 64
          (0x20130+GroupedBalancedWireUpper67.upperSize (Heights.take k)+
            16*(67+level)+8*i.val) =
          BitVec.ofNat 64
            (GroupedBalancedSignUpperSchedule67.witnessBase k+16*level+
              8*i.val) := by
        exact congrArg (BitVec.ofNat 64) (by
          unfold GroupedBalancedSignUpperSchedule67.witnessBase
          rw [startEq]
          omega)
      have machine := upperSiblings k hk45 level levelBound i
      rw [←address] at machine
      have a := GroupedBalancedSignLayersSchedule67.signed_upper_sibling_word
        hash secretKey message k level hk45 levelBound i
      have b := GroupedBalancedSignWireUpperFields67.wire_upper_sibling_word
        (signature hash secretKey message) k hk level hlevel i
      exact machine.trans (a.symm.trans b)
  exact ⟨initial,final,steps,cycles,loaded,run,stepsBound,cyclesBound,output⟩

#print axioms loaded_wire
end SigGolfCandidate.Hypertree.GroupedBalancedSignLoadedWire67
