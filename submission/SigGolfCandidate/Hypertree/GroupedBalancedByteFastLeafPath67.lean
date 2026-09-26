import SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeaf67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafCarry67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastUpperPathIter67

/-! Three instructions between upper leaf compression and Merkle edge zero. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeInit67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

def initState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x50)
  execInstrBr s (.SD .x28 .x6 0)

theorem code :
    Keygen.instructionAt image 0x174c = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1750 = some (.base (.ADDI .x28 .x28 0x50)) ∧
    Keygen.instructionAt image 0x1754 = some (.base (.SD .x28 .x6 0)) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

theorem init_steps (s : MachineState) (pc : s.pc = 0x174c) :
    OrdinarySteps image s 3 (initState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x50)
  obtain ⟨c0,c1,c2⟩ := code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 2
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x50)) 1
  · have hp : s1.pc = 0x1750 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 (execInstrBr s2 (.SD .x28 .x6 0)) _
      (.base (.SD .x28 .x6 0)) 0
  · have hp : s2.pc = 0x1754 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem init_pc (s : MachineState) (pc : s.pc = 0x174c) :
    (initState s).pc = 0x1758 := by
  simp [initState,execInstrBr,pc]

theorem init_count (s : MachineState) (zero : s.getReg .x6 = 0) :
    (initState s).getMem 0x81050 = 0 := by
  simp [initState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,zero]

theorem init_mem (s : MachineState) (a : Word) (ne : a ≠ 0x81050) :
    (initState s).getMem a = s.getMem a := by
  have neq : a ≠ (528464 : Word) := by simpa using ne
  simp [initState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  intro eq
  exact False.elim (neq eq)

#print axioms init_steps
#print axioms init_count
#print axioms init_mem

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeInit67

/-! Complete upper leaf hash and height-three/four Merkle path. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafPath67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeIndexRefine67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastUpperPathIter67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem leaf_path (hash : Hash) (s : MachineState)
    (base leaf start height : Nat)
    (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest)
    (siblings : Nat → Reference.Digest)
    (done : GroupedBalancedByteFastChainEndpoints67.StrongDone hash s
      base leaf start message values)
    (heightChoice : height = 3 ∨ height = 4)
    (aligned : start % 8 = 0)
    (wireBound : start + 16*67 + 16*height ≤ 0x38da0)
    (baseBound : base < 256)
    (leafBound : leaf < 2^192)
    (hbase : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (hindex : StoredIndex s (BitVec.ofNat 192 leaf))
    (hlimit : s.getMem 0x81060 = BitVec.ofNat 64 height)
    (witness : ∀ j, j < height → ∀ half : Fin 2,
      s.getMem (BitVec.ofNat 64
        (start+16*67+16*j+8*half.val)) =
        (siblings j).extractLsb' (64*half.val) 64) :
    ∃ final steps cycles,
      Trace hash image s steps cycles (1+height) (18+height) final ∧
      final.pc = 0x19c4 ∧
      final.getMem 0x81048 =
        BitVec.ofNat 64 (start+16*67+16*height) ∧
      final.getMem 0x81050 = BitVec.ofNat 64 height ∧
      final.getMem 0x81060 = BitVec.ofNat 64 height ∧
      final.getMem 0x81000 = BitVec.ofNat 64 (base+height) ∧
      StoredIndex final (BitVec.ofNat 192 (leaf/2^height)) ∧
      (∀ half : Fin 2,
        final.getMem (Signing.wordAddress 0x80500 half.val) =
          (rootAt hash base leaf
            (GroupedBalancedUpperTree67.compressLeaf hash base leaf
              (GroupedBalancedByteFastEndpointAccum67.expectedEndpoint
                hash base leaf message values)) siblings height).extractLsb'
              (64*half.val) 64) ∧
      final.getMem 0x81058 = s.getMem 0x81058 ∧
      (∀ a : Word, a.toNat < 0x80000 → final.getMem a = s.getMem a) ∧
      (∀ a : Word, 0xfff700 ≤ a.toNat → final.getMem a = s.getMem a) ∧
      cycles ≤ 202+172*height := by
  let leafDigest := GroupedBalancedUpperTree67.compressLeaf hash base leaf
    (GroupedBalancedByteFastEndpointAccum67.expectedEndpoint hash base leaf
      message values)
  let leafState := GroupedBalancedByteFastLeaf67.leafState hash s
  let edgeEntry := GroupedBalancedByteFastEdgeInit67.initState leafState
  have leafTrace := GroupedBalancedByteFastLeaf67.leaf_trace hash s done.1.pc
  have initTrace := GroupedBalancedByteFastEdgeInit67.init_steps leafState
    leafTrace.2
  have entryPc := GroupedBalancedByteFastEdgeInit67.init_pc leafState
    leafTrace.2
  have entryCount := GroupedBalancedByteFastEdgeInit67.init_count leafState
    (GroupedBalancedByteFastLeafCarry67.leaf_x6 hash s)
  have entryMem (a : Word) (ne : a ≠ 0x81050) :
      edgeEntry.getMem a = leafState.getMem a :=
    GroupedBalancedByteFastEdgeInit67.init_mem leafState a ne
  have leafMem (a : Word) (high : 0x81000 ≤ a.toNat)
      (ne : a ≠ 0x81048) : leafState.getMem a = s.getMem a :=
    GroupedBalancedByteFastLeafCarry67.leaf_mem hash s done.1.pc a
      (GroupedBalancedByteFastLeafCarry67.outside_high a high ne)
  have entryPtr : edgeEntry.getMem 0x81048 = ptrAt (start+16*67) 0 := by
    rw [entryMem 0x81048 (by decide),
      GroupedBalancedByteFastLeafCarry67.leaf_pointer hash s done.1.pc,
      done.1.witnessPtr]
    simp [ptrAt]
  have entryLimit : edgeEntry.getMem 0x81060 = countAt height := by
    rw [entryMem 0x81060 (by decide),leafMem 0x81060
      (by decide) (by decide),hlimit]
    rfl
  have entryLevel : edgeEntry.getMem 0x81000 = BitVec.ofNat 64 base := by
    rw [entryMem 0x81000 (by decide),leafMem 0x81000
      (by decide) (by decide)]
    exact hbase
  have entryIndex : StoredIndex edgeEntry (BitVec.ofNat 192 leaf) := by
    intro i
    rw [entryMem _ (by fin_cases i <;> decide),
      leafMem _ (by fin_cases i <;> decide)
        (by fin_cases i <;> decide)]
    exact hindex i
  have entryRoot : ∀ half : Fin 2,
      edgeEntry.getMem (Signing.wordAddress 0x80500 half.val) =
        leafDigest.extractLsb' (64*half.val) 64 := by
    intro half
    rw [entryMem _ (by fin_cases half <;> decide)]
    exact GroupedBalancedByteFastLeafLayout67.leaf_result_words hash s
      base leaf start message values done hbase hindex half
  have entryWitness : ∀ j, j < height → ∀ half : Fin 2,
      edgeEntry.getMem (BitVec.ofNat 64
        (start+16*67+16*j+8*half.val)) =
        (siblings j).extractLsb' (64*half.val) 64 := by
    intro j hj half
    have low : (BitVec.ofNat 64
        (start+16*67+16*j+8*half.val)).toNat < 0x80000 := by
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega :
          start+16*67+16*j+8*half.val < 2^64)]
      omega
    rw [entryMem _ (by
      intro eq
      rw [eq] at low
      exact (by decide : ¬ ((0x81050 : Word).toNat < 0x80000)) low),
      GroupedBalancedByteFastLeafCarry67.leaf_mem hash s done.1.pc _
        (GroupedBalancedByteFastLeafCarry67.outside_low _ low)]
    exact witness j hj half
  have entryLow (a : Word) (low : a.toNat < 0x80000) :
      edgeEntry.getMem a = s.getMem a := by
    rw [entryMem a (by
      intro eq
      have h := congrArg BitVec.toNat eq
      have hc : (0x81050 : Word).toNat = 0x81050 := by decide
      rw [hc] at h
      omega)]
    exact GroupedBalancedByteFastLeafCarry67.leaf_mem hash s done.1.pc
      a (GroupedBalancedByteFastLeafCarry67.outside_low a low)
  have entryHigh (a : Word) (high : 0xfff700 ≤ a.toNat) :
      edgeEntry.getMem a = s.getMem a := by
    have disjoint (b : Word) (small : b.toNat < 0xfff700) : a ≠ b := by
      intro eq
      have h := congrArg BitVec.toNat eq
      omega
    rw [entryMem a (disjoint 0x81050 (by decide))]
    exact leafMem a (by omega) (disjoint 0x81048 (by decide))
  have aligned' : (start+16*67)%8=0 := by omega
  have levelBound : base+height<2^64 := by
    rcases heightChoice with rfl | rfl <;> omega
  obtain ⟨final,pathSteps,pathCycles,path,finalPc,finalPtr,finalCount,
    finalLimit,finalLevel,finalIndex,finalRoot,finalGroup,finalLow,
    finalHigh,_,cycleBound⟩ :=
    run_path hash edgeEntry (start+16*67) base leaf height height
      leafDigest siblings le_rfl heightChoice aligned' wireBound
      levelBound leafBound entryPc entryPtr entryCount entryLimit
      entryLevel entryIndex entryRoot entryWitness
  refine ⟨final,59+pathSteps,202+pathCycles,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have first := leafTrace.1.trans
      (OrdinarySteps.trace (hash := hash) initTrace)
    have total := first.trans path
    simpa [image,GroupedBalancedByteFastLeaf67.image] using total
  · simpa using finalPc
  · simpa [ptrAt] using finalPtr
  · simpa [countAt] using finalCount
  · simpa [countAt] using finalLimit
  · exact finalLevel
  · simpa [indexAt] using finalIndex
  · simpa [leafDigest] using finalRoot
  · rw [finalGroup,entryMem 0x81058 (by decide),
      leafMem 0x81058 (by decide) (by decide)]
  · intro a low
    rw [finalLow a low,entryLow a low]
  · intro a high
    rw [finalHigh a high,entryHigh a high]
  · omega

#print axioms leaf_path

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafPath67
