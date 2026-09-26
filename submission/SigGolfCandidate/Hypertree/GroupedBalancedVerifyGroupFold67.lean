import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeLoadedDecoderSafe67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyNonfinalGroup67

/-! The 30 height-three and 15 height-four verifier groups share one invariant. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyGroupFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67Byte.submission

def accumulatedHeight (g : Nat) : Nat :=
  if g ≤ 30 then 3*g else 90+4*(g-30)

def heightAt (g : Nat) : Nat := if g < 30 then 3 else 4
def baseAt (g : Nat) : Nat := 10+accumulatedHeight g
def startAt (g : Nat) : Nat := 0x2c7d0+16*67*g+16*accumulatedHeight g
def leafAt (leaf0 g : Nat) : Nat := leaf0 / 2^accumulatedHeight g

theorem accumulated_zero : accumulatedHeight 0 = 0 := by decide
theorem height_zero : heightAt 0 = 3 := by decide
theorem base_zero : baseAt 0 = 10 := by decide
theorem start_zero : startAt 0 = 0x2c7d0 := by decide
theorem leaf_zero (leaf0 : Nat) : leafAt leaf0 0 = leaf0 := by
  simp [leafAt,accumulated_zero]

theorem accumulated_step (g : Nat) (small : g < 44) :
    accumulatedHeight (g+1) = accumulatedHeight g+heightAt g := by
  unfold accumulatedHeight heightAt
  split_ifs <;> omega

theorem height_step (g : Nat) (small : g < 44) :
    heightAt (g+1) = if g = 29 then 4 else heightAt g := by
  unfold heightAt
  split_ifs <;> omega

theorem base_step (g : Nat) (small : g < 44) :
    baseAt (g+1) = baseAt g+heightAt g := by
  simp only [baseAt,accumulated_step g small]
  omega

theorem start_step (g : Nat) (small : g < 44) :
    startAt (g+1) = startAt g+16*67+16*heightAt g := by
  simp only [startAt,accumulated_step g small]
  omega

theorem leaf_step (leaf0 g : Nat) (small : g < 44) :
    leafAt leaf0 (g+1) = leafAt leaf0 g / 2^heightAt g := by
  simp only [leafAt,accumulated_step g small,pow_add]
  rw [Nat.div_div_eq_div_mul]

theorem height_choice (g : Nat) : heightAt g = 3 ∨ heightAt g = 4 := by
  unfold heightAt
  split_ifs <;> simp

theorem base_bound (g : Nat) (small : g < 45) : baseAt g < 256 := by
  unfold baseAt accumulatedHeight
  split_ifs <;> omega

theorem start_aligned (g : Nat) : startAt g % 8 = 0 := by
  unfold startAt
  omega

theorem wire_bound (g : Nat) (small : g < 45) :
    startAt g+16*67+16*heightAt g ≤ 0x38da0 := by
  unfold startAt accumulatedHeight heightAt
  split_ifs <;> omega

theorem leaf_bound (leaf0 g : Nat) (bound : leaf0 < 2^192) :
    leafAt leaf0 g < 2^192 := by
  have h : leafAt leaf0 g ≤ leaf0 := Nat.div_le_self _ _
  omega

def advanceRoot (hash : Hash) (wire : MachineState)
    (base leaf start height : Nat) (message : Reference.Digest) :
    Reference.Digest :=
  GroupedBalancedByteFastUpperPathIter67.rootAt hash base leaf
    (GroupedBalancedUpperTree67.compressLeaf hash base leaf
      (GroupedBalancedByteFastEndpointAccum67.expectedEndpoint hash
        base leaf message
        (GroupedBalancedVerifyGenericPath67.witnessDigest wire start)))
    (GroupedBalancedVerifyGenericPath67.siblingDigest wire start) height

def rootAt (hash : Hash) (wire : MachineState) (leaf0 : Nat) :
    Nat → Reference.Digest
  | 0 => GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot wire
  | g+1 => advanceRoot hash wire (baseAt g) (leafAt leaf0 g)
      (startAt g) (heightAt g) (rootAt hash wire leaf0 g)

def callsAt (hash : Hash) (wire : MachineState) (leaf0 : Nat) : Nat → Nat
  | 0 => 0
  | g+1 => callsAt hash wire leaf0 g +
      GroupedBalancedChecksum67.suffixCost (rootAt hash wire leaf0 g)+
      1+heightAt g

def blocksAt (hash : Hash) (wire : MachineState) (leaf0 : Nat) : Nat → Nat
  | 0 => 0
  | g+1 => blocksAt hash wire leaf0 g +
      GroupedBalancedChecksum67.suffixCost (rootAt hash wire leaf0 g)+
      18+heightAt g

def GroupState (hash : Hash) (wire : MachineState)
    (leaf0 g : Nat) (s : MachineState) : Prop :=
  s.pc = 0x1514 ∧
  s.getReg .x2 = 0xfff700 ∧
  GroupedBalancedVerifyByteContract67.Tables s ∧
  GroupedBalancedVerifyStackGlobal67.LowFrame wire s ∧
  s.getMem 0x81048 = BitVec.ofNat 64 (startAt g) ∧
  s.getMem 0x81058 = BitVec.ofNat 64 g ∧
  s.getMem 0x81060 = BitVec.ofNat 64 (heightAt g) ∧
  s.getMem 0x81000 = BitVec.ofNat 64 (baseAt g) ∧
  GroupedBalancedByteFastEdgeIndexRefine67.StoredIndex s
    (BitVec.ofNat 192 (leafAt leaf0 g)) ∧
  GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot s =
    rootAt hash wire leaf0 g

private theorem root_of_words (s : MachineState) (root : Reference.Digest)
    (words : ∀ half : Fin 2,
      s.getMem (Signing.wordAddress 0x80500 half.val) =
        root.extractLsb' (64*half.val) 64) :
    GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot s = root := by
  have lo := words ⟨0,by decide⟩
  have hi := words ⟨1,by decide⟩
  change s.getMem 0x80500 = root.extractLsb' 0 64 at lo
  change s.getMem 0x80508 = root.extractLsb' 64 64 at hi
  simp only [GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot,
    hi,lo]
  bv_decide

theorem step (hash : Hash) (wire s : MachineState) (leaf0 g : Nat)
    (small : g < 44) (leaf0Bound : leaf0 < 2^192)
    (state : GroupState hash wire leaf0 g s) :
    let message := rootAt hash wire leaf0 g
    ∃ next steps cycles tailSteps,
      tailSteps ≤ 15 ∧
      Trace hash image s
        (1+GroupedBalancedVerifyNonfinalGroup67.decoderCost message+
          (4*GroupedBalancedChecksum67.suffixCost message+1281+
            steps+tailSteps))
        (1+GroupedBalancedVerifyNonfinalGroup67.decoderCost message+
          (11*GroupedBalancedChecksum67.suffixCost message+1281+
            cycles+tailSteps))
        (GroupedBalancedChecksum67.suffixCost message+1+heightAt g)
        (GroupedBalancedChecksum67.suffixCost message+18+heightAt g)
        next ∧
      GroupState hash wire leaf0 (g+1) next ∧
      1+GroupedBalancedVerifyNonfinalGroup67.decoderCost message+
        (11*GroupedBalancedChecksum67.suffixCost message+1281+
          cycles+tailSteps) ≤ 3545 := by
  obtain ⟨pc,stack,tables,low,ptr,group,height,base,index,root⟩ := state
  obtain ⟨next,steps,cycles,tailSteps,tailBound,run,nextPc,
    nextPtr,nextGroup,nextHeight,nextBase,nextIndex,nextLow,
    nextTables,nextStack,words,cycleBound⟩ :=
    GroupedBalancedVerifyNonfinalGroup67.next_group hash s g
      (baseAt g) (leafAt leaf0 g) (startAt g) (heightAt g)
      pc stack group small base index ptr height tables
      (height_choice g) (start_aligned g) (wire_bound g (by omega))
      (base_bound g (by omega)) (leaf_bound leaf0 g leaf0Bound)
  have framed := GroupedBalancedVerifyWireFrame67.group_root_frame
    hash wire s (baseAt g) (leafAt leaf0 g) (startAt g)
    (heightAt g) (rootAt hash wire leaf0 g)
    (wire_bound g (by omega)) low
  have nextWords : ∀ half : Fin 2,
      next.getMem (Signing.wordAddress 0x80500 half.val) =
        (rootAt hash wire leaf0 (g+1)).extractLsb'
          (64*half.val) 64 := by
    intro half
    have h := words half
    rw [root] at h
    change next.getMem (Signing.wordAddress 0x80500 half.val) =
      (GroupedBalancedByteFastUpperPathIter67.rootAt hash
        (baseAt g) (leafAt leaf0 g)
        (GroupedBalancedUpperTree67.compressLeaf hash
          (baseAt g) (leafAt leaf0 g)
          (GroupedBalancedByteFastEndpointAccum67.expectedEndpoint hash
            (baseAt g) (leafAt leaf0 g) (rootAt hash wire leaf0 g)
            (GroupedBalancedVerifyGenericPath67.witnessDigest s
              (startAt g))))
        (GroupedBalancedVerifyGenericPath67.siblingDigest s (startAt g))
        (heightAt g)).extractLsb' (64*half.val) 64 at h
    rw [framed] at h
    simpa only [rootAt,advanceRoot] using h
  have nextIndex' : GroupedBalancedByteFastEdgeIndexRefine67.StoredIndex
      next (BitVec.ofNat 192 (leafAt leaf0 (g+1))) := by
    simpa only [leaf_step leaf0 g small] using nextIndex
  have nextHeight' : next.getMem 0x81060 =
      BitVec.ofNat 64 (heightAt (g+1)) := by
    rw [height_step g small]
    by_cases eq : g = 29
    · simpa [eq] using nextHeight
    · simpa [eq] using nextHeight
  have heightMax : heightAt g ≤ 4 := by
    rcases height_choice g with h | h <;> omega
  refine ⟨next,steps,cycles,tailSteps,tailBound,?_,?_,?_⟩
  · simpa only [root] using run
  · refine ⟨nextPc,nextStack,nextTables,low.trans nextLow,?_,
      nextGroup,nextHeight',?_,nextIndex',root_of_words next _ nextWords⟩
    · simpa only [start_step g small] using nextPtr
    · simpa only [base_step g small] using nextBase
  · have b := GroupedBalancedVerifyNonfinalGroup67.charged_cycles_bound
      (rootAt hash wire leaf0 g) (heightAt g) cycles tailSteps
      cycleBound tailBound
    omega

theorem fold (hash : Hash) (wire : MachineState) (leaf0 : Nat)
    (leaf0Bound : leaf0 < 2^192)
    (initial : GroupState hash wire leaf0 0 wire)
    (g : Nat) (gBound : g ≤ 44) :
    ∃ state steps cycles,
      Trace hash image wire steps cycles
        (callsAt hash wire leaf0 g) (blocksAt hash wire leaf0 g)
        state ∧
      cycles ≤ 3545*g ∧ steps ≤ cycles ∧
      GroupState hash wire leaf0 g state := by
  induction g with
  | zero =>
    exact ⟨wire,0,0,Trace.refl wire,by omega,by omega,initial⟩
  | succ g ih =>
    have small : g < 44 := by omega
    obtain ⟨mid,priorSteps,priorCycles,priorRun,priorBound,_,
      priorState⟩ := ih (by omega)
    obtain ⟨next,groupSteps,groupCycles,tailSteps,tailBound,
      groupRun,nextState,groupBound⟩ :=
      step hash wire mid leaf0 g small leaf0Bound priorState
    let message := rootAt hash wire leaf0 g
    let n := 1+GroupedBalancedVerifyNonfinalGroup67.decoderCost message+
      (4*GroupedBalancedChecksum67.suffixCost message+1281+
        groupSteps+tailSteps)
    let c := 1+GroupedBalancedVerifyNonfinalGroup67.decoderCost message+
      (11*GroupedBalancedChecksum67.suffixCost message+1281+
        groupCycles+tailSteps)
    have fullRun : Trace hash image wire
        (priorSteps+n) (priorCycles+c)
        (callsAt hash wire leaf0 (g+1))
        (blocksAt hash wire leaf0 (g+1)) next := by
      have all := priorRun.trans groupRun
      simpa only [n,c,message,callsAt,blocksAt,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all
    have fuelBound := GroupedBalancedVerifyNonfinalGroup67.trace_steps_le_cycles
      hash image fullRun
    refine ⟨next,priorSteps+n,priorCycles+c,fullRun,?_,
      fuelBound,nextState⟩
    dsimp [c,message] at groupBound ⊢
    omega

end SigGolfCandidate.Hypertree.GroupedBalancedVerifyGroupFold67
