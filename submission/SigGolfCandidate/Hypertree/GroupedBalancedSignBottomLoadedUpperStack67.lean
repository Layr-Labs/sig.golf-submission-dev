import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeCompleteStack67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeReturn67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoadedStack67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomToUpper67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeReturnedStack67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoadedUpperStack67. -/
section
/-! Complete bottom-tree call through its three-instruction return. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeReturnedStack67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomTreeParentProtected67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

theorem bottom_tree_returned (hash : Hash) (secretKey : SecretKey)
    (base : Nat) (s : MachineState)
    (pc : s.pc = 0x14ec)
    (sp : s.getReg .x2 = 0xfff7e0 ∨ s.getReg .x2 = 0xfff700)
    (aligned : base % 1024 = 0)
    (bounded : base + 1024 ≤ 2^160)
    (count : s.getMem 0x810d0 = 1024)
    (height : s.getMem 0x81000 = 0)
    (maxLevel : s.getMem 0x81060 = 10)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (selectedBound : (s.getMem 0x810e8).toNat < 1024)
    (scratch : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x810a8 i.val) =
        (BitVec.ofNat 192 base).extractLsb' (64*i.val) 64)
    (leafWords : ∀ j, j < 1024 → ∀ i : Fin 2,
      s.getMem (GroupedBalancedSignBottomStackSlots67.slot j i.val) =
        (GroupedBottomTree.leafRoot hash secretKey (base+j)).extractLsb'
          (64*i.val) 64) :
    ∃ returned : MachineState,
      Trace hash image s 87099 94260 1023 1023 returned ∧
      returned.pc = 0x14f0 ∧
      returned.getReg .x2 = s.getReg .x2 ∧
      returned.getMem 0x810c0 = 0x83000 ∧
      (∀ i : Fin 2,
        returned.getMem (BitVec.ofNat 64 (0x83000+8*i.val)) =
          (GroupedBottomTree.root hash secretKey 10 (base/1024)).extractLsb'
            (64*i.val) 64) ∧
      (∀ a, Protected a → a ≠ s.getReg .x2 - 16 →
        returned.getMem a = s.getMem a) ∧
      returned.getMem 0x81000=10 := by
  obtain ⟨final,tree,finalPc,source,rootWords,finalSp,saved,frame,
    treeWord⟩ :=
    GroupedBalancedSignBottomTreeCompleteStack67.bottom_tree_stack hash
      secretKey base s pc sp aligned bounded count height maxLevel witnessBase
      selectedBound scratch leafWords
  have valid : accessValid (final.getReg .x2) 8 = true := by
    rw [finalSp]
    rcases sp with h | h <;> rw [h] <;> decide
  have link : final.getMem (final.getReg .x2) = 0x14f0 := by
    rw [finalSp]
    exact saved
  let returned := Keygen.returnState final
  refine ⟨returned,?_,GroupedBalancedSignBottomTreeReturn67.return_pc final link,?_,?_,?_,?_,?_⟩
  · have ret := GroupedBalancedSignBottomTreeReturn67.return_trace hash final finalPc valid
    simpa [returned,image] using tree.trans ret
  · rw [GroupedBalancedSignBottomTreeReturn67.return_sp,finalSp]
    rcases sp with h | h <;> rw [h] <;> decide
  · exact (GroupedBalancedSignBottomTreeReturn67.return_mem final 0x810c0).trans source
  · intro i
    exact (GroupedBalancedSignBottomTreeReturn67.return_mem final _).trans (rootWords i)
  · intro a safe neSlot
    exact (GroupedBalancedSignBottomTreeReturn67.return_mem final a).trans
      (frame a safe neSlot)
  · exact (GroupedBalancedSignBottomTreeReturn67.return_mem final 0x81000).trans
      treeWord

#print axioms bottom_tree_returned
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeReturnedStack67

end

/-! The official loaded signer returns from the bottom tree and enters upper signing. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoadedUpperStack67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomAddress67
open GroupedBalancedSignBottomTreeParentProtected67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev submission := GroupedBalancedProgram67Byte.submission

theorem loaded_bottom_to_upper (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    ∃ initial upper : MachineState, ∃ n c : Nat,
      initialState submission .sign (secretKey,cache,message) = some initial ∧
      Trace hash image initial n c 3073 3075 upper ∧
      upper.pc = 0x15e0 ∧
      (∀ i : Fin 2,
        upper.getMem (BitVec.ofNat 64 (0x80500+8*i.val)) =
          (GroupedBottomTree.root hash secretKey 10
            ((leafIndex (Reference.indexOf hash message
              (Reference.randomizer hash secretKey message)))/1024)).extractLsb'
                (64*i.val) 64) ∧
      upper.getMem 0x81058 = 0 ∧
      upper.getMem 0x81060 = 3 ∧
      upper.getMem 0x810f0 = 0x20130 ∧
      (∀ i : Fin 3,
        upper.getMem (Signing.wordAddress 0x81090 i.val) =
          ((BitVec.ofNat 192 (Reference.indexOf hash message
            (Reference.randomizer hash secretKey message)).toNat) >>> 10).extractLsb'
              (64*i.val) 64) ∧
      upper.getReg .x2=0xfff700 ∧
      upper.getMem 0x81000=10 ∧
      (∀ i : Fin 4, upper.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64) ∧
      (∀ a : Word, 0xfff700 ≤ a.toNat →
        upper.getMem a = initial.getMem a) ∧
      n ≤ 257742 ∧ c ≤ 279269 ∧
      (∀ i : Fin 4,
        upper.getMem (Signing.wordAddress 0x20060 i.val) =
          (Reference.randomizer hash secretKey message).extractLsb'
            (64*i.val) 64) ∧
      (∀ i : Fin 2,
        upper.getMem (Signing.wordAddress 0x20080 i.val) =
          (GroupedBottomTree.secret hash secretKey
            (Reference.indexOf hash message
              (Reference.randomizer hash secretKey message)).toNat).extractLsb'
                (64*i.val) 64) := by
  obtain ⟨initial,finish,n,c,loaded,leaves,finishPc,leafWords,maxLevel,
    count,witnessBase,scratch,selected,indexWords,height,sp,finishKey,
    finishHigh,nBound,cBound,finishRandomWords,finishSeedWords⟩ :=
    GroupedBalancedSignBottomLoadedStack67.loaded_all_bottom_leaves_stack
      hash secretKey cache message
  let index := Reference.indexOf hash message
    (Reference.randomizer hash secretKey message)
  let base := leafIndex index
  have aligned : base % 1024 = 0 :=
    GroupedBalancedSignBottomIndexBounds67.leafIndex_align index
  have bounded : base + 1024 ≤ 2^160 :=
    GroupedBalancedSignBottomIndexBounds67.leafIndex_bound index
  have selectedBound : (finish.getMem 0x810e8).toNat < 1024 :=
    GroupedBalancedSignBottomTreeStart67.selected_mask_bound finish selected
  have leafWords' : ∀ j, j < 1024 → ∀ i : Fin 2,
      finish.getMem (GroupedBalancedSignBottomStackSlots67.slot j i.val) =
        (GroupedBottomTree.leafRoot hash secretKey (base+j)).extractLsb'
          (64*i.val) 64 := by
    intro j hj i
    fin_cases i
    · simpa only [base,index,Nat.mul_zero] using (leafWords j hj).1
    · simpa only [base,index,Nat.mul_one] using (leafWords j hj).2
  obtain ⟨returned,tree,returnedPc,returnedSp,source,rootWords,frame,
    returnedTree⟩ :=
    GroupedBalancedSignBottomTreeReturnedStack67.bottom_tree_returned
      hash secretKey base finish finishPc (Or.inr sp) aligned bounded count
      height maxLevel witnessBase selectedBound scratch leafWords'
  have selectedWords : ∀ i : Fin 3,
      returned.getMem (Signing.wordAddress 0x81090 i.val) =
        (BitVec.ofNat 192 index.toNat).extractLsb' (64*i.val) 64 := by
    intro i
    have safe : Protected (Signing.wordAddress 0x81090 i.val) := by
      fin_cases i <;> simp [Signing.wordAddress,Protected]
    have neSlot : Signing.wordAddress 0x81090 i.val ≠
        finish.getReg .x2 - 16 := by
      rw [sp]
      fin_cases i <;> decide
    exact (frame _ safe neSlot).trans (by simpa [index] using indexWords i)
  obtain ⟨upper,handoff,upperPc,lowRoot,highRoot,layer,height3,witness,
      shifted,upperFrame,upperSp⟩ := GroupedBalancedSignBottomToUpper67.post_bottom_to_upper
      returned (BitVec.ofNat 192 index.toNat) returnedPc source selectedWords
  refine ⟨initial,upper,n+87099+366,c+94260+366,loaded,?_,upperPc,?_,
    layer,height3,witness,?_,upperSp.trans (returnedSp.trans sp),
    (upperFrame 0x81000 (by simp [GroupedBalancedSignBottomToUpper67.Outside])).trans
      returnedTree,?_,?_,by omega,by omega,?_,?_⟩
  · have handoffTrace := OrdinarySteps.trace (hash := hash) handoff
    simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (leaves.trans tree).trans handoffTrace
  · intro i
    fin_cases i
    · simpa [base,index] using lowRoot.trans (rootWords 0)
    · simpa [base,index] using highRoot.trans (rootWords 1)
  · intro i
    simpa [index] using shifted i
  · intro i
    have safe : Protected (Signing.wordAddress 0x20 i.val) := by
      unfold Protected
      right; right; right; right
      fin_cases i <;> decide
    have neSlot : Signing.wordAddress 0x20 i.val ≠
        finish.getReg .x2 - 16 := by
      rw [sp]
      fin_cases i <;> decide
    have outside : GroupedBalancedSignBottomToUpper67.Outside
        (Signing.wordAddress 0x20 i.val) := by
      fin_cases i <;>
        simp [GroupedBalancedSignBottomToUpper67.Outside,Signing.wordAddress]
    exact (upperFrame _ outside).trans ((frame _ safe neSlot).trans
      (finishKey i))
  · intro a high
    have ne (b : Word) (below : b.toNat < 0xfff700) : a ≠ b := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      omega
    have outside : GroupedBalancedSignBottomToUpper67.Outside a := by
      unfold GroupedBalancedSignBottomToUpper67.Outside
      exact ⟨ne _ (by decide), ne _ (by decide), ne _ (by decide),
        ne _ (by decide), ne _ (by decide), ne _ (by decide),
        ne _ (by decide), ne _ (by decide), ne _ (by decide)⟩
    have noSlot : a ≠ finish.getReg .x2 - 16 := by
      rw [sp]
      exact ne _ (by decide)
    exact (upperFrame a outside).trans ((frame a (Or.inl (by omega))
      noSlot).trans (finishHigh a high))
  · intro i
    have safe : Protected (Signing.wordAddress 0x20060 i.val) := by
      unfold Protected
      right; right; right; right
      fin_cases i <;> decide
    have neSlot : Signing.wordAddress 0x20060 i.val ≠
        finish.getReg .x2 - 16 := by
      rw [sp]
      fin_cases i <;> decide
    have outside : GroupedBalancedSignBottomToUpper67.Outside
        (Signing.wordAddress 0x20060 i.val) := by
      fin_cases i <;>
        simp [GroupedBalancedSignBottomToUpper67.Outside,Signing.wordAddress]
    exact (upperFrame _ outside).trans ((frame _ safe neSlot).trans
      (finishRandomWords i))
  · intro i
    have safe : Protected (Signing.wordAddress 0x20080 i.val) := by
      unfold Protected
      right; right; right; right
      fin_cases i <;> decide
    have neSlot : Signing.wordAddress 0x20080 i.val ≠
        finish.getReg .x2 - 16 := by
      rw [sp]
      fin_cases i <;> decide
    have outside : GroupedBalancedSignBottomToUpper67.Outside
        (Signing.wordAddress 0x20080 i.val) := by
      fin_cases i <;>
        simp [GroupedBalancedSignBottomToUpper67.Outside,Signing.wordAddress]
    exact (upperFrame _ outside).trans ((frame _ safe neSlot).trans
      (finishSeedWords i))

#print axioms loaded_bottom_to_upper
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoadedUpperStack67
