import SigGolfCandidate.Hypertree.SignLayersMemory
import SigGolfCandidate.Hypertree.SignPrefixRefine

/-! Inlined from SigGolfCandidate.Hypertree.SignLoopEntry; its only importer was SigGolfCandidate.Hypertree.SignExecutionSetup. -/
section
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 4096

theorem loaded_scratch (secretKey : SecretKey) (cache : Cache) (message : Message)
    (s : MachineState) (loaded : initialState submission .sign (secretKey,cache,message) = some s)
    (a : Word) (high : 0x80000 ≤ a.toNat) : s.getMem a = 0 := by
  unfold initialState at loaded
  rw [if_pos (admitted.2 .sign)] at loaded
  cases Option.some.inj loaded
  dsimp only [submission]
  dsimp only [inputBuffers, Riscv.standardLayout, Layout.message, Layout.secretKey, Layout.publicKey, Layout.cache, Layout.signature, Layout.witness,List.foldl_cons,List.foldl_nil]
  rw [MachineState.getMem_setReg]
  rw [Memory.write_preserves _ 0 (bytes message) a
    (by rw [Memory.bytes_length]; decide) (by right; rw [Memory.bytes_length]; omega)]
  rw [Memory.write_preserves _ 0x60 (bytes cache) a
    (by rw [Memory.bytes_length (n := CACHE_BYTES)]; decide)
    (by right; rw [Memory.bytes_length (n := CACHE_BYTES)]; change 131168 ≤ a.toNat; omega)]
  rw [Memory.write_preserves _ 0x20 (bytes secretKey) a
    (by rw [Memory.bytes_length]; decide) (by right; rw [Memory.bytes_length]; omega)]
  rw [show sign.data = [] by rfl,MachineState.writeBytesAsWords_nil]
  rfl

theorem loaded_stack (secretKey : SecretKey) (cache : Cache) (message : Message)
    (s : MachineState) (loaded : initialState submission .sign (secretKey,cache,message) = some s) :
    s.getReg .x2 = 0x1000000 := by
  unfold initialState at loaded
  rw [if_pos (admitted.2 .sign)] at loaded
  cases Option.some.inj loaded
  rw [MachineState.getReg_setReg_eq (by decide)]
  rfl

theorem outside_index_work_low (a : Word) (low : a.toNat < 0x80000) : OutsideIndexWork a := by
  refine ⟨?_,?_,?_⟩
  all_goals
    intro i eq
    have h := congrArg BitVec.toNat eq
    simp only [wordAddress,BitVec.toNat_ofNat] at h
    have := i.isLt
    omega

/-- Exact organizer-loaded signer prefix, universally including arbitrary untrusted caches. -/
theorem loaded_loop_entry (hash : Hash) (secretKey : SecretKey) (cache : Cache) (message : Message) :
    ∃ initial final,
      initialState submission .sign (secretKey,cache,message) = some initial ∧
      Trace hash sign initial 238 268 2 4 final ∧ final.pc = 0x1220 ∧
      StoredIndex final ((Reference.indexOf hash message (Reference.randomizer hash secretKey message)).zeroExtend 192) ∧
      final.getReg .x2 = 0x1000000 ∧ final.getMem 0x80400 = 0 ∧
      final.getMem 0x80440 = 1 ∧ final.getMem 0x80448 = 0x20080 ∧
      final.getMem 0x80500 = 0 ∧ final.getMem 0x80508 = 0 ∧
      (∀ i : Fin 4, final.getMem (wordAddress 0x20060 i.val) =
        (Reference.randomizer hash secretKey message).extractLsb' (64*i.val) 64) ∧
      (∀ a, a.toNat < 0x80000 → (∀ i : Fin 4, a ≠ wordAddress 0x20060 i.val) →
        final.getMem a = initial.getMem a) := by
  obtain ⟨initial,loaded,pc⟩ := initialState_exists submission admitted .sign (secretKey,cache,message)
  obtain ⟨final,run,fpc,index,randomizer,mode,pointer,sp,frame⟩ := entry_full hash initial secretKey message pc
    (Loader.sign_secretKey submission (admitted.2 .sign) (by rfl) secretKey cache message initial loaded)
    (Loader.sign_zeroSlot submission (admitted.2 .sign) (by rfl) (by rfl) secretKey cache message initial loaded)
    (Loader.sign_message submission (admitted.2 .sign) (by rfl) secretKey cache message initial loaded)
  refine ⟨initial,final,loaded,run,fpc,index,sp.trans (loaded_stack secretKey cache message initial loaded),?_,mode,pointer,?_,?_,randomizer,?_⟩
  · rw [frame _ (by unfold OutsidePrefix OutsideIndexWork; decide)]
    exact loaded_scratch secretKey cache message initial loaded _ (by decide)
  · rw [frame _ (by unfold OutsidePrefix OutsideIndexWork; decide)]
    exact loaded_scratch secretKey cache message initial loaded _ (by decide)
  · rw [frame _ (by unfold OutsidePrefix OutsideIndexWork; decide)]
    exact loaded_scratch secretKey cache message initial loaded _ (by decide)
  · intro a low outside
    apply frame a ⟨outside_index_work_low a low,outside,?_,?_⟩
    · intro eq; rw [eq] at low; change 0x80440 < 0x80000 at low; omega
    · intro eq; rw [eq] at low; change 0x80448 < 0x80000 at low; omega

/-- info: 'SigGolfCandidate.Hypertree.Signing.loaded_loop_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loaded_loop_entry

end SigGolfCandidate.Hypertree.Signing
end

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

def loopCalls (count level : Nat) : Nat := 739*count - (if level=0 ∧ count≠0 then 734 else 0)
def loopBlocks (count level : Nat) : Nat := 761*count - (if level=0 ∧ count≠0 then 756 else 0)

theorem loopCalls_succ (count level : Nat) :
    loopCalls (count+1) level = (if level=0 then 5 else 739)+loopCalls count (level+1) := by
  unfold loopCalls
  by_cases h : level=0 <;> simp [h] <;> omega

theorem loopBlocks_succ (count level : Nat) :
    loopBlocks (count+1) level = (if level=0 then 5 else 761)+loopBlocks count (level+1) := by
  unfold loopBlocks
  by_cases h : level=0 <;> simp [h] <;> omega

/-- The complete 160-layer actual signer loop, including all serialized signature fields. -/
theorem sign_layers (hash : Hash) (secretKey : SecretKey) (count : Nat) :
    ∀ (s : MachineState) (level index : Nat) (current : Reference.Digest),
    level+count=160 → index<2^192 → s.pc=(if level=160 then 0x12f8 else 0x1220) →
    LoopData s secretKey level index current →
    ∃ final instructions cycles, Trace hash sign s instructions cycles (loopCalls count level) (loopBlocks count level) final ∧
      instructions ≤ 100454*count ∧ cycles ≤ 105803*count ∧ final.pc=0x12f8 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80500 i.val) =
        (Reference.rootsAfter hash secretKey count level index current).extractLsb' (64*i.val) 64) ∧
      LayersStored final level (Reference.signLayers hash secretKey count level index current) ∧
      (∀ address : Nat, address<0x80000 → address%8=0 → address<0x20060+layerOffset level →
        final.getMem (BitVec.ofNat 64 address) = s.getMem (BitVec.ofNat 64 address)) := by
  induction count with
  | zero =>
    intro s level index current total small pc data
    have levelEq : level=160 := by omega
    refine ⟨s,0,0,?_,by omega,by omega,?_,data.currentWords,True.intro,?_⟩
    · simpa [loopCalls,loopBlocks] using Trace.refl (hash := hash) (image := sign) s
    · simpa [levelEq] using pc
    · intro address low aligned before; rfl
  | succ count ih =>
    intro s level index current total small pc data
    have bound : level<160 := by omega
    have startPC : s.pc=0x1220 := by simpa only [if_neg (show level≠160 by omega)] using pc
    obtain ⟨next,n,c,run,nb,cb,nextPC,nextData,stored,frame⟩ := sign_layer hash s secretKey level index current startPC bound small data
    obtain ⟨final,ns,cs,rest,nsb,csb,finalPC,root,storedRest,restFrame⟩ :=
      ih next (level+1) (index/2) (Reference.treeRoot hash secretKey level (index/2)) (by omega) (by omega) nextPC nextData
    refine ⟨final,n+ns,c+cs,?_,?_,?_,finalPC,root,?_,?_⟩
    · simpa only [loopCalls_succ,loopBlocks_succ] using run.trans rest
    · have : n≤100454 := by split at nb <;> omega
      omega
    · have : c≤105803 := by split at cb <;> omega
      omega
    · exact ⟨stored.prefix_frame next final level _ bound restFrame,storedRest⟩
    · intro address low aligned before
      rw [restFrame address low aligned (by have := layerOffset_mono level (level+1) (by omega); omega)]
      apply frame address low aligned
      left
      simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show address<2^64 by omega)] using before

/-- info: 'SigGolfCandidate.Hypertree.Signing.sign_layers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_layers
end SigGolfCandidate.Hypertree.Signing


namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

theorem secretKey_words_of_bytes (s : MachineState) (base : Nat) (value : SecretKey)
    (aligned : base%8=0) (bound : base+32<2^64)
    (bytes : ∀ i, i<32 → s.getByte (BitVec.ofNat 64 (base+i)) = value.extractLsb' (8*i) 8)
    (i : Fin 4) : s.getMem (wordAddress base i.val)=value.extractLsb' (64*i.val) 64 := by
  apply eq_of_forall_extractByte
  intro j hj
  have hi := i.isLt
  have whole : 8*i.val+j<32 := by omega
  have quot : (8*i.val+j)/8=i.val := by omega
  have rem : (8*i.val+j)%8=j := by omega
  have h := bytes (8*i.val+j) whole
  rw [getByte_word _ base (8*i.val+j) aligned (by omega)] at h
  simp only [quot,rem] at h
  rw [h]
  symm
  simpa only [quot,rem] using KeygenNode.extractByte_slice value (8*i.val+j)

/-- The official loaded prefix satisfies every hypothesis of the complete loop. -/
theorem loaded_loop_data (hash : Hash) (secretKey : SecretKey) (cache : Cache) (message : Message) :
    ∃ initial ready, initialState submission .sign (secretKey,cache,message)=some initial ∧
      Trace hash sign initial 238 268 2 4 ready ∧ ready.pc=0x1220 ∧
      LoopData ready secretKey 0 (Reference.indexOf hash message (Reference.randomizer hash secretKey message)).toNat 0 ∧
      (∀ i : Fin 4, ready.getMem (wordAddress 0x20060 i.val)=
        (Reference.randomizer hash secretKey message).extractLsb' (64*i.val) 64) := by
  obtain ⟨initial,ready,loaded,run,pc,index,sp,level,mode,ptr,lo,hi,randomizer,frame⟩ :=
    loaded_loop_entry hash secretKey cache message
  have loadedSecretKey := secretKey_words_of_bytes initial 0x20 secretKey (by decide) (by decide)
    (Loader.sign_secretKey submission (admitted.2 .sign) (by rfl) secretKey cache message initial loaded)
  refine ⟨initial,ready,loaded,run,pc,?_,randomizer⟩
  · constructor
    · exact sp
    · exact level
    · have eq : (Reference.indexOf hash message (Reference.randomizer hash secretKey message)).zeroExtend 192 =
          BitVec.ofNat 192 (Reference.indexOf hash message (Reference.randomizer hash secretKey message)).toNat := by
        apply BitVec.eq_of_toNat_eq
        simp
      rw [←eq]; exact index
    · intro i
      rw [frame _ (by fin_cases i <;> decide) (by intro j; fin_cases i <;> fin_cases j <;> decide)]
      exact loadedSecretKey i
    · exact mode
    · exact ptr
    · intro i
      fin_cases i
      · exact lo
      · exact hi

end SigGolfCandidate.Hypertree.Signing
