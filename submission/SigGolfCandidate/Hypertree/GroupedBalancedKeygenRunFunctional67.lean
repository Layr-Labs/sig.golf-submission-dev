import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootCacheTree67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootPriorLeavesFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenFooterFunctional67
import SigGolfCandidate.Hypertree.GroupedBalancedProgram67ByteSign
import SigGolfCandidate.Hypertree.KeygenFunctionalInitial
import SigGolfCandidate.Hypertree.KeygenCache
import SigGolfCandidate.Execution

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenCacheAll67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenRunFunctional67. -/
section
/-! Every cache word is unchanged by the direct67 keygen execution. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenCacheAll67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenRootCacheNode67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem regular_leaves_cache (hash : Hash) (s final : MachineState)
    (k : Nat) (bound : k ≤ 15)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 0)
    (leaf : s.getMem 0x81008#64 = 0)
    (level : s.getMem 0x81000 = 156)
    (trace : Trace hash image s (11854*k) (13726*k)
      (248*k) (265*k) final) :
    CacheFrame s final := by
  induction k generalizing final with
  | zero =>
      have same : final = s := Trace.deterministic trace (Trace.refl s)
      rw [same]
      exact CacheFrame.refl s
  | succ k ih =>
      obtain ⟨mid,first,midPC,midCounter,midLeaf,midLevel⟩ :=
        GroupedBalancedKeygenLeavesFold67.regular_leaves hash s k
          (by omega) pc counter leaf level
      have firstFrame := ih mid (by omega) first
      obtain ⟨made,second,_,_,_,_⟩ :=
        GroupedBalancedKeygenLeavesFold67.regular_leaf hash mid k
          midPC (by omega) midCounter midLeaf midLevel
      have secondFrame :=
        GroupedBalancedKeygenRootPriorLeavesFrame67.regular_leaf_safe
          hash mid made k midPC (by omega) midCounter midLeaf midLevel second
      have full : Trace hash image s (11854*(k+1)) (13726*(k+1))
          (248*(k+1)) (265*(k+1)) made := by
        simpa only [Nat.mul_succ,Nat.add_comm] using first.trans second
      have same : final = made := Trace.deterministic trace full
      rw [same]
      exact firstFrame.trans (fun a low => secondFrame a (Or.inl low))

theorem sixteen_leaves_cache (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 0)
    (leaf : s.getMem 0x81008#64 = 0)
    (level : s.getMem 0x81000 = 156)
    (trace : Trace hash image s 189660 219612 3968 4240 final) :
    CacheFrame s final := by
  obtain ⟨mid,first,midPC,midCounter,midLeaf,midLevel⟩ :=
    GroupedBalancedKeygenLeavesFold67.regular_leaves hash s 15
      (by decide) pc counter leaf level
  have firstFrame := regular_leaves_cache hash s mid 15
    (by decide) pc counter leaf level first
  obtain ⟨made,second,_,_,_⟩ :=
    GroupedBalancedKeygenLeavesFold67.last_leaf hash mid
      midPC midCounter (by simpa using midLeaf) midLevel
  have secondFrame :=
    GroupedBalancedKeygenRootPriorLeavesFrame67.last_leaf_safe
      hash mid made midPC midCounter (by simpa using midLeaf)
      midLevel second
  have full : Trace hash image s 189660 219612 3968 4240 made := by
    simpa only [Nat.reduceMul,Nat.reduceAdd] using first.trans second
  have same : final = made := Trace.deterministic trace full
  rw [same]
  exact firstFrame.trans (fun a low => secondFrame a (Or.inl low))

theorem entry_leaves_cache (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x1000)
    (trace : Trace hash image s 189680 219632 3968 4240 final) :
    CacheFrame s final := by
  let entry := GroupedBalancedKeygenPrefix67.entryState s
  have first : Trace hash image s 20 20 0 0 entry :=
    GroupedBalancedKeygenPrefix67.entry_trace hash s pc
  obtain ⟨level,leaf,_,_,counter⟩ :=
    GroupedBalancedKeygenPrefix67.entry_words s
  obtain ⟨known,second,_,_,_⟩ :=
    GroupedBalancedKeygenLeavesFold67.sixteen_leaves hash entry
      (GroupedBalancedKeygenPrefix67.entry_pc s pc) counter leaf level
  have secondFrame := sixteen_leaves_cache hash entry known
    (GroupedBalancedKeygenPrefix67.entry_pc s pc) counter leaf level second
  have full : Trace hash image s 189680 219632 3968 4240 known := by
    simpa only [Nat.reduceAdd] using first.trans second
  have same : final = known := Trace.deterministic trace full
  rw [same]
  intro a low
  have ne (b : Nat) (lower : 0x80000 ≤ b) (upper : b < 2^64) :
      a ≠ BitVec.ofNat 64 b := by
    intro eq
    have h := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt upper] at h
    omega
  rw [secondFrame a low,
    GroupedBalancedKeygenPrefix67.entry_mem_other s a
      (ne 0x81000 (by decide) (by decide))
      (ne 0x81008 (by decide) (by decide))
      (ne 0x81010 (by decide) (by decide))
      (ne 0x81018 (by decide) (by decide))
      (ne 0x81030 (by decide) (by decide))]

theorem keygen_root_cache (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x1000)
    (trace : Trace hash image s 191039 221096 3983 4255 final) :
    CacheFrame s final := by
  obtain ⟨leaves,first,leavesPC,_,_⟩ :=
    GroupedBalancedKeygenLeavesFold67.entry_sixteen_leaves hash s pc
  have firstFrame := entry_leaves_cache hash s leaves pc first
  obtain ⟨known,second,_,_,_⟩ :=
    GroupedBalancedKeygenTreeFold67.tree_trace hash leaves
      leavesPC
  have secondFrame :=
    GroupedBalancedKeygenRootCacheTree67.tree_cache hash leaves known
      leavesPC second
  have full : Trace hash image s 191039 221096 3983 4255 known := by
    simpa only [Nat.reduceAdd] using first.trans second
  have same : final = known := Trace.deterministic trace full
  rw [same]
  exact firstFrame.trans secondFrame

#print axioms regular_leaves_cache
#print axioms entry_leaves_cache
#print axioms keygen_root_cache

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenCacheAll67

end

/-! Loaded direct67 keygen succeeds and returns the reference public root. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRunFunctional67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image
private abbrev submission := GroupedBalancedProgram67ByteSign.submission
private abbrev initial (secretKey : SecretKey) := KeygenResource.secretKeyState secretKey

theorem loaded (secretKey : SecretKey) :
    initialState submission .keygen secretKey = some (initial secretKey) := by
  unfold initialState
  rw [if_pos (GroupedBalancedProgram67ByteSign.admissible.2 .keygen)]
  have hd : (submission.image .keygen).data = [] := rfl
  have hb : dataBase (submission.image .keygen) = 0x1000000 := by decide
  simp only [hd,hb,inputBuffers,List.foldl_cons,List.foldl_nil]
  rw [MachineState.writeBytesAsWords]
  rfl

theorem output_word (s : MachineState)
    (pointer : s.getMem 0x81078#64 = 0x82000#64)
    (value : PublicKey)
    (root : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x82000 i.val) =
        value.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (GroupedBalancedKeygenFooterFunctional67.outputState s).getMem
        (Signing.wordAddress 0x40 i.val) =
          value.extractLsb' (64*i.val) 64 := by
  intro i
  fin_cases i
  · rw [GroupedBalancedKeygenFooterFunctional67.output_mem s pointer]
    simpa [Signing.wordAddress] using root ⟨0,by decide⟩
  · rw [GroupedBalancedKeygenFooterFunctional67.output_mem s pointer]
    simpa [Signing.wordAddress] using root ⟨1,by decide⟩

theorem decode_publicKey (s : MachineState) (value : PublicKey)
    (words : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x40 i.val) =
        value.extractLsb' (64*i.val) 64) :
    readBuffer s 0x40 16 = value := by
  apply Memory.readBuffer_of_bytes
  intro i hi
  rw [Signing.getByte_word s 0x40 i (by decide) (by omega),
    words ⟨i/8,by omega⟩]
  exact KeygenNode.extractByte_slice value i

theorem footer_cache (s : MachineState)
    (pointer : s.getMem 0x81078#64 = 0x82000#64)
    (a : Word) (lower : 0x60 ≤ a.toNat) :
    (GroupedBalancedKeygenFooterFunctional67.outputState s).getMem a =
      s.getMem a := by
  have h48 : a ≠ 0x48#64 := by
    intro eq
    rw [eq] at lower
    norm_num at lower
  have h40 : a ≠ 0x40#64 := by
    intro eq
    rw [eq] at lower
    norm_num at lower
  rw [GroupedBalancedKeygenFooterFunctional67.output_mem s pointer]
  simp [h48,h40]

theorem decode_zero_cache (s : MachineState)
    (zero : ∀ a : Word, 0x60 ≤ a.toNat →
      a.toNat < 0x20060 → s.getMem a = 0) :
    readBuffer s 0x60 CACHE_BYTES = KeygenFunctional.zeroCache := by
  apply Memory.readBuffer_of_bytes
  intro i hi
  have hi' : i < 131072 := hi
  rw [Signing.getByte_word s 0x60 i (by decide) (by omega)]
  have lower : 0x60 ≤ (Signing.wordAddress 0x60 (i/8)).toNat := by
    change 0x60 ≤ (0x60+8*(i/8))%2^64
    omega
  have upper : (Signing.wordAddress 0x60 (i/8)).toNat < 0x20060 := by
    change (0x60+8*(i/8))%2^64 < 0x20060
    omega
  rw [zero _ lower upper]
  simp [KeygenFunctional.zeroCache,extractByte]

theorem executes (hash : Hash) (secretKey : SecretKey) :
    ∃ final,
      Executes hash image (initial secretKey) 191050
        ⟨.success,final,221107,3983,4255⟩ ∧
      readBuffer final 0x40 16 =
        GroupedBalancedScheme67.keygen hash secretKey ∧
      readBuffer final 0x60 CACHE_BYTES = KeygenFunctional.zeroCache := by
  obtain ⟨root,first,pc,words,pointer⟩ :=
    GroupedBalancedKeygenLeafFunctionalSafety67.keygen_root
      hash secretKey (initial secretKey)
      (KeygenFunctional.secretKey_pc secretKey)
      (KeygenFunctional.secretKey_word secretKey)
  let final := GroupedBalancedKeygenFooterFunctional67.outputState root
  have second : Executes hash image root 11
      ⟨.success,final,11,0,0⟩ :=
    GroupedBalancedKeygenFooterFunctional67.footer hash root pc pointer
  refine ⟨final,?_,?_,?_⟩
  · simpa only [Nat.reduceAdd,Execution.charge] using
      first.then_executes second
  · exact decode_publicKey final _ (output_word root pointer _ words)
  · apply decode_zero_cache
    intro a lower upper
    rw [footer_cache root pointer a lower,
      GroupedBalancedKeygenCacheAll67.keygen_root_cache hash
        (initial secretKey) root
        (KeygenFunctional.secretKey_pc secretKey) first a upper]
    exact KeygenFunctional.secretKey_zero secretKey a (by omega)

theorem run_exact (hash : Hash) (secretKey : SecretKey) :
    submission.runWith hash .keygen secretKey =
      ⟨some (GroupedBalancedScheme67.keygen hash secretKey,
        KeygenFunctional.zeroCache),true,221107,3983,4255⟩ := by
  obtain ⟨final,trace,pk,cache⟩ := executes hash secretKey
  have run := runWith_of_executes submission hash .keygen secretKey
    (initial secretKey) 191050
    ⟨.success,final,221107,3983,4255⟩ (loaded secretKey)
    trace (by decide)
  rw [run]
  change (⟨some (readBuffer final 0x40 16,
    readBuffer final 0x60 CACHE_BYTES),true,221107,3983,4255⟩ :
      RunResult (PublicKey×Cache)) = _
  rw [pk,cache]
  rfl

theorem run_refines (hash : Hash) (secretKey : SecretKey) :
    ∃ cache : Cache,
      submission.runWith hash .keygen secretKey =
        ⟨some (GroupedBalancedScheme67.keygen hash secretKey,cache),
          true,221107,3983,4255⟩ := by
  exact ⟨KeygenFunctional.zeroCache,run_exact hash secretKey⟩

#print axioms loaded
#print axioms executes
#print axioms run_exact
#print axioms run_refines

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRunFunctional67
