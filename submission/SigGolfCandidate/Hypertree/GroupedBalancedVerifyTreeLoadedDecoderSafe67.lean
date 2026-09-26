import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreePrefixSafe67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Base67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeDecoderHandoff67
import SigGolfCandidate.Hypertree.GroupedBalancedSignByteFullMemFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsLeafPath67

/-! The loaded verifier reaches the decoder with its embedded tables and stack intact. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeLoadedDecoderSafe67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyTreeHighFrame67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67Byte.submission
private abbrev Low := GroupedBalancedVerifyStackGlobal67.LowFrame

private theorem high_ne (a : Word) (ha : 0x90000 ≤ a.toNat)
    (b : Nat) (hb : b < 0x90000) : a ≠ BitVec.ofNat 64 b := by
  intro eq
  have hn := congrArg BitVec.toNat eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : b < 2^64)] at hn
  omega

theorem post_safe (s : MachineState) :
    SafeFrame s (GroupedBalancedVerifyTreePost67.postState s) := by
  constructor
  · intro a ha
    exact GroupedBalancedVerifyTreePost67.post_mem s a
      (high_ne a ha 0x81058 (by decide))
      (high_ne a ha 0x81060 (by decide))
  · exact GroupedBalancedVerifyTreePost67.post_stack s

theorem post_low (s : MachineState) :
    Low s (GroupedBalancedVerifyTreePost67.postState s) := by
  intro a low
  exact GroupedBalancedVerifyTreePost67.post_mem s a
    (GroupedBalancedVerifyStackGlobal67.low_ne a low 0x81058
      (by decide) (by decide))
    (GroupedBalancedVerifyStackGlobal67.low_ne a low 0x81060
      (by decide) (by decide))

theorem call_safe (s : MachineState) :
    SafeFrame s (GroupedBalancedVerifyTreePost67.callState s) := by
  constructor
  · intro a _
    exact GroupedBalancedVerifyTreePost67.call_mem s a
  · simp [GroupedBalancedVerifyTreePost67.callState,execInstrBr,
      MachineState.getReg_setReg_ne]

theorem call_low (s : MachineState) :
    Low s (GroupedBalancedVerifyTreePost67.callState s) := by
  intro a _
  exact GroupedBalancedVerifyTreePost67.call_mem s a

theorem loaded_call_safe (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial n called,
      initialState program .verify input = some initial ∧
      n ≤ 1857 ∧
      Trace hash image initial n (n+92) 12 13 called ∧
      called.pc = 0x1a4c ∧
      called.getReg .x1 = 0x1518 ∧
      SafeFrame initial called ∧
      called.getMem 0x81048 = GroupedBalancedVerifyTreeH4Fold67.ptrAt 10 ∧
      called.getMem 0x81058 = 0 ∧ called.getMem 0x81060 = 3 ∧
      called.getMem 0x81000 = 10 ∧
      Low initial called := by
  obtain ⟨initial,start,loaded,startRun,startPC,startSafe,
    pointer,counter,base,startLow⟩ :=
    GroupedBalancedVerifyTreePrefixSafe67.loaded_tree_start_safe hash input
  obtain ⟨n,tree,nBound,treeRun,treePC,treePointer,_,treeBase,treeSafe,
    treeLow⟩ :=
    GroupedBalancedVerifyTreeH4Base67.ten_rounds_base hash start
      startPC pointer counter
  let post := GroupedBalancedVerifyTreePost67.postState tree
  let called := GroupedBalancedVerifyTreePost67.callState post
  have postRun := GroupedBalancedVerifyTreePost67.post_steps tree treePC
  have postPC := GroupedBalancedVerifyTreePost67.post_pc tree treePC
  have callRun := GroupedBalancedVerifyTreePost67.call_step post postPC
  obtain ⟨ctrl58,ctrl60⟩ := GroupedBalancedVerifyTreePost67.post_controls tree
  refine ⟨initial,n+227,called,loaded,by omega,?_,
    GroupedBalancedVerifyTreePost67.call_pc post postPC,
    GroupedBalancedVerifyTreePost67.call_link post postPC,
    safe_trans (safe_trans (safe_trans startSafe treeSafe) (post_safe tree))
      (call_safe post),?_,?_,?_,?_,
      (startLow.trans treeLow).trans ((post_low tree).trans (call_low post))⟩
  · have all := (startRun.trans treeRun).trans
      (postRun.trace.trans callRun.trace)
    simpa [image,called,post,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all
  · rw [GroupedBalancedVerifyTreePost67.call_mem,
      GroupedBalancedVerifyTreePost67.post_mem tree 0x81048
        (by decide) (by decide),treePointer]
  · rw [GroupedBalancedVerifyTreePost67.call_mem,ctrl58]
  · rw [GroupedBalancedVerifyTreePost67.call_mem,ctrl60]
  · rw [GroupedBalancedVerifyTreePost67.call_mem,
      GroupedBalancedVerifyTreePost67.post_mem tree 0x81000
        (by decide) (by decide),treeBase,base]
    decide

theorem decoder_mem_other (s : MachineState) (message : Reference.Digest)
    (a : Word)
    (outside : a.toNat < 0x80600 ∨ 0x80648 ≤ a.toNat) :
    (GroupedBalancedVerifyByteFull67.fullDecoderState s message).getMem a =
      s.getMem a := by
  have hflag : a ≠ (0x80640 : Word) := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rcases outside with lo | hi <;> simp at hn <;> omega
  have hcopy : ∀ k, k < 16 →
      a ≠ alignToDword (BitVec.ofNat 64 (0x80600+4*k)) := by
    intro k hk eq
    have hn := congrArg BitVec.toNat eq
    have hv : (alignToDword (BitVec.ofNat 64 (0x80600+4*k))).toNat =
        0x80600 + 8*(k/2) := by
      interval_cases k <;> decide
    rw [hv] at hn
    rcases outside with lo | hi <;> omega
  exact GroupedBalancedSignByteFullMemFrame67.fullDecoder_mem s message a
    hflag hcopy

theorem loaded_decoder (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial called final n,
      initialState program .verify input = some initial ∧
      n ≤ 2137 ∧
      Trace hash image initial n (n+92) 12 13 final ∧
      final.pc = 0x1518 ∧
      (∀ chain : Fin 67,
        final.getByte (BitVec.ofNat 64 (0x80600+chain.val)) =
          BitVec.ofNat 8
            (GroupedBalancedChecksum67.digit
              (GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot called) chain).val) ∧
      GroupedBalancedVerifyByteContract67.Tables final ∧
      (∀ a : Word, a.toNat < 0x80600 ∨ 0x80648 ≤ a.toNat →
        final.getMem a = called.getMem a) ∧
      final.getMem 0x81048 = GroupedBalancedVerifyTreeH4Fold67.ptrAt 10 ∧
      final.getMem 0x81058 = 0 ∧ final.getMem 0x81060 = 3 ∧
      final.getMem 0x81000 = 10 ∧
      Low initial final := by
  obtain ⟨initial,n,called,loaded,nBound,run,pc,link,safe,
    pointer,count,height,base,calledLow⟩ :=
    loaded_call_safe hash input
  have stack : called.getReg .x2 = 0xfff700 :=
    safe.2.trans (GroupedBalancedVerifyEntry67.loaded_sp input initial loaded)
  have tables : GroupedBalancedVerifyByteContract67.Tables called :=
    tables_of_high safe.1
      (GroupedBalancedVerifyByteContract67.initial_tables input initial loaded)
  let root := GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot called
  let final := GroupedBalancedVerifyByteFull67.fullDecoderState called root
  obtain ⟨decodeRun,digits,endPC,finalTables⟩ :=
    GroupedBalancedVerifyTreeDecoderHandoff67.decode_from_call called pc stack link tables
  let d := 8+112+(if GroupedBalancedQuaternary.rawSum root < 96 then 9 else 10)+144+6
  have memFrame : ∀ a : Word,
      a.toNat < 0x80600 ∨ 0x80648 ≤ a.toNat → final.getMem a = called.getMem a := by
    intro a outside
    exact decoder_mem_other called root a outside
  refine ⟨initial,called,final,n+d,loaded,?_,?_,endPC,digits,
    finalTables,memFrame,?_,?_,?_,?_,?_⟩
  · dsimp [d]
    split_ifs <;> omega
  · have all := run.trans decodeRun.trace
    simpa [d,root,final,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all
  · exact (memFrame 0x81048 (Or.inr (by decide))).trans pointer
  · exact (memFrame 0x81058 (Or.inr (by decide))).trans count
  · exact (memFrame 0x81060 (Or.inr (by decide))).trans height
  · exact (memFrame 0x81000 (Or.inr (by decide))).trans base
  · exact calledLow.trans (by
      intro a low
      exact memFrame a (Or.inl (by omega)))

def currentIndex (s : MachineState) : BitVec 192 :=
  s.getMem 0x81018 ++ s.getMem 0x81010 ++ s.getMem 0x81008

theorem current_index_words (s : MachineState) :
    GroupedBalancedByteFastEdgeIndexRefine67.StoredIndex s (currentIndex s) := by
  intro i
  fin_cases i
  · change s.getMem 0x81008 =
      ((s.getMem 0x81018 ++ s.getMem 0x81010) ++ s.getMem 0x81008).extractLsb' 0 64
    exact BitVec.extractLsb'_append_eq_right.symm
  · change s.getMem 0x81010 =
      ((s.getMem 0x81018 ++ s.getMem 0x81010) ++ s.getMem 0x81008).extractLsb' 64 64
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 64)]
    simpa only [Nat.sub_self] using
      (BitVec.extractLsb'_append_eq_right (a := s.getMem 0x81018)
        (b := s.getMem 0x81010)).symm
  · change s.getMem 0x81018 =
      ((s.getMem 0x81018 ++ s.getMem 0x81010) ++ s.getMem 0x81008).extractLsb' 128 64
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 128)]
    simpa only [Nat.reduceSub] using
      (BitVec.extractLsb'_append_eq_left (a := s.getMem 0x81018)
        (b := s.getMem 0x81010)).symm

def witnessDigest (s : MachineState) (chain : Fin 67) : Reference.Digest :=
  s.getMem (BitVec.ofNat 64 (0x2c7d0+16*chain.val+8)) ++
  s.getMem (BitVec.ofNat 64 (0x2c7d0+16*chain.val))

theorem witness_words (s : MachineState) :
    GroupedBalancedByteFastChainReady67.WitnessWords
      s 0x2c7d0 (witnessDigest s) := by
  intro chain half
  fin_cases half
  · change s.getMem (BitVec.ofNat 64 (0x2c7d0+16*chain.val)) =
      (witnessDigest s chain).extractLsb' 0 64
    exact BitVec.extractLsb'_append_eq_right.symm
  · change s.getMem (BitVec.ofNat 64 (0x2c7d0+16*chain.val+8)) =
      (witnessDigest s chain).extractLsb' 64 64
    exact BitVec.extractLsb'_append_eq_left.symm

theorem safe_witnesses :
    GroupedBalancedByteFastChainReady67.SafeWitnesses 0x2c7d0 := by
  intro chain half
  have hc := chain.isLt
  fin_cases half
  · simp [GroupedBalancedByteFastChainReady67.witnessAddress,
      accessValid,rangeValid,MEMORY_BYTES,BitVec.toNat_ofNat]
    omega
  · simp [GroupedBalancedByteFastChainReady67.witnessAddress,
      accessValid,rangeValid,MEMORY_BYTES,BitVec.toNat_ofNat]
    omega

def siblingDigest (s : MachineState) (j : Nat) : Reference.Digest :=
  s.getMem (BitVec.ofNat 64 (0x2c7d0+16*67+16*j+8)) ++
  s.getMem (BitVec.ofNat 64 (0x2c7d0+16*67+16*j))

theorem sibling_words (s : MachineState) :
    ∀ j, j < 3 → ∀ half : Fin 2,
      s.getMem (BitVec.ofNat 64 (0x2c7d0+16*67+16*j+8*half.val)) =
        (siblingDigest s j).extractLsb' (64*half.val) 64 := by
  intro j _ half
  fin_cases half
  · change s.getMem (BitVec.ofNat 64 (0x2c7d0+16*67+16*j)) =
      (siblingDigest s j).extractLsb' 0 64
    exact BitVec.extractLsb'_append_eq_right.symm
  · change s.getMem (BitVec.ofNat 64 (0x2c7d0+16*67+16*j+8)) =
      (siblingDigest s j).extractLsb' 64 64
    exact BitVec.extractLsb'_append_eq_left.symm

theorem path_from_decoder (hash : Hash) (s : MachineState)
    (message : Reference.Digest)
    (pc : s.pc = 0x1518)
    (pointer : s.getMem 0x81048 = 0x2c7d0)
    (height : s.getMem 0x81060 = 3)
    (tables : GroupedBalancedVerifyByteContract67.Tables s)
    (digits : GroupedBalancedByteFastWotsFrame67.Digits s message)
    (baseSmall : (s.getMem 0x81000).toNat < 256) :
    ∃ final steps cycles,
      Trace hash image s
        (4*GroupedBalancedChecksum67.suffixCost message+1281+steps)
        (11*GroupedBalancedChecksum67.suffixCost message+1281+cycles)
        (GroupedBalancedChecksum67.suffixCost message+4)
        (GroupedBalancedChecksum67.suffixCost message+21) final ∧
      final.pc = 0x19c4 ∧
      (∀ half : Fin 2,
        final.getMem (Signing.wordAddress 0x80500 half.val) =
          (GroupedBalancedByteFastUpperPathIter67.rootAt hash
            (s.getMem 0x81000).toNat (currentIndex s).toNat
            (GroupedBalancedUpperTree67.compressLeaf hash
              (s.getMem 0x81000).toNat (currentIndex s).toNat
              (GroupedBalancedByteFastEndpointAccum67.expectedEndpoint hash
                (s.getMem 0x81000).toNat (currentIndex s).toNat
                message (witnessDigest s)))
            (siblingDigest s) 3).extractLsb' (64*half.val) 64) ∧
      final.getMem 0x81048 = 0x2cc30 ∧
      final.getMem 0x81050 = 3 ∧
      final.getMem 0x81060 = 3 ∧
      final.getMem 0x81000 =
        BitVec.ofNat 64 ((s.getMem 0x81000).toNat+3) ∧
      GroupedBalancedByteFastEdgeIndexRefine67.StoredIndex final
        (BitVec.ofNat 192 ((currentIndex s).toNat/8)) ∧
      final.getMem 0x81058 = s.getMem 0x81058 ∧
      (∀ a : Word, a.toNat < 0x80000 → final.getMem a = s.getMem a) ∧
      cycles ≤ 718 := by
  have index : GroupedBalancedByteFastEdgeIndexRefine67.StoredIndex s
      (BitVec.ofNat 192 (currentIndex s).toNat) := by
    simpa using current_index_words s
  have baseWord : s.getMem 0x81000 =
      BitVec.ofNat 64 (s.getMem 0x81000).toNat := by simp
  have leafBound : (currentIndex s).toNat < 2^192 := (currentIndex s).isLt
  have startWord : s.getMem 0x81048 = BitVec.ofNat 64 0x2c7d0 := by
    simpa using pointer
  have heightWord : s.getMem 0x81060 = BitVec.ofNat 64 3 := by
    simpa using height
  obtain ⟨final,steps,cycles,run,endPC,root,finalPtr,finalCount,
    finalHeight,finalLevel,finalIndex,group,low,_,bound⟩ :=
    GroupedBalancedVerifyWotsLeafPath67.run_wots_leaf_path hash s
      (s.getMem 0x81000).toNat (currentIndex s).toNat 0x2c7d0 3 message
      (witnessDigest s) (siblingDigest s) pc baseWord index
      startWord heightWord safe_witnesses (witness_words s) tables digits
      (sibling_words s) (Or.inl rfl) (by decide) (by decide)
      baseSmall leafBound
  refine ⟨final,steps,cycles,?_,endPC,root,?_,finalCount,finalHeight,
    finalLevel,?_,group,low,?_⟩
  · simpa only [Nat.reduceAdd] using run
  · simpa [show (0x2c7d0 + 16*67 + 16*3 : Nat) = 0x2cc30 by decide]
      using finalPtr
  · simpa only [Nat.reducePow, Nat.reduceDiv] using finalIndex
  · omega

def firstGroupRoot (hash : Hash) (called decoded : MachineState) :
    Reference.Digest :=
  GroupedBalancedByteFastUpperPathIter67.rootAt hash 10
    (currentIndex decoded).toNat
    (GroupedBalancedUpperTree67.compressLeaf hash 10
      (currentIndex decoded).toNat
      (GroupedBalancedByteFastEndpointAccum67.expectedEndpoint hash 10
        (currentIndex decoded).toNat
        (GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot called)
        (witnessDigest decoded)))
    (siblingDigest decoded) 3

theorem loaded_first_group (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial called decoded final n steps cycles,
      initialState program .verify input = some initial ∧
      n ≤ 2137 ∧ cycles ≤ 718 ∧
      Trace hash image initial
        (n + (4*GroupedBalancedChecksum67.suffixCost
          (GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot called)+1281+steps))
        (n+92 + (11*GroupedBalancedChecksum67.suffixCost
          (GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot called)+1281+cycles))
        (GroupedBalancedChecksum67.suffixCost
          (GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot called)+16)
        (GroupedBalancedChecksum67.suffixCost
          (GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot called)+34)
        final ∧
      final.pc = 0x19c4 ∧
      (∀ half : Fin 2,
        final.getMem (Signing.wordAddress 0x80500 half.val) =
          (firstGroupRoot hash called decoded).extractLsb' (64*half.val) 64) ∧
      final.getMem 0x81048 = 0x2cc30 ∧
      final.getMem 0x81000 = 13 ∧
      final.getMem 0x81058 = 0 ∧
      final.getMem 0x81060 = 3 ∧
      (∀ a : Word, a.toNat < 0x80000 →
        final.getMem a = decoded.getMem a) ∧
      Low initial final := by
  obtain ⟨initial,called,decoded,n,loaded,nBound,prefixRun,pc,digits,tables,
    _,pointer,group,height,base,decodedLow⟩ := loaded_decoder hash input
  have pointerValue : decoded.getMem 0x81048 = 0x2c7d0 := by
    simpa [GroupedBalancedVerifyTreeH4Fold67.ptrAt] using pointer
  have baseSmall : (decoded.getMem 0x81000).toNat < 256 := by
    rw [base]
    decide
  obtain ⟨final,steps,cycles,path,endPC,root,finalPtr,_,finalHeight,
    finalBase,_,groupCarry,low,cycleBound⟩ :=
    path_from_decoder hash decoded
      (GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot called)
      pc pointerValue height tables digits baseSmall
  have rootValue : ∀ half : Fin 2,
      final.getMem (Signing.wordAddress 0x80500 half.val) =
        (firstGroupRoot hash called decoded).extractLsb' (64*half.val) 64 := by
    intro half
    have val : (decoded.getMem 0x81000).toNat = 10 := by
      rw [base]
      decide
    simpa only [firstGroupRoot,val] using root half
  refine ⟨initial,called,decoded,final,n,steps,cycles,loaded,nBound,
    cycleBound,?_,endPC,rootValue,finalPtr,?_,?_,finalHeight,low,
    decodedLow.trans low⟩
  · have all := prefixRun.trans path
    convert all using 1 <;> omega
  · have val : (decoded.getMem 0x81000).toNat = 10 := by
      rw [base]
      decide
    rw [val] at finalBase
    simpa using finalBase
  · exact groupCarry.trans group

theorem loaded_group_entry (hash : Hash)
    (input : Input program.sizes .verify) :
    ∃ initial entry n,
      initialState program .verify input = some initial ∧
      n ≤ 1856 ∧
      Trace hash image initial n (n+92) 12 13 entry ∧
      entry.pc = 0x1514 ∧
      entry.getReg .x2 = 0xfff700 ∧
      GroupedBalancedVerifyByteContract67.Tables entry ∧
      Low initial entry ∧
      entry.getMem 0x81048 = 0x2c7d0 ∧
      entry.getMem 0x81058 = 0 ∧
      entry.getMem 0x81060 = 3 ∧
      entry.getMem 0x81000 = 10 := by
  obtain ⟨initial,start,loaded,startRun,startPC,startSafe,
    pointer,counter,base,startLow⟩ :=
    GroupedBalancedVerifyTreePrefixSafe67.loaded_tree_start_safe hash input
  obtain ⟨m,tree,mBound,treeRun,treePC,treePointer,_,treeBase,treeSafe,
    treeLow⟩ :=
    GroupedBalancedVerifyTreeH4Base67.ten_rounds_base hash start
      startPC pointer counter
  let entry := GroupedBalancedVerifyTreePost67.postState tree
  have postRun := GroupedBalancedVerifyTreePost67.post_steps tree treePC
  have postPC := GroupedBalancedVerifyTreePost67.post_pc tree treePC
  have safe := safe_trans (safe_trans startSafe treeSafe) (post_safe tree)
  have low := (startLow.trans treeLow).trans (post_low tree)
  obtain ⟨group,height⟩ := GroupedBalancedVerifyTreePost67.post_controls tree
  refine ⟨initial,entry,m+226,loaded,by omega,?_,postPC,?_,?_,low,
    ?_,group,height,?_⟩
  · have all := (startRun.trans treeRun).trans postRun.trace
    simpa [entry,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all
  · exact safe.2.trans
      (GroupedBalancedVerifyEntry67.loaded_sp input initial loaded)
  · exact tables_of_high safe.1
      (GroupedBalancedVerifyByteContract67.initial_tables input initial loaded)
  · rw [GroupedBalancedVerifyTreePost67.post_mem tree 0x81048
      (by decide) (by decide),treePointer]
    decide
  · rw [GroupedBalancedVerifyTreePost67.post_mem tree 0x81000
      (by decide) (by decide),treeBase,base]
    decide

#print axioms loaded_call_safe
#print axioms loaded_decoder
#print axioms loaded_first_group
#print axioms loaded_group_entry
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeLoadedDecoderSafe67
