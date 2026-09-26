import SigGolfCandidate.Hypertree.GroupedAddressDomains

/-!
The public random-oracle graph for grouped signatures is indexed by the
serialized query address. A graph coordinate covers every public chain,
leaf, and node domain (tags 2, 3, and 4). Using the address as the coordinate
makes input separation independent of the payload and of the order in which
the graph is evaluated.

This module proves the domain and lazy-sampling infrastructure. The canonical
payload recursion and its coupling to the grouped signer are separate steps.
-/

namespace SigGolfCandidate.Hypertree.GroupedSecurityGraph
open SigGolf OracleComp OracleSpec Reference SecurityRandomOracle SecurityGraph

abbrev Position := {address : Address //
  address.tag.val = 2 ∨ address.tag.val = 3 ∨ address.tag.val = 4}

def Position.input (position : Position) (payload : List Byte) : Query :=
  position.val.input payload

theorem Position.input_separated (first second : Position)
    (different : first ≠ second) (payload payload' : List Byte) :
    first.input payload ≠ second.input payload' := by
  intro same
  apply different
  apply Subtype.ext
  exact Address.eq_of_input_eq same

theorem source_input_separated (source : Address) (sourceTag : source.tag.val = 1)
    (position : Position) (privatePayload publicPayload : List Byte) :
    source.input privatePayload ≠ position.input publicPayload := by
  intro same
  have addressEq : source = position.val := Address.eq_of_input_eq same
  have tagEq := congrArg (fun address : Address => address.tag.val) addressEq
  rcases position.property with tagTwo | tagThree | tagFour
  · omega
  · omega
  · omega

private theorem lift160_toNat (value : BitVec 160) :
    (BitVec.ofNat 192 value.toNat).toNat = value.toNat := by
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (GroupedBottomIndex.index_fits_tree_field value)]

def bottomLeaf (index : BitVec 160) : Position :=
  ⟨⟨2, 0, BitVec.ofNat 192 index.toNat, 0, 0, 0⟩, Or.inl rfl⟩

def bottomNode (level : Fin 10) (tree : BitVec 160) : Position :=
  ⟨⟨4, ⟨level.val, by omega⟩, BitVec.ofNat 192 tree.toNat, 0, 0, 0⟩,
    Or.inr (Or.inr rfl)⟩

def upperChain (base : Fin 150) (leaf : BitVec 160)
    (chain : Fin 52) (step : Fin 5) : Position :=
  ⟨⟨2, ⟨base.val + 10, by omega⟩, BitVec.ofNat 192 leaf.toNat,
    0, ⟨chain.val, by omega⟩, ⟨step.val, by omega⟩⟩, Or.inl rfl⟩

def upperLeaf (base : Fin 150) (leaf : BitVec 160) : Position :=
  ⟨⟨3, ⟨base.val + 10, by omega⟩, BitVec.ofNat 192 leaf.toNat,
    0, 0, 0⟩, Or.inr (Or.inl rfl)⟩

def upperNode (level : Fin 150) (tree : BitVec 160) : Position :=
  ⟨⟨4, ⟨level.val + 10, by omega⟩, BitVec.ofNat 192 tree.toNat,
    0, 0, 0⟩, Or.inr (Or.inr rfl)⟩

theorem bottom_leaf_input (index : BitVec 160) (payload : List Byte) :
    (bottomLeaf index).input payload =
      addressedInput 2 0 index.toNat 0 0 0 payload := by
  simp only [Position.input, bottomLeaf, Address.input]
  rw [lift160_toNat]
  rfl

theorem bottom_node_input (level : Fin 10) (tree : BitVec 160)
    (payload : List Byte) :
    (bottomNode level tree).input payload =
      addressedInput 4 level.val tree.toNat 0 0 0 payload := by
  simp only [Position.input, bottomNode, Address.input]
  rw [lift160_toNat]
  rfl

theorem upper_chain_input (base : Fin 150) (leaf : BitVec 160)
    (chain : Fin 52) (step : Fin 5) (payload : List Byte) :
    (upperChain base leaf chain step).input payload =
      addressedInput 2 (base.val + 10) leaf.toNat 0 chain.val step.val payload := by
  simp only [Position.input, upperChain, Address.input]
  rw [lift160_toNat]
  rfl

theorem upper_leaf_input (base : Fin 150) (leaf : BitVec 160)
    (payload : List Byte) :
    (upperLeaf base leaf).input payload =
      addressedInput 3 (base.val + 10) leaf.toNat 0 0 0 payload := by
  simp only [Position.input, upperLeaf, Address.input]
  rw [lift160_toNat]
  rfl

theorem upper_node_input (level : Fin 150) (tree : BitVec 160)
    (payload : List Byte) :
    (upperNode level tree).input payload =
      addressedInput 4 (level.val + 10) tree.toNat 0 0 0 payload := by
  simp only [Position.input, upperNode, Address.input]
  rw [lift160_toNat]
  rfl

abbrev Labels := Position → BitVec 256

def readGraph (payload : Labels → Position → List Byte) :
    List Position → Labels → OracleComp HashSpec Labels
  | [], labels => pure labels
  | position :: rest, labels => do
      let answer ← HashSpec.query (position.input (payload labels position))
      readGraph payload rest (Function.update labels position answer)

noncomputable def sampleGraph (payload : Labels → Position → List Byte) :
    List Position → Labels → QueryCache HashSpec →
      ProbComp (Labels × QueryCache HashSpec)
  | [], labels, cache => pure (labels, cache)
  | position :: rest, labels, cache => do
      let answer ← $ᵗ BitVec 256
      sampleGraph payload rest (Function.update labels position answer)
        (cache.cacheQuery (position.input (payload labels position)) answer)

theorem run_readGraph_eq_sampleGraph (payload : Labels → Position → List Byte)
    (positions : List Position) (distinct : positions.Nodup) (labels : Labels)
    (cache : QueryCache HashSpec)
    (fresh : ∀ position ∈ positions, ∀ values,
      cache (position.input (payload values position)) = none) :
    (simulateQ (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp))
      (readGraph payload positions labels)).run cache =
      sampleGraph payload positions labels cache := by
  induction positions generalizing labels cache with
  | nil => rfl
  | cons position rest ih =>
      obtain ⟨notRest, restDistinct⟩ := List.nodup_cons.mp distinct
      simp only [readGraph, simulateQ_bind, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind]
      rw [randomOracle.run_eq, fresh position (by simp) labels]
      simp only [bind_assoc, pure_bind, sampleGraph]
      apply bind_congr
      intro answer
      apply ih restDistinct
      intro other member values
      have different : other ≠ position := fun h => notRest (h ▸ member)
      rw [QueryCache.cacheQuery_of_ne _ _
        (Position.input_separated other position different _ _)]
      exact fresh other (List.mem_cons_of_mem _ member) values

end SigGolfCandidate.Hypertree.GroupedSecurityGraph
