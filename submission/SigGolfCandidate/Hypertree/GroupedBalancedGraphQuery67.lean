import SigGolfCandidate.Hypertree.GroupedBalancedGraphSampling67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphProgramming67

/-! Lookup at the grouped graph cache parses only the public address. Thus an
arbitrary query has at most one possible canonical label contact. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphQuery67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPayload67 GroupedBalancedGraphOrder67
open GroupedBalancedGraphSampling67 GroupedBalancedGraphCausality67 GroupedBalancedGraphProgramming67
open scoped Classical

noncomputable def locate (query : Query) : Option Position :=
  if found : ∃ position : Position, ∃ data : List Byte,
      position.input data = query
  then some found.choose else none

theorem locate_address (position : Position) (data : List Byte) :
    locate (position.input data) = some position := by
  unfold locate
  split
  next found =>
    obtain ⟨otherData, equal⟩ := found.choose_spec
    have same : found.choose = position := by
      apply Subtype.ext
      exact SecurityGraph.Address.eq_of_input_eq equal
    rw [same]
  next absent => exact False.elim (absent ⟨position, data, rfl⟩)

theorem locate_input (privateAnswers : PrivateAnswers)
    (labels : GroupedBalancedSecurityGraph67.Labels) (position : Position) :
    locate (graphInput privateAnswers labels position) = some position :=
  locate_address position (payload privateAnswers labels position)

theorem locate_programmed (data : Position → List Byte)
    (labels : GroupedBalancedSecurityGraph67.Labels) (residual : Hash)
    (query : Query) :
    programmed data labels residual query =
      match locate query with
      | none => residual query
      | some position => if query = position.input (data position)
          then labels position else residual query := by
  unfold GroupedBalancedGraphProgramming67.programmed GroupedGraphProgramming.programmed
  split
  next found =>
    have located : locate query = some found.choose := by
      exact (congrArg locate found.choose_spec).symm.trans
        (locate_address found.choose (data found.choose))
    simp only [located, if_pos found.choose_spec.symm]
  next absent =>
    cases located : locate query with
    | none => rfl
    | some position =>
        have different : query ≠ position.input (data position) :=
          fun same => absent ⟨position, same.symm⟩
        simp only [if_neg different]

theorem graphCache_outside (privateAnswers : PrivateAnswers)
    (positions : List Position) (labels : GroupedBalancedSecurityGraph67.Labels)
    (cache : QueryCache HashSpec) (query : Query)
    (outside : ∀ position ∈ positions,
      query ≠ graphInput privateAnswers labels position) :
    graphCache privateAnswers positions labels cache query = cache query := by
  induction positions generalizing cache with
  | nil => rfl
  | cons position rest ih =>
      rw [graphCache, ih _
        (fun other member => outside other (List.mem_cons_of_mem _ member))]
      exact QueryCache.cacheQuery_of_ne cache _ (outside position (by simp))

theorem graphCache_inside (privateAnswers : PrivateAnswers)
    (positions : List Position) (labels : GroupedBalancedSecurityGraph67.Labels)
    (cache : QueryCache HashSpec) (position : Position)
    (member : position ∈ positions) :
    graphCache privateAnswers positions labels cache
      (graphInput privateAnswers labels position) =
      some (labels position) := by
  induction positions generalizing cache with
  | nil => simp at member
  | cons first rest ih =>
      by_cases occurs : position ∈ rest
      · exact ih _ occurs
      · have same : position = first :=
          (List.mem_cons.mp member).resolve_right occurs
        subst first
        rw [graphCache, graphCache_outside]
        · exact QueryCache.cacheQuery_self _ _ _
        · intro other otherMember equal
          have same : position = other := by
            apply Subtype.ext
            exact SecurityGraph.Address.eq_of_input_eq equal
          exact occurs (same ▸ otherMember)

theorem complete_cache_lookup (privateAnswers : PrivateAnswers)
    (labels : GroupedBalancedSecurityGraph67.Labels) (query : Query) :
    graphCache privateAnswers positions labels ∅ query =
      match locate query with
      | none => none
      | some position => if query = graphInput privateAnswers labels position
          then some (labels position) else none := by
  cases located : locate query with
  | none =>
      apply graphCache_outside
      intro position _ same
      have wrong := locate_input privateAnswers labels position
      rw [← same, located] at wrong
      cases wrong
  | some position =>
      by_cases same : query = graphInput privateAnswers labels position
      · simp only [if_pos same]
        rw [same]
        exact graphCache_inside privateAnswers positions labels ∅ position
          (positions_complete position)
      · simp only [if_neg same]
        apply graphCache_outside
        intro other _ equal
        have otherLocated := locate_input privateAnswers labels other
        rw [← equal, located] at otherLocated
        have positionsEqual := Option.some.inj otherLocated
        exact same (positionsEqual ▸ equal)

end SigGolfCandidate.Hypertree.GroupedBalancedGraphQuery67
