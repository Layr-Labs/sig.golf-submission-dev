import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointGlobal67

/-! Both graph contact and H5 conflict are charged inside one sampled run. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointBound67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedGraphIndexJointGlobal67
set_option backward.isDefEq.respectTransparency false
open scoped Classical

theorem graph_bad_le_expected_calls {α : Type}
    (view : QueryCache PointSpec → GroupedBalancedGraphMonitorSignCompiler67.View α)
    (remaining : Nat) :
    Pr[fun result => result.1.bad = true |
      SecurityIndexProgram.execute (global view remaining)] ≤
    expectedValue (SecurityIndexProgram.execute (global view remaining))
      (fun result => (2 * result.1.value.graphCalls : ENNReal)) /
        (2 : ENNReal) ^ 128 := by
  have bound :=
    GroupedBalancedGraphMeteredBound67.bad_le_expected_graph_calls
      view remaining
  rw [← graph_projection view remaining, probEvent_map, expectedValue_map] at bound
  exact bound

theorem h5_conflict_le_expected_draws {α : Type}
    (view : QueryCache PointSpec → GroupedBalancedGraphMonitorSignCompiler67.View α)
    (remaining : Nat) :
    Pr[fun result => SecurityIndexTrace.Conflict result.2 ∧
        SecurityIndexTrace.marks result.2 ≤ LIFETIME |
      SecurityIndexProgram.execute (global view remaining)] ≤
    expectedValue (SecurityIndexProgram.execute (global view remaining))
      (fun result => (result.2.length : ENNReal)) /
        (2 : ENNReal) ^ 128 :=
  SecurityIndexProgram.prob_lifetime_conflict_le _

theorem joint_bad_le_expected_calls {α : Type}
    (view : QueryCache PointSpec → GroupedBalancedGraphMonitorSignCompiler67.View α)
    (remaining : Nat) :
    Pr[fun result => result.1.bad = true ∨
      (SecurityIndexTrace.Conflict result.2 ∧
        SecurityIndexTrace.marks result.2 ≤ LIFETIME) |
      SecurityIndexProgram.execute (global view remaining)] ≤
    expectedValue (SecurityIndexProgram.execute (global view remaining))
      (fun result =>
        ((2 * result.1.value.graphCalls : ENNReal) + result.2.length : ENNReal)) /
          (2 : ENNReal) ^ 128 := by
  let simulation := SecurityIndexProgram.execute (global view remaining)
  have graph := graph_bad_le_expected_calls view remaining
  have h5 := h5_conflict_le_expected_draws view remaining
  calc
    _ ≤ Pr[fun result => result.1.bad = true | simulation] +
        Pr[fun result => SecurityIndexTrace.Conflict result.2 ∧
          SecurityIndexTrace.marks result.2 ≤ LIFETIME | simulation] :=
        probEvent_or_le _ _ _
    _ ≤ expectedValue simulation
          (fun result => (2 * result.1.value.graphCalls : ENNReal)) /
            (2 : ENNReal) ^ 128 +
        expectedValue simulation
          (fun result => (result.2.length : ENNReal)) /
            (2 : ENNReal) ^ 128 := add_le_add graph h5
    _ = _ := by
      rw [← ENNReal.add_div, ← expectedValue_add]

theorem h5_double_lifetime_le_expected_draws {α : Type}
    (view : QueryCache PointSpec → GroupedBalancedGraphMonitorSignCompiler67.View α)
    (remaining : Nat) :
    Pr[fun result => SecurityIndexTrace.Conflict result.2 ∧
        SecurityIndexTrace.marks result.2 ≤ 2 * LIFETIME |
      SecurityIndexProgram.execute (global view remaining)] ≤
    expectedValue (SecurityIndexProgram.execute (global view remaining))
      (fun result => (result.2.length : ENNReal)) /
        (2 : ENNReal) ^ 127 := by
  have bound := SecurityIndexProgram.prob_conflict_le
    (global view remaining) (2 * LIFETIME)
  have ratio : ((2 * LIFETIME : Nat) : ENNReal) /
      (2 : ENNReal) ^ 160 = 1 / (2 : ENNReal) ^ 127 := by
    apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness)
      (by norm_num) (by finiteness)).2
    norm_num [LIFETIME]
  rw [ratio] at bound
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using bound

theorem joint_double_bad_le_expected_total {α : Type}
    (view : QueryCache PointSpec → GroupedBalancedGraphMonitorSignCompiler67.View α)
    (remaining : Nat) :
    Pr[fun result => result.1.bad = true ∨
      (SecurityIndexTrace.Conflict result.2 ∧
        SecurityIndexTrace.marks result.2 ≤ 2 * LIFETIME) |
      SecurityIndexProgram.execute (global view remaining)] ≤
    expectedValue (SecurityIndexProgram.execute (global view remaining))
      (fun result =>
        ((result.1.value.graphCalls : ENNReal) + result.2.length : ENNReal)) /
          (2 : ENNReal) ^ 127 := by
  let simulation := SecurityIndexProgram.execute (global view remaining)
  have graph := graph_bad_le_expected_calls view remaining
  have h5 := h5_double_lifetime_le_expected_draws view remaining
  have graphRatio : (2 : ENNReal) / (2 : ENNReal) ^ 128 =
      1 / (2 : ENNReal) ^ 127 := by
    apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness)
      (by norm_num) (by finiteness)).2
    norm_num
  have graphScaled :
      expectedValue simulation
        (fun result => (2 * result.1.value.graphCalls : ENNReal)) /
          (2 : ENNReal) ^ 128 =
      expectedValue simulation
        (fun result => (result.1.value.graphCalls : ENNReal)) /
          (2 : ENNReal) ^ 127 := by
    simp only [mul_comm (2 : ENNReal), expectedValue_mul_const]
    rw [mul_div_assoc, graphRatio]
    simp only [one_div, one_mul, div_eq_mul_inv]
  calc
    _ ≤ Pr[fun result => result.1.bad = true | simulation] +
        Pr[fun result => SecurityIndexTrace.Conflict result.2 ∧
          SecurityIndexTrace.marks result.2 ≤ 2 * LIFETIME | simulation] :=
        probEvent_or_le _ _ _
    _ ≤ expectedValue simulation
          (fun result => (2 * result.1.value.graphCalls : ENNReal)) /
            (2 : ENNReal) ^ 128 +
        expectedValue simulation
          (fun result => (result.2.length : ENNReal)) /
            (2 : ENNReal) ^ 127 := add_le_add graph h5
    _ = _ := by
      rw [graphScaled, ← ENNReal.add_div, ← expectedValue_add]

#print axioms joint_double_bad_le_expected_total

#print axioms joint_bad_le_expected_calls

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointBound67
