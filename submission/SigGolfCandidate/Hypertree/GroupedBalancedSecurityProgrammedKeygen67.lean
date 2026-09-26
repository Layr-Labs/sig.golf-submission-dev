import SigGolfCandidate.Hypertree.GroupedBalancedSecurityObservedPhases67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphProgrammedTree67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSetupBound67

/-! The concrete keygen observation under the planted graph hash exposes the
designated public top label with the same zero cache and exact call count. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityProgrammedKeygen67
open SigGolf OracleComp Reference
open GroupedBalancedGraphProgrammedReference67
open GroupedBalancedGraphPassive67
set_option maxRecDepth 8192

private abbrev submission := GroupedBalancedProgram67ByteSign.submission

theorem top_label (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) :
    evalWithAnswerFn (programmedGrouped residual secretKey labels)
      (GroupedBalancedSecurityObservedPhases67.view <$>
        submission.run .keygen secretKey) =
      (some (truncate (labels
        (GroupedBalancedSecurityGraph67.upperNode ⟨149, by decide⟩ 0)),
        (0 : Cache)),3983) := by
  rw [GroupedBalancedSecurityObservedPhases67.keygen,
    GroupedBalancedGraphProgrammedTree67.programmed_keygen]

theorem table_root (residual : Hash) (secretKey : SecretKey)
    (table : PointTable) :
    evalWithAnswerFn (programmedGrouped residual secretKey
      (GroupedBalancedGraphMonitorTable67.labelsOf table))
      (GroupedBalancedSecurityObservedPhases67.view <$>
        submission.run .keygen secretKey) =
      (some (GroupedBalancedGraphMonitorSetupBound67.rootPublic table,
        (0 : Cache)),3983) := by
  simpa only [GroupedBalancedGraphMonitorSetupBound67.rootPublic,
    GroupedBalancedGraphMonitorSetupBound67.rootPoint,
    GroupedBalancedGraphMonitorTable67.labelsOf] using
    top_label residual secretKey
      (GroupedBalancedGraphMonitorTable67.labelsOf table)

#print axioms top_label
#print axioms table_root

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityProgrammedKeygen67
