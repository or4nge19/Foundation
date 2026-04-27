import Philosophy.Kant.Text.PreCritical.DuisburgNachlass
import Philosophy.Kant.Text.CPR.Analytic.TranscendentalDeductionB

namespace Philosophy.Kant.Text.Bridges

open Philosophy.Kant.Text
open Philosophy.Kant.Text.PreCritical
open Philosophy.Kant.Text.CPR.Analytic

/-- A bridge thesis from the Duisburg functions of apperception to the critical
architecture of objective unity. -/
def PreCriticalToCriticalBridge
    (F : FunctionOfApperception → RelationForm)
    (K : DeductionB_System) : Prop :=
  (F .inherence = .categorical ∧
    F .dependence = .hypothetical ∧
    F .composition = .disjunctive) ∧
  ObjectiveUnityOfApperception K

theorem precritical_to_critical_preserves_relation_forms
    (K : DeductionB_System) :
    PreCriticalToCriticalBridge functionToRelationForm K →
      functionToRelationForm .inherence = .categorical := by
  intro h
  exact h.1.1

theorem precritical_to_critical_supports_objective_unity
    (K : DeductionB_System) :
    PreCriticalToCriticalBridge functionToRelationForm K →
      ObjectiveUnityOfApperception K := by
  intro h
  exact h.2

end Philosophy.Kant.Text.Bridges
