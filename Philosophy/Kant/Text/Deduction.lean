import Philosophy.Kant.Text.Objectivity

universe u v w x y z

namespace Philosophy.Kant.Text

theorem condition_of_possible_experience_implies_objective_validity
    (K : ObjectivitySystem)
    (h : ConditionOfPossibleExperience K) :
    ∀ i, UnifiedInOneConsciousness K.toSynthesisSystem i → ObjectivelyValid K i := by
  exact h.2.2

/-- The abstract Deduction: under the conditions of possible experience, unified
representations are objectively valid. -/
theorem lawful_synthesis_yields_objective_validity
    (K : ObjectivitySystem)
    (h : ConditionOfPossibleExperience K) :
    ∀ i, UnifiedInOneConsciousness K.toSynthesisSystem i → ObjectivelyValid K i := by
  exact condition_of_possible_experience_implies_objective_validity K h

end Philosophy.Kant.Text
