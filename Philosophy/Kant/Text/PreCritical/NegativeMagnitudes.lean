import Mathlib

universe u

namespace Philosophy.Kant.Text.PreCritical

/-- Logical opposition yields absolute nothingness (Nihil Negativum). -/
theorem nihil_negativum (P : Prop) (hP : P) (hnP : ¬P) : False :=
  hnP hP

/-- Real opposition yields equilibrium while preserving the reality of each magnitude
(Nihil Privativum). -/
theorem nihil_privativum {M : Type u} [AddCommGroup M] (force : M) :
    force + (-force) = 0 :=
  add_neg_cancel force

/-- The distinction: real opposition yields zero (a magnitude), not logical nothingness. -/
theorem real_opposition_yields_magnitude
    {M : Type u} [AddCommGroup M] (force : M) :
    force + (-force) = (0 : M) :=
  nihil_privativum force

end Philosophy.Kant.Text.PreCritical
