import Mathlib

universe u

namespace Philosophy.Kant.Laywine

/-- Logical opposition yields absolute nothingness. -/
theorem nihil_negativum (P : Prop) (hP : P) (hnP : ¬ P) : False :=
  hnP hP

/-- Real opposition yields equilibrium while preserving the reality of each magnitude. -/
theorem nihil_privativum {M : Type u} [AddCommGroup M] (force : M) :
    force + (-force) = 0 :=
  add_neg_cancel force

end Philosophy.Kant.Laywine
