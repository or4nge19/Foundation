import Mathlib

universe u v

namespace Philosophy.Kant.Text.PreCritical

/-- A text-level formulation of the Herz-letter problem of representation and objectivity. -/
structure HerzLetterSystem where
  Object : Type u
  Representation : Type v
  represent : Object → Representation

def DivineUnderstanding (K : HerzLetterSystem) : Prop :=
  Function.Bijective K.represent

def FiniteUnderstanding (K : HerzLetterSystem) : Prop :=
  Function.Injective K.represent

def HerzProblem (K : HerzLetterSystem) : Prop :=
  FiniteUnderstanding K ∧ ¬ DivineUnderstanding K

theorem divine_understanding_implies_finite_understanding
    {K : HerzLetterSystem} (h : DivineUnderstanding K) :
    FiniteUnderstanding K :=
  h.1

end Philosophy.Kant.Text.PreCritical
