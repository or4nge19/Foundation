import Mathlib

universe u

namespace Philosophy.Kant.Text.PreCritical

/-- A text-level system for the Nova Dilucidatio: ground/consequence and real connection. -/
structure NewElucidationSystem where
  Substance : Type u
  groundOf : Substance → Substance → Prop
  consequenceOf : Substance → Substance → Prop

def RealConnection (K : NewElucidationSystem) (a b : K.Substance) : Prop :=
  K.groundOf a b ∧ K.consequenceOf b a

def ReciprocalGrounding (K : NewElucidationSystem) : Prop :=
  ∀ a b : K.Substance, K.groundOf a b → K.groundOf b a

theorem reciprocal_grounding_symmetric
    {K : NewElucidationSystem} (h : ReciprocalGrounding K)
    {a b : K.Substance} (hab : K.groundOf a b) :
    K.groundOf b a :=
  h a b hab

end Philosophy.Kant.Text.PreCritical
