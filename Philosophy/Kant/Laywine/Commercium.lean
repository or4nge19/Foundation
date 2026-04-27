import Mathlib

universe u

namespace Philosophy.Kant.Laywine

/-- A pre-critical system of substances linked by interaction. -/
structure CommerciumSystem where
  Substance : Type u
  interacts : Substance → Substance → Prop

/-- Reciprocal influx is the requirement that interaction be two-sided. -/
def ReciprocalInflux (C : CommerciumSystem) : Prop :=
  ∀ a b, C.interacts a b → C.interacts b a

/-- The world-whole is connected by chains of interaction. -/
def WorldWhole (C : CommerciumSystem) : Prop :=
  ∀ a b, Relation.ReflTransGen C.interacts a b

theorem reciprocal_influx_symm {C : CommerciumSystem}
    (h : ReciprocalInflux C) {a b : C.Substance} :
    C.interacts a b → C.interacts b a :=
  h a b

end Philosophy.Kant.Laywine
