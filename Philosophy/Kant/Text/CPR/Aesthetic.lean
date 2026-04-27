import Mathlib

universe u v w

namespace Philosophy.Kant.Text.CPR

/--
Refactored Aesthetic: Not a collection of types,
but a system of "Setting Out" (Ekthesis).
-/
structure AestheticSystem where
  Appearance : Type u
  -- The "Rhapsody": the many before synthesis (B195)
  Manifold   : Appearance → Type v

  -- Space and Time as the "Grid"
  TimeLine : Type w
  /-- Space is the order of simultaneity (The Perpendiculars) -/
  SimultaneityGrid : TimeLine → Type w

  /--
  Ekthesis: The mind "sketches" an appearance by mapping its manifold
  onto the toothed-comb of time and space.
  -/
  ekthesis : (a : Appearance) → (Manifold a) → (t : TimeLine) × (SimultaneityGrid t) → Prop

/--
Laywine's "Cartography" Axiom:
Every part of every appearance must be uniquely locatable on the shared map.
-/
def IsCosmologicallyUnified (K : AestheticSystem) : Prop :=
  ∀ a : K.Appearance, ∀ m : K.Manifold a,
    ∃! coords, K.ekthesis a m coords

/--
Empirical Reality:
The map is "real" because it is the only way objects can be given to us.
-/
def EmpiricalReality (K : AestheticSystem) : Prop :=
  IsCosmologicallyUnified K

/--
Transcendental Ideality:
The map is "ideal" because the 'SimultaneityGrid' and 'TimeLine'
derive their unity from the mind's own Principium of Disposition.
-/
def TranscendentalIdeality (K : AestheticSystem) (legislatedByMind : Prop) : Prop :=
  legislatedByMind → (EmpiricalReality K)

end Philosophy.Kant.Text.CPR
