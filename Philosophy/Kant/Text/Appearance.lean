import Mathlib

universe u v w

namespace Philosophy.Kant.Text

/--
The "Rhapsody of Perceptions" (B195).
A state of appearances before the understanding has legislated order.
-/
structure AppearanceSystem where
  Appearance : Type u
  /-- The raw data of sensibility. -/
  Sensation  : Type v
  /-- The Time-line: the formal condition of all appearances (A34/B50). -/
  TimeLine   : Type w

  /-- The passive "Synopsis" of sense. -/
  synopsis : Appearance → Sensation

  /-- Every appearance is necessarily in Time (The "Toothed-Comb" baseline). -/
  temporal_location : Appearance → TimeLine

/--
Laywine's "Swarm" Predicate:
A manifold is a 'swarm' or 'rhapsody' if it lacks a rule of connection.
-/
def IsSwarm (K : AppearanceSystem) (manifold : Set K.Appearance) : Prop :=
  ∀ a₁ ∈ manifold, ∀ a₂ ∈ manifold, a₁ ≠ a₂ → ¬∃ (rule : Prop), rule

/--
The "Deduction Goal":
To prove that no part of the Sensation can remain a "blind play"
excluded from the unified world-whole.
-/
def IsExposible (K : AppearanceSystem) (a : K.Appearance) : Prop :=
  ∃ (t : K.TimeLine), K.temporal_location a = t

end Philosophy.Kant.Text
