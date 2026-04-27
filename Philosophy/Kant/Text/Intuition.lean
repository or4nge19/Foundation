import Philosophy.Kant.Text.Appearance
import Mathlib

universe u v w

namespace Philosophy.Kant.Text

/--
IntuitionSystem: Formalizes the Synthesis of Apprehension (A98-100).
It defines how the mind actively "runs through" and "takes together"
appearances to form conscious intuitions over time.
-/
structure IntuitionSystem extends AppearanceSystem where
  /-- The result of the synthesis of apprehension. -/
  Intuition : Type w

  /-- Kant distinguishes pure (formal) from empirical intuitions (B160-161). -/
  is_pure : Intuition → Prop
  is_empirical : Intuition → Prop

  -- AXIOM: An intuition is either pure (a priori) or empirical (a posteriori).
  partition : ∀ i, Xor' (is_pure i) (is_empirical i)

  /--
  The Synthesis of Apprehension (A99).
  Instead of a static 'Manifold -> Intuition', this is an active process.
  It takes a subset of raw appearances (the manifold) and constructs an Intuition.
  -/
  synthesisOfApprehension : Set Appearance → Intuition

  /--
  Every intuition, because it requires "running through" (Durchlaufen),
  occupies a specific span of the TimeLine (B154 / L1 28.202).
  -/
  time_span : Intuition → Set TimeLine

  -- AXIOM of Ekthesis (Mental Drawing):
  -- To form an empirical intuition requires time. It cannot be instantaneous.
  -- "The going through of a part of the appearance cannot take place in an instant." (L1 28.202)
  empirical_requires_duration : ∀ (s : Set Appearance),
    is_empirical (synthesisOfApprehension s) →
    ∃ t₁ t₂, t₁ ∈ time_span (synthesisOfApprehension s) ∧
             t₂ ∈ time_span (synthesisOfApprehension s) ∧
             t₁ ≠ t₂

end Philosophy.Kant.Text
