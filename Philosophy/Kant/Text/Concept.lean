import Philosophy.Kant.Text.Intuition
import Mathlib

universe u v w x

namespace Philosophy.Kant.Text

/--
ConceptSystem: Formalizes the Faculty of Understanding (Spontaneity).
Concepts are not static containers, but active rules used by the mind
to unify the synthesized manifold (A106, B93).
-/
structure ConceptSystem extends IntuitionSystem where
  /-- The representations of the understanding. -/
  Concept : Type x

  /-- Kant strictly distinguishes the Categories (pure) from empirical concepts. -/
  is_pure_concept : Concept → Prop
  is_empirical_concept : Concept → Prop

  -- AXIOM: A concept is either pure (a priori) or empirical (a posteriori).
  partition_concept : ∀ c, Xor' (is_pure_concept c) (is_empirical_concept c)

  /--
  Analytic Unity (B133-134).
  A concept "holds for many" (B93). It has an extension (Umfang) of intuitions
  that it can successfully unify.
  -/
  extension : Concept → Set Intuition

  /--
  The Synthesis of Recognition in a Concept (A103).
  Instead of a passive 'underConcept' relation, we model the active
  subsumption of an intuition under the rule of a concept.
  -/
  subsumes : Concept → Intuition → Prop

  -- AXIOM of Subsumption:
  -- An intuition is actively subsumed by a concept if and only if
  -- the understanding recognizes it as belonging to the concept's extension.
  subsumption_is_extension : ∀ c i, subsumes c i ↔ i ∈ extension c

  /--
  The "I think" (Pure Apperception) must be able to accompany all concepts.
  This means every concept must possess analytic unity (it remains the *same*
  thought no matter what it accompanies).
  (Laywine, Chapter 2, §2f).
  -/
  has_analytic_unity : Concept → Prop

  -- AXIOM: To be a concept at all is to possess analytic unity.
  concept_implies_analytic_unity : ∀ c, has_analytic_unity c

end Philosophy.Kant.Text
