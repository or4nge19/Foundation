import Philosophy.Kant.Text.Objectivity

universe u v w z

namespace Philosophy.Kant.Text.CPR.Analytic

open Philosophy.Kant.Text

/--
PhenomenaNoumenaSystem: Formalizes the boundary of the Cosmology of Experience (A235/B294).
It extends ObjectivitySystem to explicitly bound what the human mind can and cannot legislate.
-/
structure PhenomenaNoumenaSystem extends ObjectivitySystem where
  /--
  The supreme ontological category (The "Thing").
  Before being qualified epistemically, we can posit entities.
  -/
  Thing : Type v

  /--
  An Object of Experience (from ObjectivitySystem) is a Thing given in
  sensible intuition and synthesized by the categories. This is a Phenomenon.
  -/
  asThing : ObjectOfExperience → Thing

  /--
  Intellectual Intuition: The mode of cognition of an Intellectus Archetypus (God).
  (Laywine Ch 4, §1a: A divine mind creates its own manifold; humans only receive it).
  -/
  IntellectualIntuition : Type w

  /-- Positive Noumenon: An object given directly to an Intellectual Intuition (B307). -/
  givenInIntellectualIntuition : Thing → IntellectualIntuition → Prop

  /--
  AXIOM of Human Finitude:
  Human cognitive architecture entirely lacks Intellectual Intuition.
  "We have no insight into the possibility of noumena" (A248/B305).
  -/
  human_lacks_intellectual_intuition : IsEmpty IntellectualIntuition

/--
A Phenomenon is an object of possible experience.
It is the direct result of lawful synthesis mapping an intuition to objective validity.
-/
def IsPhenomenon (K : PhenomenaNoumenaSystem) (t : K.Thing) : Prop :=
  ∃ (o : K.ObjectOfExperience) (i : K.Intuition),
    K.asThing o = t ∧ K.refersTo i o ∧ ObjectivelyValid K.toObjectivitySystem i

/--
The Negative Sense of Noumenon (B307):
A Thing considered purely through the understanding, abstracted from space, time,
and sensible intuition. "A thing so far as it is not an object of our sensible intuition."
-/
def IsNoumenonNegative (K : PhenomenaNoumenaSystem) (t : K.Thing) : Prop :=
  ¬ IsPhenomenon K t

/--
The Positive Sense of Noumenon (B307):
An object of a non-sensible (intellectual) intuition.
-/
def IsNoumenonPositive (K : PhenomenaNoumenaSystem) (t : K.Thing) : Prop :=
  ∃ ii : K.IntellectualIntuition, K.givenInIntellectualIntuition t ii

/--
The Limiting Concept Theorem (A255/B310):
Because humans lack intellectual intuition, the concept of a Noumenon
is strictly negative for us. It serves only to mark the limits of sensibility.
This replaces your "Proof by True" with a rigorous logical deduction.
-/
theorem noumenon_is_strictly_negative_for_humans
    (K : PhenomenaNoumenaSystem) (t : K.Thing) :
    ¬ IsNoumenonPositive K t := by
  -- Assume for contradiction that it is a positive noumenon
  intro ⟨ii, _⟩
  -- This requires an instance of IntellectualIntuition.
  -- But by the Axiom of Human Finitude, this type is Empty.
  exact K.human_lacks_intellectual_intuition.false ii

/--
Laywine's "Anti-Aporetic" Corollary (A104 / B146):
Categories applied without sensible intuition yield no objective knowledge.
We can *think* the Thing (as a Noumenon), but we cannot *know* it, because
knowledge requires the active synthesis of the sensible manifold.
-/
theorem categories_without_sensibility_are_empty
    (K : PhenomenaNoumenaSystem) (t : K.Thing) :
    IsNoumenonNegative K t → ¬ ∃ (i : K.Intuition),
      (∃ o, K.asThing o = t ∧ K.refersTo i o) := by
  intro h_noumenon ⟨i, ⟨o, h_eq, h_refers⟩⟩
  -- If it is referred to by an intuition, it is an ObjectOfExperience.
  -- Therefore, it is a Phenomenon, which contradicts that it is a Negative Noumenon.
  have h_phenom : IsPhenomenon K t := by
    use o, i
    exact ⟨h_eq, h_refers, ⟨o, h_refers⟩⟩
  exact h_noumenon h_phenom

end Philosophy.Kant.Text.CPR.Analytic
