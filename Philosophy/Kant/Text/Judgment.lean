import Philosophy.Kant.Text.Concept

universe u v w x y

namespace Philosophy.Kant.Text

inductive QuantityForm
  | universal
  | particular
  | singular
  deriving DecidableEq, Repr

inductive QualityForm
  | affirmative
  | negative
  | infinite
  deriving DecidableEq, Repr

inductive RelationForm
  | categorical
  | hypothetical
  | disjunctive
  deriving DecidableEq, Repr

inductive ModalityForm
  | problematic
  | assertoric
  | apodeictic
  deriving DecidableEq, Repr

/--
JudgmentSystem: Formalizes Kant's break from Meier and Wolff (§19, B141).
A judgment is not merely a relation between concepts, but the active subsumption
of concepts under the objective unity of apperception.
-/
structure JudgmentSystem extends ConceptSystem where
  /-- The act of judging. -/
  Judgment : Type y

  -- The Logical Forms of Judgment (A70/B95)
  quantity : Judgment → QuantityForm
  quality : Judgment → QualityForm
  relation : Judgment → RelationForm
  modality : Judgment → ModalityForm

  /--
  The Matter of Judgment.
  Every judgment synthesizes a manifold of constituent concepts (Laywine Ch 3, §2d).
  -/
  matter : Judgment → Set Concept

  /--
  The Copula ("is"):
  Designates the bringing of representations into the *Objective* Unity of Apperception,
  as opposed to the merely *Subjective* unity of the reproductive imagination (B141-142).
  -/
  is_objective_unity : Judgment → Prop

  -- AXIOM of Objective Validity (§19):
  -- To be a judgment at all, the relation of concepts must possess objective unity.
  -- This is what separates "The body is heavy" from "I feel weight when I hold a body."
  judgment_implies_objective_unity : ∀ j, is_objective_unity j

  /--
  A mere association of ideas (subjective unity).
  (Laywine Ch 3, §1: "completely contingent" connections of the imagination).
  -/
  AssociationOfIdeas : Type y
  associated_concepts : AssociationOfIdeas → Set Concept

  /-- Associations lack objective unity; they are only subjectively valid. -/
  is_subjective_unity : AssociationOfIdeas → Prop

  -- AXIOM of Subjective Contingency:
  -- Associations of ideas can never possess the objective unity of a judgment.
  -- This rigorously formally separates the faculties of Imagination and Understanding.
  association_is_not_objective : ∀ a, is_subjective_unity a ↔ ¬(∃ j, matter j = associated_concepts a ∧ is_objective_unity j)

end Philosophy.Kant.Text
