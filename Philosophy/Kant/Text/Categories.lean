import Philosophy.Kant.Text.Judgment

universe u y

namespace Philosophy.Kant.Text

/--
Relation categories (A80/B106):
The specific rules the understanding uses to connect representations.
(Laywine: The future "Laws of Community/Nature" in the Cosmology of Experience).
-/
inductive CategoryOfRelation
  | inherenceAndSubsistence
  | causalityAndDependence
  | community
  deriving DecidableEq, Repr

/--
CategorySystem: Formalizes the Categories not as static tags,
but as active functions (Handlungen) of the understanding (B143).
-/
structure CategorySystem extends JudgmentSystem where

  /--
  The Function of Judging (functio/Verrichtung).
  A category is the active operation that takes the matter of a judgment (a set of concepts)
  and synthesizes them into an Objective Unity.
  -/
  synthesize_judgment : CategoryOfRelation → Set Concept → Judgment

  /--
  The Hylomorphic Axiom of the Categories (Laywine Ch 3, §2d):
  The active function of the category *produces* the logical form.
  (The category is the 'art of sculpting', the logical form is the 'statue').
  -/
  category_generates_form : ∀ (cat : CategoryOfRelation) (matter : Set Concept),
    relation (synthesize_judgment cat matter) =
      match cat with
      | .inherenceAndSubsistence => RelationForm.categorical
      | .causalityAndDependence  => RelationForm.hypothetical
      | .community               => RelationForm.disjunctive

  /--
  The matter synthesized by the category becomes the exact matter of the resulting judgment.
  -/
  synthesis_preserves_matter : ∀ (cat : CategoryOfRelation) (m : Set Concept),
    matter (synthesize_judgment cat m) = m


/--
The Metaphysical Deduction (The Discovery Mechanism - A79/B104).
While the category *generates* the form ontologically (as modeled above),
we *discover* the categories by mapping backwards from the forms of general logic.
-/
def formToCategory : RelationForm → CategoryOfRelation
  | .categorical => .inherenceAndSubsistence
  | .hypothetical => .causalityAndDependence
  | .disjunctive => .community

/-- Sanity check: The discovery mapping is total over relational forms. -/
theorem form_to_category_total (r : RelationForm) :
    ∃ c, formToCategory r = c := by
  exact ⟨formToCategory r, rfl⟩

end Philosophy.Kant.Text
