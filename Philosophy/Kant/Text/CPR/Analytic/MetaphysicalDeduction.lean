import Philosophy.Kant.Text.Judgment
import Philosophy.Kant.Text.Categories

universe u y

namespace Philosophy.Kant.Text.CPR.Analytic

open Philosophy.Kant.Text

/- Kant A80/B106: The full table of categories. -/

/-- Quantity categories. -/
inductive CategoryOfQuantity
  | unity
  | plurality
  | totality
  deriving DecidableEq, Repr

/-- Quality categories. -/
inductive CategoryOfQuality
  | reality
  | negation
  | limitation
  deriving DecidableEq, Repr

/-- Modality categories (formalizing the positive pole as per Kant's B106 table). -/
inductive CategoryOfModality
  | possibility
  | existence
  | necessity
  deriving DecidableEq, Repr

/--
The Scaravelli/Laywine Architectural Split (B110).
Mathematical Categories govern the construction of magnitudes (Axioms/Anticipations).
-/
inductive MathematicalCategory
  | quantity (c : CategoryOfQuantity)
  | quality (c : CategoryOfQuality)

/--
Dynamical Categories govern the existence of objects and their cosmological
relations in time (Analogies) and to the cognitive faculty (Postulates).
-/
inductive DynamicalCategory
  | relation (c : CategoryOfRelation)
  | modality (c : CategoryOfModality)

/--
FullCategorySystem: Elevates the full table of categories into active functions.
A complete judgment requires a synthesis across all four headings.
-/
structure FullCategorySystem extends CategorySystem where

  /--
  The Complete Function of Judging.
  Synthesizing a complete judgment requires a category from each of the four headings
  operating upon the matter (the Set of Concepts).
  -/
  synthesize_full_judgment :
    CategoryOfQuantity → CategoryOfQuality → CategoryOfRelation → CategoryOfModality →
    Set Concept → Judgment

  /--
  The Hylomorphic Axioms for the Full Table:
  The categories *generate* the logical form of the judgment across all four dimensions.
  -/
  quantity_generates_form : ∀ qt ql r m mat,
    quantity (synthesize_full_judgment qt ql r m mat) =
      match qt with
      | .unity => QuantityForm.universal
      | .plurality => QuantityForm.particular
      | .totality => QuantityForm.singular

  quality_generates_form : ∀ qt ql r m mat,
    quality (synthesize_full_judgment qt ql r m mat) =
      match ql with
      | .reality => QualityForm.affirmative
      | .negation => QualityForm.negative
      | .limitation => QualityForm.infinite

  relation_generates_form : ∀ qt ql r m mat,
    relation (synthesize_full_judgment qt ql r m mat) =
      match r with
      | .inherenceAndSubsistence => RelationForm.categorical
      | .causalityAndDependence => RelationForm.hypothetical
      | .community => RelationForm.disjunctive

  modality_generates_form : ∀ qt ql r m mat,
    modality (synthesize_full_judgment qt ql r m mat) =
      match m with
      | .possibility => ModalityForm.problematic
      | .existence => ModalityForm.assertoric
      | .necessity => ModalityForm.apodeictic

  /-- The matter synthesized by the full categorical profile is preserved in the judgment. -/
  full_synthesis_preserves_matter : ∀ qt ql r m mat,
    matter (synthesize_full_judgment qt ql r m mat) = mat

/-
The Metaphysical Deduction (Discovery Mechanism).
Mapping backwards from the forms of general logic to discover the functions.
-/
def quantityFormToCategory : QuantityForm → CategoryOfQuantity
  | .universal => .unity
  | .particular => .plurality
  | .singular => .totality

def qualityFormToCategory : QualityForm → CategoryOfQuality
  | .affirmative => .reality
  | .negative => .negation
  | .infinite => .limitation

def modalityFormToCategory : ModalityForm → CategoryOfModality
  | .problematic => .possibility
  | .assertoric => .existence
  | .apodeictic => .necessity

theorem quantity_form_maps_to_quantity_category_total (q : QuantityForm) :
    ∃ c, quantityFormToCategory q = c := ⟨_, rfl⟩

theorem quality_form_maps_to_quality_category_total (q : QualityForm) :
    ∃ c, qualityFormToCategory q = c := ⟨_, rfl⟩

theorem modality_form_maps_to_modality_category_total (m : ModalityForm) :
    ∃ c, modalityFormToCategory m = c := ⟨_, rfl⟩

end Philosophy.Kant.Text.CPR.Analytic
