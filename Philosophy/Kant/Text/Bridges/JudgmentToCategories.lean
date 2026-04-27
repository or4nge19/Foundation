import Philosophy.Kant.Text.CPR.Analytic.MetaphysicalDeduction

namespace Philosophy.Kant.Text.Bridges

open Philosophy.Kant.Text
open Philosophy.Kant.Text.CPR.Analytic

theorem judgment_to_categories_quantity :
    quantityFormToCategory .universal = .unity ∧
    quantityFormToCategory .particular = .plurality ∧
    quantityFormToCategory .singular = .totality := by
  exact quantity_form_maps_to_quantity_category

theorem judgment_to_categories_quality :
    qualityFormToCategory .affirmative = .reality ∧
    qualityFormToCategory .negative = .negation ∧
    qualityFormToCategory .infinite = .limitation := by
  exact quality_form_maps_to_quality_category

theorem judgment_to_categories_relation :
    relationFormToCategory .categorical = .inherenceAndSubsistence ∧
    relationFormToCategory .hypothetical = .causalityAndDependence ∧
    relationFormToCategory .disjunctive = .community := by
  exact relation_form_maps_to_relation_category

theorem judgment_to_categories_modality :
    modalityFormToCategory .problematic = .possibility ∧
    modalityFormToCategory .assertoric = .existence ∧
    modalityFormToCategory .apodeictic = .necessity := by
  exact modality_form_maps_to_modality_category

end Philosophy.Kant.Text.Bridges
