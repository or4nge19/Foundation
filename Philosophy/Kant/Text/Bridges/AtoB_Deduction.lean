import Philosophy.Kant.Text.CPR.Analytic.TranscendentalDeductionA
import Philosophy.Kant.Text.CPR.Analytic.TranscendentalDeductionB

namespace Philosophy.Kant.Text.Bridges

open Philosophy.Kant.Text.CPR.Analytic

/-- A lightweight comparison package between the A- and B-Deduction architectures. -/
structure DeductionComparison (A : DeductionA_System) (B : DeductionB_System) : Prop where
  apprehension_to_combination :
    ∀ a₀ a₁ : A.Appearance, B.SubjectiveUnityOfConsciousness
  recognition_to_objectivity :
    SynthesisOfRecognition A → ObjectiveUnityOfApperception B

theorem a_to_b_preserves_objective_unity
    {A : DeductionA_System} {B : DeductionB_System}
    (h : DeductionComparison A B)
    (hRec : SynthesisOfRecognition A) :
    ObjectiveUnityOfApperception B :=
  h.recognition_to_objectivity hRec

end Philosophy.Kant.Text.Bridges
