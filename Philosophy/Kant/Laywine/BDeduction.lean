import Philosophy.Kant.Laywine.CosmologyOfExperience
import Philosophy.Kant.Text.Deduction

namespace Philosophy.Kant.Laywine

/-- Laywine's reading of the B-Deduction: under the cosmology of experience, unified
representations are objectively valid. -/
theorem laywine_b_deduction
    (C : CommerciumSystem)
    (K : Philosophy.Kant.Text.ObjectivitySystem)
    (h : CosmologyOfExperience C K) :
    ∀ i,
      Philosophy.Kant.Text.UnifiedInOneConsciousness K.toSynthesisSystem i →
      Philosophy.Kant.Text.ObjectivelyValid K i := by
  exact Philosophy.Kant.Text.lawful_synthesis_yields_objective_validity K h.2.2

end Philosophy.Kant.Laywine
