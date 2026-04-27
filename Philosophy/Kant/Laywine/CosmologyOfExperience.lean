import Philosophy.Kant.Laywine.Commercium
import Philosophy.Kant.Text.Objectivity

namespace Philosophy.Kant.Laywine

def CosmologicalCategory (c : Philosophy.Kant.Text.CategoryOfRelation) : Prop :=
  c = .inherenceAndSubsistence ∨ c = .causalityAndDependence ∨ c = .community

/-- Laywine's thesis: the world-whole and reciprocal community are recapitulated as
conditions of possible experience. -/
def CosmologyOfExperience
    (C : CommerciumSystem)
    (K : Philosophy.Kant.Text.ObjectivitySystem) : Prop :=
  ReciprocalInflux C ∧ WorldWhole C ∧ Philosophy.Kant.Text.ConditionOfPossibleExperience K

theorem all_relation_categories_are_cosmological
    (c : Philosophy.Kant.Text.CategoryOfRelation) :
    CosmologicalCategory c := by
  cases c <;> simp [CosmologicalCategory]

theorem laywine_commercium_supports_world_whole
    {C : CommerciumSystem}
    {K : Philosophy.Kant.Text.ObjectivitySystem}
    (h : CosmologyOfExperience C K) :
    WorldWhole C :=
  h.2.1

end Philosophy.Kant.Laywine
