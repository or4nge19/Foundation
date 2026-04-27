import Philosophy.Kant.Models.ChartedSpace
import Philosophy.Kant.Text.Deduction
import Mathlib

universe u v

namespace Philosophy.Kant.Models

open TopologicalSpace

/-- Data of a groupoid-style semantic presentation of experience. -/
structure GroupoidSemanticData (PureIntuition : Type u) [TopologicalSpace PureIntuition] where
  SensibleManifold : Type v
  instTopologicalSpace : TopologicalSpace SensibleManifold
  instChartedSpace : ChartedSpace PureIntuition SensibleManifold
  Categories : StructureGroupoid PureIntuition

attribute [instance] GroupoidSemanticData.instTopologicalSpace
attribute [instance] GroupoidSemanticData.instChartedSpace

/-- The groupoid semantics satisfy unity when every chart transition belongs to the chosen
structure groupoid. -/
def SatisfiesGroupoidUnity
    {PureIntuition : Type u} [TopologicalSpace PureIntuition]
    (M : GroupoidSemanticData PureIntuition) : Prop :=
  @HasGroupoid PureIntuition _ M.SensibleManifold M.instTopologicalSpace M.instChartedSpace M.Categories

noncomputable def GroupoidSemanticData.toObjectivitySystem
    {PureIntuition : Type u} [TopologicalSpace PureIntuition]
    (M : GroupoidSemanticData PureIntuition) :
    Philosophy.Kant.Text.ObjectivitySystem where
  Appearance := M.SensibleManifold
  Manifold := M.SensibleManifold
  gather := id
  Intuition := M.SensibleManifold
  formIntuition := id
  Concept := Philosophy.Kant.Text.CategoryOfRelation
  underConcept := fun _ _ => True
  Judgment := Unit
  quantity := fun _ => .universal
  quality := fun _ => .affirmative
  relation := fun _ => .categorical
  modality := fun _ => .assertoric
  synthesize := id
  combineInOneConsciousness := fun _ _ => SatisfiesGroupoidUnity M
  ruleGovernedBy := fun _ c => c = Philosophy.Kant.Text.CategoryOfRelation.community
  ObjectOfExperience := M.SensibleManifold
  refersTo := fun i o => o = i

theorem groupoid_model_satisfies_conditions_of_experience
    {PureIntuition : Type u} [TopologicalSpace PureIntuition]
    (M : GroupoidSemanticData PureIntuition)
    (hUnity : SatisfiesGroupoidUnity M) :
    Philosophy.Kant.Text.ConditionOfPossibleExperience M.toObjectivitySystem := by
  constructor
  · intro i j hij
    exact ⟨.community, rfl, rfl⟩
  constructor
  · intro i j hij
    exact ⟨.community, rfl, rfl⟩
  · intro i hi
    exact ⟨i, rfl⟩

end Philosophy.Kant.Models
