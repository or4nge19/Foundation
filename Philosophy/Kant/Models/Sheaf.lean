import Philosophy.Kant.Text.Deduction
import Mathlib

universe u v

namespace Philosophy.Kant.Models

open CategoryTheory Opposite TopologicalSpace

/-- Data of a sheaf-theoretic semantics for objective experience. -/
structure SheafSemanticData where
  X : TopCat.{u}
  F : TopCat.Presheaf (Type v) X
  iThink : F.obj (op ⊤)

/-- The sheaf condition is the semantic law, not part of the carrier data. -/
def SatisfiesSheafCondition (M : SheafSemanticData) : Prop :=
  M.F.IsSheaf

noncomputable def SheafSemanticData.toObjectivitySystem (M : SheafSemanticData) :
    Philosophy.Kant.Text.ObjectivitySystem where
  Appearance := M.F.obj (op ⊤)
  Manifold := M.F.obj (op ⊤)
  gather := id
  Intuition := M.F.obj (op ⊤)
  formIntuition := id
  Concept := Philosophy.Kant.Text.CategoryOfRelation
  underConcept := fun _ _ => True
  Judgment := Unit
  quantity := fun _ => .universal
  quality := fun _ => .affirmative
  relation := fun _ => .categorical
  modality := fun _ => .assertoric
  synthesize := id
  combineInOneConsciousness := fun _ _ => SatisfiesSheafCondition M
  ruleGovernedBy := fun _ c => c = Philosophy.Kant.Text.CategoryOfRelation.inherenceAndSubsistence
  ObjectOfExperience := M.F.obj (op ⊤)
  refersTo := fun i o => o = i

theorem sheaf_model_expresses_unity_of_apperception
    (M : SheafSemanticData) (hSheaf : SatisfiesSheafCondition M) :
    Philosophy.Kant.Text.UnityOfApperception M.toObjectivitySystem.toSynthesisSystem := by
  intro i j hij
  exact ⟨.inherenceAndSubsistence, rfl, rfl⟩

theorem sheaf_model_satisfies_conditions_of_experience
    (M : SheafSemanticData) (hSheaf : SatisfiesSheafCondition M) :
    Philosophy.Kant.Text.ConditionOfPossibleExperience M.toObjectivitySystem := by
  constructor
  · exact sheaf_model_expresses_unity_of_apperception M hSheaf
  constructor
  · intro i j hij
    exact ⟨.inherenceAndSubsistence, rfl, rfl⟩
  · intro i hi
    exact ⟨i, rfl⟩

end Philosophy.Kant.Models
