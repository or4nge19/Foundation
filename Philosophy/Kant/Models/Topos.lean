import Philosophy.Kant.Text.Deduction
import Mathlib

universe u

noncomputable section

namespace Philosophy.Kant.Models

open CategoryTheory Opposite TopologicalSpace
open scoped MonoidalCategory

abbrev UnderstandingTopos (World : Type u) [TopologicalSpace World] :=
  Sheaf (Opens.grothendieckTopology World) TopCat.{0}

abbrev RawIntuition (World : Type u) [TopologicalSpace World] :=
  (Opens World)ᵒᵖ ⥤ TopCat.{0}

structure CognitiveArchitecture (World : Type u) [TopologicalSpace World] where
  apprehension : RawIntuition World ⥤ UnderstandingTopos World
  schematism : UnderstandingTopos World ⥤ RawIntuition World
  unity : apprehension ⊣ schematism

def schematism_is_transcendentally_unique
    {World : Type u} [TopologicalSpace World]
    {mind₁ mind₂ : CognitiveArchitecture World}
    (h_same_app : mind₁.apprehension = mind₂.apprehension) :
    mind₁.schematism ≅ mind₂.schematism :=
  CategoryTheory.Adjunction.rightAdjointUniq mind₁.unity (h_same_app ▸ mind₂.unity)

structure RelationalOuterObject {World : Type u} [TopologicalSpace World]
    (A : UnderstandingTopos World) where
  relational_rule : ((CategoryTheory.Functor.const _).obj (TopCat.of PUnit)) ⟶ A.val

structure AttentionHead {World : Type u} [TopologicalSpace World]
    [MonoidalCategory ((Opens World)ᵒᵖ ⥤ TopCat.{0})]
    {A : UnderstandingTopos World} where
  attention_map : (A.val ⊗ A.val) ⟶ A.val

structure Apperception {World : Type u} [TopologicalSpace World]
    [MonoidalCategory ((Opens World)ᵒᵖ ⥤ TopCat.{0})]
    [HasProducts ((Opens World)ᵒᵖ ⥤ TopCat.{0})]
    (A : UnderstandingTopos World) (HeadIndex : Type) where
  heads : HeadIndex → AttentionHead (A := A)
  W_O : piObj (fun _ : HeadIndex => A.val) ⟶ A.val

def global_synthesis {World : Type u} [TopologicalSpace World]
    [MonoidalCategory ((Opens World)ᵒᵖ ⥤ TopCat.{0})]
    [HasProducts ((Opens World)ᵒᵖ ⥤ TopCat.{0})]
    {A : UnderstandingTopos World} {HeadIndex : Type}
    (mind : Apperception A HeadIndex) :
    (A.val ⊗ A.val) ⟶ A.val :=
  Pi.lift (fun i => (mind.heads i).attention_map) ≫ mind.W_O

def IsTranscendentalUnity {World : Type u} [TopologicalSpace World]
    [MonoidalCategory ((Opens World)ᵒᵖ ⥤ TopCat.{0})]
    [SymmetricCategory ((Opens World)ᵒᵖ ⥤ TopCat.{0})]
    [HasProducts ((Opens World)ᵒᵖ ⥤ TopCat.{0})]
    {A : UnderstandingTopos World} {HeadIndex : Type}
    (mind : Apperception A HeadIndex) : Prop :=
  (β_ A.val A.val).hom ≫ global_synthesis mind = global_synthesis mind

/-- Data of a topos-theoretic semantic presentation. -/
structure ToposSemanticData where
  World : Type u
  instTopologicalSpace : TopologicalSpace World
  instMonoidal :
    MonoidalCategory ((Opens World)ᵒᵖ ⥤ TopCat.{0})
  instSymmetric :
    SymmetricCategory ((Opens World)ᵒᵖ ⥤ TopCat.{0})
  instHasProducts :
    HasProducts ((Opens World)ᵒᵖ ⥤ TopCat.{0})
  A : UnderstandingTopos World
  HeadIndex : Type
  mind : @Apperception World instTopologicalSpace instMonoidal instHasProducts A HeadIndex

attribute [instance] ToposSemanticData.instTopologicalSpace
attribute [instance] ToposSemanticData.instMonoidal
attribute [instance] ToposSemanticData.instSymmetric
attribute [instance] ToposSemanticData.instHasProducts

/-- Transcendental unity is a property of the topos data, not a bundled field. -/
def SatisfiesToposUnity (M : ToposSemanticData) : Prop :=
  @IsTranscendentalUnity M.World M.instTopologicalSpace M.instMonoidal
    M.instSymmetric M.instHasProducts M.A M.HeadIndex M.mind

noncomputable def ToposSemanticData.toObjectivitySystem (M : ToposSemanticData) :
    Philosophy.Kant.Text.ObjectivitySystem where
  Appearance := M.HeadIndex
  Manifold := M.HeadIndex
  gather := id
  Intuition := M.HeadIndex
  formIntuition := id
  Concept := Philosophy.Kant.Text.CategoryOfRelation
  underConcept := fun _ _ => True
  Judgment := Unit
  quantity := fun _ => .universal
  quality := fun _ => .affirmative
  relation := fun _ => .categorical
  modality := fun _ => .assertoric
  synthesize := id
  combineInOneConsciousness := fun _ _ => SatisfiesToposUnity M
  ruleGovernedBy := fun _ c => c = Philosophy.Kant.Text.CategoryOfRelation.community
  ObjectOfExperience := M.HeadIndex
  refersTo := fun i o => o = i

theorem topos_model_satisfies_kantian_kernel
    (M : ToposSemanticData) (hUnity : SatisfiesToposUnity M) :
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
