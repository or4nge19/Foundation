import Philosophy.Kant.Text.Judgment

universe u

namespace Philosophy.Kant.Laywine

/--
In the Duisburg Nachlass, Kant identifies three functions of apperception that
Laywine reads as precursors to the canonical relation forms of judgment.
-/
inductive FunctionOfApperception : Type
  | inherence
  | dependence
  | composition
  deriving DecidableEq, Repr

/-- The three functions of apperception ground the canonical relation forms of judgment. -/
def apperceptionToRelationForm :
    FunctionOfApperception → Philosophy.Kant.Text.RelationForm
  | .inherence => .categorical
  | .dependence => .hypothetical
  | .composition => .disjunctive

theorem apperception_to_relation_forms_correct :
    apperceptionToRelationForm .inherence = .categorical ∧
    apperceptionToRelationForm .dependence = .hypothetical ∧
    apperceptionToRelationForm .composition = .disjunctive := by
  exact ⟨rfl, rfl, rfl⟩

theorem duisburg_functions_map_to_judgment_forms :
    apperceptionToRelationForm .inherence = .categorical ∧
    apperceptionToRelationForm .dependence = .hypothetical ∧
    apperceptionToRelationForm .composition = .disjunctive := by
  exact apperception_to_relation_forms_correct

/-- A perception is an appearance of which the subject is conscious. -/
structure Perception (Appearance : Type u) where
  content : Appearance
  is_conscious : Prop

/-- Exposition assigns each conscious perception to a function of apperception. -/
def Exposition (Appearance : Type u) :=
  Perception Appearance → FunctionOfApperception

/-- A perception is subsumed by a function when the exposition assigns that function to it. -/
def SubsumedBy {Appearance : Type u}
    (exposition : Exposition Appearance) (perception : Perception Appearance)
    (f : FunctionOfApperception) : Prop :=
  exposition perception = f

/-- Objective representation arises when a conscious perception is subsumed under one
of the functions of apperception. -/
structure ObjectiveRepresentation {Appearance : Type u} (exposition : Exposition Appearance) where
  perception : Perception Appearance
  func : FunctionOfApperception
  is_subsumed : SubsumedBy exposition perception func

theorem laywine_duisburg_exposition_is_rule_governed
    {Appearance : Type u} (exposition : Exposition Appearance)
    (perception : Perception Appearance) :
    SubsumedBy exposition perception (exposition perception) := rfl

end Philosophy.Kant.Laywine
