import Mathlib
import Philosophy.Kant.Text.Judgment

universe u

namespace Philosophy.Kant.Text.PreCritical

open Philosophy.Kant.Text

inductive FunctionOfApperception : Type
  | inherence
  | dependence
  | composition
  deriving DecidableEq, Repr

def functionToRelationForm : FunctionOfApperception → RelationForm
  | .inherence => .categorical
  | .dependence => .hypothetical
  | .composition => .disjunctive

structure Perception (Appearance : Type u) where
  content : Appearance
  isConscious : Prop

def Exposition (Appearance : Type u) :=
  Perception Appearance → FunctionOfApperception

def SubsumedBy {Appearance : Type u}
    (expo : Exposition Appearance)
    (p : Perception Appearance)
    (f : FunctionOfApperception) : Prop :=
  expo p = f

structure ObjectiveRepresentation {Appearance : Type u} (expo : Exposition Appearance) where
  perception : Perception Appearance
  func : FunctionOfApperception
  isSubsumed : SubsumedBy expo perception func

theorem duisburg_functions_map_to_judgment_forms :
    functionToRelationForm .inherence = .categorical ∧
    functionToRelationForm .dependence = .hypothetical ∧
    functionToRelationForm .composition = .disjunctive := by
  exact ⟨rfl, rfl, rfl⟩

end Philosophy.Kant.Text.PreCritical
