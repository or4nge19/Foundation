import Mathlib.ModelTheory.Syntax      
import Mathlib.ModelTheory.Semantics      
import Mathlib.ModelTheory.Bundled  -- Required for ModelType  
import Mathlib.CategoryTheory.Category.Basic      
import Mathlib.Data.Set.Basic      

open CategoryTheory
open FirstOrder.Language

namespace FormalHermeneutics

universe u v w

structure FormalSystem where
  L : FirstOrder.Language.{u, v}
  T : Theory L
  J : Set Prop

def Theory.Provable {L : FirstOrder.Language} (T : Theory L) (φ : Sentence L) : Prop :=
  φ ∈ T

structure Aporia (S : FormalSystem) where
  statement : Sentence S.L
  is_proven : Theory.Provable S.T statement
  is_limitative : ∀ (M : Type w) [S.L.Structure M] [M ⊨ S.T] [Nonempty M],
    ¬ (M ⊨ statement)

structure Aporia' (S : FormalSystem) where
  statement : Sentence S.L
  is_proven : Theory.Provable S.T statement
  is_limitative : ∀ (M : S.T.ModelType), ¬ (M ⊨ statement)

end FormalHermeneutics