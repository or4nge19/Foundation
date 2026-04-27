import Mathlib
import Philosophy.Aristotle.DeInterpretatione

namespace Aristotle.PriorAnalytics

open Aristotle.DeInterpretatione

/-!
# Syllogistic Syntax

Following Robin Smith and John Corcoran, we treat the syllogistic as an
object-language. This file narrows the broader `DeInterpretatione`
statement-layer to the universal/particular categorical forms used by the
syllogistic; proof-theoretic facts live in `ProofTheory`.
-/

/--
The syllogistic should not introduce a second incompatible universe of terms.
It reuses the term-object and categorical forms already fixed upstream by the
`DeInterpretatione` layer.
-/
abbrev Term := Aristotle.DeInterpretatione.Term
abbrev Categorical := Aristotle.DeInterpretatione.Categorical
abbrev Quantity := Aristotle.DeInterpretatione.CategoricalQuantity
abbrev Quality := Aristotle.DeInterpretatione.Quality

namespace Categorical

abbrev A (S P : Term) : Aristotle.PriorAnalytics.Categorical :=
  Aristotle.DeInterpretatione.Categorical.A S P

abbrev E (S P : Term) : Aristotle.PriorAnalytics.Categorical :=
  Aristotle.DeInterpretatione.Categorical.E S P

abbrev I (S P : Term) : Aristotle.PriorAnalytics.Categorical :=
  Aristotle.DeInterpretatione.Categorical.I S P

abbrev O (S P : Term) : Aristotle.PriorAnalytics.Categorical :=
  Aristotle.DeInterpretatione.Categorical.O S P

end Categorical

def Categorical.subject : Categorical → Term
    :=
  Aristotle.DeInterpretatione.Categorical.subject

def Categorical.predicate : Categorical → Term
    :=
  Aristotle.DeInterpretatione.Categorical.predicate

def Categorical.quantity : Categorical → Quantity
    :=
  Aristotle.DeInterpretatione.Categorical.quantity

def Categorical.quality : Categorical → Quality
    :=
  Aristotle.DeInterpretatione.Categorical.quality

def Categorical.contradictory : Categorical → Categorical
    :=
  Aristotle.DeInterpretatione.Categorical.contradictory

@[simp] theorem contradictory_involutive (c : Categorical) :
    c.contradictory.contradictory = c := by
  exact Aristotle.DeInterpretatione.Categorical.contradictory_involutive c

/--
Swap the subject and predicate terms of a categorical proposition.

This is a purely syntactic operation. It should not be confused with
Aristotelian conversion, which is only licensed for restricted forms.
-/
def Categorical.swapTerms : Categorical → Categorical
  | .A S P => .A P S
  | .E S P => .E P S
  | .I S P => .I P S
  | .O S P => .O P S

theorem subject_of_swapTerms (c : Categorical) :
    c.swapTerms.subject = c.predicate := by
  cases c with
  | A S P =>
      change P = P
      rfl
  | E S P =>
      change P = P
      rfl
  | I S P =>
      change P = P
      rfl
  | O S P =>
      change P = P
      rfl

theorem predicate_of_swapTerms (c : Categorical) :
    c.swapTerms.predicate = c.subject := by
  cases c with
  | A S P =>
      change S = S
      rfl
  | E S P =>
      change S = S
      rfl
  | I S P =>
      change S = S
      rfl
  | O S P =>
      change S = S
      rfl

theorem swapTerms_involutive (c : Categorical) :
    c.swapTerms.swapTerms = c := by
  cases c <;> rfl

/--
The assertoric forms Aristotle treats as simply convertible in the current
formalization.
-/
def Categorical.IsSimplyConvertible : Categorical → Prop
  | .E _ _ => True
  | .I _ _ => True
  | .A _ _ => False
  | .O _ _ => False

end Aristotle.PriorAnalytics
