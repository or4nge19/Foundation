import Mathlib

universe u v

namespace Philosophy.Kant.Laywine

/-- An abstract representation system for the Herz-letter problem. -/
structure RepresentationSystem where
  Noumenon : Type u
  Representation : Type v
  represent : Noumenon → Representation

/-- Divine understanding is archetypal when representation is exhaustive and faithful. -/
def IntellectusArchetypus (R : RepresentationSystem) : Prop :=
  Function.Bijective R.represent

/-- Finite understanding is ectypal when representation preserves distinctions
without claiming exhaustive production of its objects. -/
def IntellectusEctypus (R : RepresentationSystem) : Prop :=
  Function.Injective R.represent

theorem archetypus_implies_ectypus {R : RepresentationSystem}
    (h : IntellectusArchetypus R) : IntellectusEctypus R :=
  h.1

namespace Categorical

open CategoryTheory

/-- The categorical version of the archetypal intellect: equivalence of categories. -/
def IntellectusArchetypus
    {Noumenon : Type u} {Representation : Type v}
    [Category Noumenon] [Category Representation]
    (F : Functor Noumenon Representation) : Prop :=
  F.IsEquivalence

/-- The categorical version of the ectypal intellect: faithful but not necessarily
creative representation. -/
def IntellectusEctypus
    {Noumenon : Type u} {Representation : Type v}
    [Category Noumenon] [Category Representation]
    (F : Functor Noumenon Representation) : Prop :=
  F.Faithful

end Categorical

end Philosophy.Kant.Laywine
