/-
  SPINOZA'S ETHICS V2: A BOURBAKI/MATHLIB4 FORMALIZATION

  Resolves four critical bugs from V1:
    1. Perfection Paradox       → Restricted functoriality (Adequate Causation)
    2. Eradication of Sadness   → External causes excluded from functor domain
    3. Transitive ≠ Immanent    → Coslice (Under) categories
    4. Isomorphism ≠ Identity   → Skeletal category axiom

  Scholarly map:
    Della Rocca (PSR)        ⟹  Thin Category
    Gueroult (Immanence)     ⟹  Initial Object + Coslice
    Melamed (Parallelism)    ⟹  Categorical Equivalence
    Deleuze (Conatus)        ⟹  Covariant Functor into Lattice
-/

import Mathlib

open CategoryTheory Limits

universe u v

namespace SpinozaV2

/-! ═══════════════════════════════════════════════════════════════════
### PART I: THE CAUSAL UNIVERSE — THIN & SKELETAL

Spinoza's Radical PSR (Della Rocca): Causation, Conception, and
Inherence collapse into one relation. Necessitarianism (E1P29)
ensures at most one morphism between any two entities.

Strict Monism (E1P14) demands isomorphism ⟹ identity, i.e. the
category is Skeletal.

Note: `Quiver.IsThin` is a Prop-valued class with a `[Quiver V]`
prerequisite, and `Skeletal C` is a bare `Prop` (not a typeclass).
Neither can appear in an `extends` clause of a structure that also
extends `Category`. We therefore store both as explicit fields.
═══════════════════════════════════════════════════════════════════ -/

/-- The Spinozist Universe: a category that is both thin and skeletal.
- **Thin** (`Quiver.IsThin`): at most one morphism X ⟶ Y.
- **Skeletal**: isomorphic objects are equal (`X ≅ Y → X = Y`). -/
class SpinozistUniverse (Entity : Type u) extends Category.{v} Entity where
  [thin : Quiver.IsThin Entity]
  skeletal : Skeletal Entity

attribute [instance] SpinozistUniverse.thin

/-! ═══════════════════════════════════════════════════════════════════
### PART II: SUBSTANCE, MONISM & IMMANENT CAUSATION (Gueroult)

God = Initial Object ⊥_ Entity.
  • E1P15: initial.to x — unique morphism to every entity.
  • E1P14: Two initial objects are isomorphic; by skeletality, equal.
  • E1P18: Modes live in the coslice category Under God —
    a mode *is* the morphism God ⟶ X, not a standalone node.
═══════════════════════════════════════════════════════════════════ -/

section Substance

variable (Entity : Type u) [su : SpinozistUniverse.{u, v} Entity] [HasInitial Entity]

/-- E1D6: God is the initial object of the causal universe. -/
noncomputable def God : Entity := ⊥_ Entity

/-- E1P14 (Substance Monism, strong form): any two initial objects
are *strictly equal* — not merely isomorphic.

Proof: initiality gives an isomorphism; skeletality collapses it
to identity. -/
theorem substance_monism (G1 G2 : Entity)
    (h1 : IsInitial G1) (h2 : IsInitial G2) : G1 = G2 :=
  su.skeletal ⟨h1.uniqueUpToIso h2⟩

/-- E1P15 (Inherence): "Whatever is, is in God."
The unique morphism from the initial object to any entity. -/
noncomputable def inherence (x : Entity) : God Entity ⟶ x :=
  initial.to x

/-- E1P18 (Immanent Causation): The mode space is the coslice
category `Under God`. A mode is not an independent entity — it
*is* the generative morphism `God ⟶ X` itself. -/
def ModeSpace : Type _ := Under (God Entity)

noncomputable instance : Category (ModeSpace Entity) :=
  inferInstanceAs (Category (Under (God Entity)))

/-- Lift any entity into the Mode Space via its inherence morphism. -/
noncomputable def toMode (x : Entity) : ModeSpace Entity :=
  Under.mk (inherence Entity x)

end Substance

/-! ═══════════════════════════════════════════════════════════════════
### PART III: ATTRIBUTES & PARALLELISM (Melamed)

Lean's type system enforces the causal barrier (E1P10): no morphism
crosses attribute boundaries. Parallelism (E2P7) is recovered as
a categorical equivalence ≌ between attribute categories.
═══════════════════════════════════════════════════════════════════ -/

/-- Attributes form parallel, causally isolated categories connected
by structural equivalence. -/
class AttributeParallelism (Attr : Type u) (AttrMode : Attr → Type u)
    [∀ a, Category.{v} (AttrMode a)]
    [∀ a, Quiver.IsThin (AttrMode a)] where
  equiv : ∀ (a b : Attr), AttrMode a ≌ AttrMode b

section Attributes

variable {Attr : Type u} {AttrMode : Attr → Type u}
variable [∀ a, Category.{v} (AttrMode a)]
variable [∀ a, Quiver.IsThin (AttrMode a)]
variable [par : AttributeParallelism Attr AttrMode]

/-- E2P7S: The idea of a body — structural transport across attributes. -/
noncomputable def ideaOf {Thought Extension : Attr}
    (body : AttrMode Extension) : AttrMode Thought :=
  (par.equiv Extension Thought).functor.obj body

/-- Parallel Causation: physical cause ↦ logical deduction. -/
noncomputable def parallelCausation {Thought Extension : Attr}
    {A B : AttrMode Extension} (cause : A ⟶ B) :
    ideaOf (Thought := Thought) A ⟶ ideaOf (Thought := Thought) B :=
  (par.equiv Extension Thought).functor.map cause

end Attributes

/-! ═══════════════════════════════════════════════════════════════════
### PART IV: CONATUS & THE PHYSICS OF AFFECTS (Deleuze)

Perfection is a CompleteLattice. In mathlib, a Preorder is
automatically a thin category where (A ⟶ B) ↔ (A ≤ B).

The potentia functor is covariant but RESTRICTED to Adequate
Causation (internal self-activity). This prevents:
  • The Perfection Paradox (God as least perfect).
  • The Eradication of Sadness.

Sadness arises from *inadequate* (external) causes, which are
NOT in the functor's domain.
═══════════════════════════════════════════════════════════════════ -/

/-- Adequate Causation: the subcategory of internal state-transitions
where a mode acts from its own essence (E3D1). -/
class AdequateCausation (Mode : Type u) extends Category.{v} Mode

section Affects

variable {Mode : Type u} [AdequateCausation.{u, v} Mode]
variable {Perfection : Type u} [CompleteLattice Perfection]

/-- Affective Dynamics: a covariant functor from Adequate Causation
into the lattice of Perfection.

Functoriality guarantees: if f : X ⟶ Y (internal cause), then
potentia(X) ≤ potentia(Y). This is the Conatus theorem. -/
class AffectiveDynamics (Mode : Type u) (Perfection : Type u)
    [AdequateCausation.{u, v} Mode] [CompleteLattice Perfection] where
  potentia_actio : Mode ⥤ Perfection

variable [aff : AffectiveDynamics.{u, v} Mode Perfection]

/-- E3P11: Joy — a strict increase in perfection. -/
def isJoy {X Y : Mode} (_ : X ⟶ Y) : Prop :=
  aff.potentia_actio.obj X < aff.potentia_actio.obj Y

/-- E3P11: Sadness — a strict decrease in perfection.
Impossible within Adequate Causation (see `conatus` below). -/
def isSadness {X Y : Mode} (_ : X ⟶ Y) : Prop :=
  aff.potentia_actio.obj Y < aff.potentia_actio.obj X

/-- **Conatus Theorem (E3P6 + E3P4):** Within Adequate Causation,
no internal morphism can decrease potentia.

Proof: The functor maps f : X ⟶ Y to a morphism
potentia(X) ⟶ potentia(Y) in the preorder category of Perfection.
By `leOfHom`, this yields potentia(X) ≤ potentia(Y),
contradicting potentia(Y) < potentia(X). -/
theorem conatus {X Y : Mode} (f : X ⟶ Y) : ¬ isSadness f := by
  intro h_sad
  have h_mor := aff.potentia_actio.map f
  have h_le : aff.potentia_actio.obj X ≤ aff.potentia_actio.obj Y :=
    leOfHom h_mor
  exact not_lt.mpr h_le h_sad

end Affects

/-! ═══════════════════════════════════════════════════════════════════
### ARCHITECTURAL SUMMARY

    God (⊥_ Entity)  — Initial Object
     │
     │  initial.to x  (unique — E1P15)
     ▼
    ModeSpace (Under God)  — Modes ARE morphisms (E1P18)
     │
     ├─ AdequateCausation  — Internal subcategory
     │    │
     │    │  potentia_actio : Mode ⥤ Perfection
     │    │  (covariant functor → Conatus guaranteed)
     │    │
     │    └─ Joy possible, Sadness impossible (E3P6)
     │
     └─ Inadequate Causes  — External, non-functorial
          └─ Sadness possible here

    Attribute₁ ≌ Attribute₂  — Parallelism (E2P7)
    (causally sealed by Lean's type system — E1P10)
═══════════════════════════════════════════════════════════════════ -/

end SpinozaV2