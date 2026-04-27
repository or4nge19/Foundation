/-
  SPINOZA'S ETHICS V2.4: A BOURBAKI/MATHLIB4 FORMALIZATION

  Resolves all compilation errors from V2.0–V2.3:
    1. FullSubcategory → ObjectProperty.FullSubcategory (Mathlib4 refactor)
    2. fullSubcategoryInclusion → ObjectProperty.ι
    3. not_lt.mpr requires LinearOrder, but CompleteLattice only gives
       PartialOrder → use `not_lt_of_ge` (which only requires `Preorder`)
    4. le_top stuck OrderTop metavariable → annotate type explicitly
    5. Stuck AffectiveDynamics typeclass → explicit Mode/Perfection params
    6. ObjectProperty is `C → Prop` (a type alias), NOT an inductive —
       cannot use ⟨...⟩ anonymous constructor notation.
       Fix: define adequateProp as a plain function, not wrapped in ⟨⟩.

  Scholarly map:
    Della Rocca (PSR)        ⟹  Thin Category
    Gueroult (Immanence)     ⟹  Initial Object + Coslice
    Melamed (Parallelism)    ⟹  Categorical Equivalence (coherent)
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
═══════════════════════════════════════════════════════════════════ -/

/-- The Spinozist Universe: a category that is both thin and skeletal.
- **Thin** (`Quiver.IsThin`): at most one morphism X ⟶ Y (E1P29).
- **Skeletal**: isomorphic objects are equal, X ≅ Y → X = Y (E1P14). -/
class SpinozistUniverse (Entity : Type u) extends Category.{v} Entity where
  [thin : Quiver.IsThin Entity]
  skeletal : Skeletal Entity

attribute [instance] SpinozistUniverse.thin

/-! ═══════════════════════════════════════════════════════════════════
### PART II: SUBSTANCE, MONISM & IMMANENT CAUSATION (Gueroult)

God = Initial Object ⊥_ Entity.
  • E1P15: initial.to x — unique morphism to every entity.
  • E1P14: Any initial object IS God (by skeletality).
  • E1P18: Modes live in the coslice category Under God —
    a mode *is* the morphism God ⟶ X, not a standalone node.
═══════════════════════════════════════════════════════════════════ -/

section Substance

variable (Entity : Type u) [su : SpinozistUniverse.{u, v} Entity] [HasInitial Entity]

/-- E1D6: God is the initial object of the causal universe. -/
noncomputable def God : Entity := ⊥_ Entity

/-- E1P14 (Substance Monism, strongest form): any initial object
is *strictly equal to God* — not merely isomorphic.

Proof: initiality gives an isomorphism G ≅ God; skeletality
collapses it to identity. -/
theorem substance_monism (G : Entity) (hG : IsInitial G) : G = God Entity := by
  have hGod : IsInitial (God Entity) := initialIsInitial
  exact su.skeletal ⟨hG.uniqueUpToIso hGod⟩

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

Coherence conditions ensure the equivalences form a consistent system.
═══════════════════════════════════════════════════════════════════ -/

/-- Attributes form parallel, causally isolated categories connected
by structural equivalence, subject to coherence laws. -/
class AttributeParallelism (Attr : Type u) (AttrMode : Attr → Type u)
    [∀ a, Category.{v} (AttrMode a)]
    [∀ a, Quiver.IsThin (AttrMode a)] where
  equiv : ∀ (a b : Attr), AttrMode a ≌ AttrMode b
  /-- E1P10: Self-equivalence is the identity functor (up to nat iso). -/
  refl_coherence : ∀ (a : Attr),
    (equiv a a).functor ≅ 𝟭 (AttrMode a)
  /-- Transitivity: composing equiv a b then equiv b c gives equiv a c. -/
  trans_coherence : ∀ (a b c : Attr),
    (equiv a b).functor ⋙ (equiv b c).functor ≅ (equiv a c).functor

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

Perfection is a CompleteLattice. In Mathlib, every `Preorder` induces
a thin category via `Preorder.smallCategory` where `(A ⟶ B) ↔ (A ≤ B)`.

Since `CompleteLattice` extends down to `Preorder`, this instance is
available. The functor `potentia_actio` maps adequate modes into this
preorder category.

#### Mathlib4 API notes (V2.4)
- `ObjectProperty C` is defined as `C → Prop` (a type alias / abbrev),
  NOT as an inductive type. Therefore `⟨predicate⟩` anonymous
  constructor notation is INVALID. Use the predicate directly as a
  function instead.
- `ObjectProperty.FullSubcategory` and `ObjectProperty.ι` are the
  current Mathlib4 API for full subcategories and their inclusions.
- `not_lt_of_ge` only needs `Preorder`, not `LinearOrder`.
- `le_top` needs its type annotated to avoid stuck metavariables.
═══════════════════════════════════════════════════════════════════ -/

section AdequateSubcategory

variable (Entity : Type u) [SpinozistUniverse.{u, v} Entity] [HasInitial Entity]

/-- E3D1: A predicate selecting modes whose transitions arise purely
from the mode's own essence — Adequate Causation. -/
class HasAdequatePredicate (Entity : Type u)
    [SpinozistUniverse.{u, v} Entity] [HasInitial Entity] where
  /-- The predicate on modes (objects of the coslice Under God). -/
  IsAdequate : ModeSpace Entity → Prop

variable [HasAdequatePredicate.{u, v} Entity]

/-- An `ObjectProperty` packaging the adequacy predicate,
for use with Mathlib's `ObjectProperty.FullSubcategory` API.

Note: `ObjectProperty C` is just `C → Prop` (a type alias),
so we define this as a plain function — no constructor needed. -/
def adequateProp : ObjectProperty (ModeSpace Entity) :=
  fun m => HasAdequatePredicate.IsAdequate m

/-- The subcategory of Adequate Causation: those modes in ModeSpace
for which `IsAdequate` holds. This is a genuine subcategory — only
modes acting from their own essence live here.

Morphisms are inherited from ModeSpace (the coslice Under God),
restricted to adequate modes. -/
abbrev AdequateSubcat : Type _ :=
  (adequateProp Entity).FullSubcategory

/-- The faithful inclusion functor from the adequate subcategory
back into the full mode space. -/
noncomputable def adequateInclusion : AdequateSubcat Entity ⥤ ModeSpace Entity :=
  (adequateProp Entity).ι

instance : (adequateInclusion Entity).Faithful :=
  inferInstanceAs ((adequateProp Entity).ι.Faithful)

end AdequateSubcategory

section AffectiveDynamics

variable (Mode : Type u) [Category.{v} Mode]
variable (Perfection : Type u) [CompleteLattice Perfection]

/-- Affective Dynamics: a covariant functor from a category of modes
into the lattice of Perfection (viewed as a thin category via its
preorder).

Functoriality guarantees: if f : X ⟶ Y (an adequate internal cause),
then potentia(X) ≤ potentia(Y). This is the Conatus theorem.

The `Mode` parameter is intended to be instantiated with
`AdequateSubcat Entity`. External (inadequate) causes are outside
the functor's domain, so sadness remains possible externally but
is provably impossible internally. -/
class AffectiveDynamics (Mode : Type u) (Perfection : Type u)
    [Category.{v} Mode] [CompleteLattice Perfection] where
  potentia_actio : Mode ⥤ Perfection

variable [aff : AffectiveDynamics.{u, v} Mode Perfection]

/-- E3P11: Joy — a strict increase in perfection under an internal
transition. -/
def isJoy {X Y : Mode} (_ : X ⟶ Y) : Prop :=
  aff.potentia_actio.obj X < aff.potentia_actio.obj Y

/-- E3P11: Sadness — a strict decrease in perfection.
Impossible within Adequate Causation (see `conatus` below). -/
def isSadness {X Y : Mode} (_ : X ⟶ Y) : Prop :=
  aff.potentia_actio.obj Y < aff.potentia_actio.obj X

/-- **Conatus Theorem (E3P6 + E3P4):** Within Adequate Causation,
no internal morphism can decrease potentia.

Proof:
  1. The functor maps f : X ⟶ Y to a morphism
     potentia(X) ⟶ potentia(Y) in the preorder category of Perfection.
  2. In a preorder category, a morphism A ⟶ B is exactly a proof
     of A ≤ B (via `leOfHom`).
  3. So potentia(X) ≤ potentia(Y), which refutes potentia(Y) < potentia(X)
     via `not_lt_of_ge` (which only requires `Preorder`, not `LinearOrder`).

All type parameters are explicit to prevent stuck typeclass resolution. -/
theorem conatus {X Y : Mode} (f : X ⟶ Y) :
    ¬ isSadness Mode Perfection f := by
  unfold isSadness
  have h_le : aff.potentia_actio.obj X ≤ aff.potentia_actio.obj Y :=
    leOfHom (aff.potentia_actio.map f)
  exact not_lt_of_ge h_le

/-- **E5P3 Corollary:** Within adequate causation, the composition
of two joy-producing transitions is also joy-producing.

This follows from transitivity of `<` and functoriality. -/
theorem joy_composes {X Y Z : Mode} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : isJoy Mode Perfection f) (hg : isJoy Mode Perfection g) :
    isJoy Mode Perfection (f ≫ g) := by
  unfold isJoy at *
  exact lt_trans hf hg

end AffectiveDynamics

/-! ═══════════════════════════════════════════════════════════════════
### PART V: BLESSEDNESS & THE THIRD KIND OF KNOWLEDGE (E5P25–E5P42)

Blessedness (beatitudo) — the state where perfection is maximal.
═══════════════════════════════════════════════════════════════════ -/

section Blessedness

variable (Mode : Type u) [Category.{v} Mode]
variable (Perfection : Type u) [CompleteLattice Perfection]
variable [aff : AffectiveDynamics.{u, v} Mode Perfection]

/-- E5P27: Blessedness — a mode is blessed if its potentia is the
top element of the perfection lattice. -/
def IsBlessed (X : Mode) : Prop :=
  aff.potentia_actio.obj X = ⊤

/-- E5P42: A blessed mode cannot experience joy (there is no higher
perfection to transition to). Blessedness is beyond affect. -/
theorem blessed_no_joy {X Y : Mode} (f : X ⟶ Y)
    (hX : IsBlessed Mode Perfection X) : ¬ isJoy Mode Perfection f := by
  unfold isJoy IsBlessed at *
  rw [hX]
  exact not_top_lt

/-- E5P42: A blessed mode cannot experience sadness either.
This follows directly from the Conatus theorem — it holds for
ALL modes within Adequate Causation, regardless of blessedness. -/
theorem blessed_no_sadness {X Y : Mode} (f : X ⟶ Y) :
    ¬ isSadness Mode Perfection f :=
  conatus Mode Perfection f

/-- E5P33: The blessed mode is a fixed point of potentia — any
adequate transition from a blessed mode leads to another blessed mode.

Proof: By conatus, potentia cannot decrease. By maximality of ⊤,
it cannot increase. So potentia is preserved. -/
theorem blessed_stable {X Y : Mode} (f : X ⟶ Y)
    (hX : IsBlessed Mode Perfection X) : IsBlessed Mode Perfection Y := by
  unfold IsBlessed at *
  have h_le : aff.potentia_actio.obj X ≤ aff.potentia_actio.obj Y :=
    leOfHom (aff.potentia_actio.map f)
  rw [hX] at h_le
  exact le_antisymm (le_top (a := aff.potentia_actio.obj Y)) h_le

end Blessedness

/-! ═══════════════════════════════════════════════════════════════════
### ARCHITECTURAL SUMMARY (V2.4)

    God (⊥_ Entity)  — Initial Object (unique by substance_monism)
     │
     │  initial.to x  (unique — E1P15)
     ▼
    ModeSpace (Under God)  — Modes ARE morphisms (E1P18)
     │
     ├─ AdequateSubcat (ObjectProperty.FullSubcategory IsAdequate)
     │    │
     │    │  potentia_actio : AdequateSubcat ⥤ Perfection
     │    │  (covariant functor → Conatus guaranteed)
     │    │
     │    ├─ Joy possible, Sadness impossible (E3P6)
     │    ├─ Joy composes (E5P3 Corollary)
     │    ├─ Blessedness: potentia = ⊤ → beyond affect (E5P42)
     │    └─ Blessed stability: potentia = ⊤ is preserved (E5P33)
     │
     ├─ adequateInclusion : AdequateSubcat ⥤ ModeSpace  (Faithful)
     │
     └─ Inadequate Causes  — External, outside functor domain
          └─ Sadness possible here

    Attribute₁ ≌ Attribute₂  — Parallelism (E2P7)
      with refl_coherence and trans_coherence
    (causally sealed by Lean's type system — E1P10)
═══════════════════════════════════════════════════════════════════ -/

end SpinozaV2