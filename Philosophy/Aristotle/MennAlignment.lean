import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Philosophy.Aristotle.PriorAnalytics
import Philosophy.Aristotle.PhysicsI
import Philosophy.Aristotle.InquiryBoundary
import Philosophy.Aristotle.Core

namespace Aristotle.MennAlignment

/-!
# Consolidated Menn map (path, boundary, being)

This module is the intentional home for **cross-layer** consolidations of Stephen
Menn’s reconstructions that are already *distributed* across the formalization.
It is not a new science or a second dialectic: it only makes explicit what
Menn would keep *distinct* and what he would treat as *analogous*.

For an **uncompromising** map of how this repo relates to Menn’s book *The Aim and
the Argument of Aristotle’s Metaphysics* (PDF sections `I*`, `II*`, `IIIa2` in
`Philosophy/Aristotle/`, as cross-cited from `AOMSB1.md`), and for what the Lean
**does not** pretend to formalize, see `Menn_AimAndArgument_Map.md`.

## Physics I.1, Reading B (`Path to Principles.md`, parallel PDF `Ia1*.pdf` in this folder)

Menn’s Reading B: we do not first win principles by decomposing a whole into
foreign parts. The same item underlies a **confused-universal** description
and, after articulation, a **sharper particular** label; the class
`Aristotle.Physics.PathToPrinciples` is that constraint in `PhysicsI.lean`.
Here we add a tiny **order structure** (mathlib `PartialOrder` on
`DescriptionStage`, with `descriptionStage_le_total` making the 2-point order
*totally* ordered in the logical sense) so "path to principled clarity" is
literally one direction on a chain, not a vague metaphor, not a foreign
`στοιχεῖον` decomposition, and not an extra ontological positing. Nothing here
lifts the stage order into **Δ7**-style *axes* of being (that is
`SensesOfBeing.lean` and *AOMSB1*, with the `Ia`–`III` PDFs in this folder as
readers’ parallel texts).

## `hoti` / `dioti` and Posterior "whether" / "why" (`InquiryBoundary.lean`)

Menn’s Physics I.1 “path to the archai” and his use of the NE/Posterior
Analytics *parallel* (roughly: the ὅτι / the διότι) concern **how scientific
knowledge of principles is acquired and ordered** (Menn’s Path to Principles
cites *NE* I 4 and *Post. An.* on starting from the ὅτι to reach the διότι
alongside the Physics I.1 *ὁδός*). That parallel motivates our **re-use of the
same `hoti`/`dioti` vocabulary** in `InquiryBoundary`, but it is still a
different *formal axis* from **Reading B** description stages, even when the
same English word “knowledge of principles” appears in the prose. In Lean,
`PathToPrinciples` and the `InquiryAim` split on `Problem` vs `WhyQuestion` are
different formal predicates. That remains true when the *same* categorical
sentence is re-asked as a `WhyQuestion` (`InquiryBoundary.problemWhyQuestion?`):
inquiry rôle, not description stage, has changed.

**Do not conflate** `DescriptionStage` with `InquiryAim` or with Smith-style
`WhyQuestion`: the former tracks **clarity of a principle-description**; the
latter track **inquiry rôle and demonstrative aim**.

## D7, many senses of being (`AOMSB1.md` and `SensesOfBeing.lean`)

Menn (AOMSB1) treats the Δ7 program as the backbone for EZHQ. In this
repository, categorial placement, per-accidens, modality, and truth are kept
*non-collapsed* in `BeingSenses` and `BeingProfile` rather than flattened
into a single "being" predicate. See module docstrings there.

## Symposia / Oxford PDFs in `Philosophy/Aristotle/`

Editions/parallel texts such as `Ia2.pdf` … `IIIa2.pdf` and related appendices
live in-repo as *reference* material for human readers; the Lean work tracks
Menn’s reading through the above modules, not through OCR of the PDFs.
-/

open Aristotle.Categories
open Aristotle.Dialectic
open Aristotle.InquiryBoundary
open Aristotle.PosteriorAnalytics
open Aristotle.PriorAnalytics
open Aristotle.Physics

@[simp]
def descriptionStageToNat (s : DescriptionStage) : ℕ :=
  match s with
  | .confusedUniversal => 0
  | .articulatedParticular => 1

theorem descriptionStageToNat_injective : Function.Injective descriptionStageToNat := by
  intro a b h
  match a, b with
  | .confusedUniversal, .confusedUniversal => rfl
  | .articulatedParticular, .articulatedParticular => rfl
  | .confusedUniversal, .articulatedParticular => simp [descriptionStageToNat] at h
  | .articulatedParticular, .confusedUniversal => simp [descriptionStageToNat] at h

/--
Epistemic direction on Menn’s Reading B axis: from confused-universal
presentation toward articulated-particular *labels of the same* principle
(`PathToPrinciples.preserves_principle`).

Renders Reading B as the inherited `PartialOrder` of the two-point subchain
\(0<1\) in `ℕ` via `descriptionStageToNat`. The companion theorem
`descriptionStage_le_total` is the *logical* “linearity” of a two-point order,
matching Menn’s single *ὁδός* to clearer *ἀρχαί*-recognition (no incomparable
branching in this model). A `LinearOrder` *class instance* is intentionally omitted: it pulls in Mathlib’s
bundled `min` / `max` / `compare` / `DecidableLE` for `Min`+`Max`+`Ord`, and this
2-type does not need that.

For the **Δ7** program (many *ways* in which a thing is said to be, without
flattening them: *AOMSB1*, `SensesOfBeing.lean`, and the `Ig*` and related PDFs
here as parallel human editions), the right multi-axis structure is
`BeingProfile` / `BeingSenses`, not a “being”-reading of `DescriptionStage`
alone.
-/
instance menn_readingBPartialOrder : PartialOrder DescriptionStage where
  le a b := descriptionStageToNat a ≤ descriptionStageToNat b
  le_refl a := by
    cases a <;> simp
  le_trans a b c hab hbc := by
    exact Nat.le_trans hab hbc
  le_antisymm a b hab hba := by
    have hnat : descriptionStageToNat a = descriptionStageToNat b := Nat.le_antisymm hab hba
    exact descriptionStageToNat_injective hnat

theorem descriptionStage_le_total (a b : DescriptionStage) : a ≤ b ∨ b ≤ a := by
  cases a <;> cases b
  · left; apply le_refl
  · left; native_decide
  · right; native_decide
  · left; apply le_refl

theorem confused_le_articulated :
    DescriptionStage.confusedUniversal ≤ DescriptionStage.articulatedParticular := by
  decide

/--
Reading B as a **bounded** two-point chain: least = confused-universal, greatest =
articulate-particular. Same order as `menn_readingBPartialOrder`, packaged with
mathlib’s `⊥`/`⊤` so the “from what is clearer to us to what is clearer by
nature” *ὁδός* has a literal extremal form without importing extra physics axioms.
-/
instance menn_readingBBot : Bot DescriptionStage where
  bot := .confusedUniversal

instance menn_readingBOrderBot : OrderBot DescriptionStage where
  bot_le := by
    intro a
    cases a
    · apply le_refl
    · exact confused_le_articulated

instance menn_readingBTop : Top DescriptionStage where
  top := .articulatedParticular

instance menn_readingBOrderTop : OrderTop DescriptionStage where
  le_top := by
    intro a
    cases a
    · exact confused_le_articulated
    · apply le_refl

instance menn_readingBBoundedOrder : BoundedOrder DescriptionStage := {}

/-- The canonical 2-point chain (Reading B) as a `Fin 2` index, for mathlib order transport. -/
def descriptionStageEquivFin2 : DescriptionStage ≃ Fin 2 where
  toFun s :=
    ⟨descriptionStageToNat s, by
      cases s
      · exact Nat.zero_lt_two
      · exact Nat.one_lt_two⟩
  invFun
    | ⟨0, _⟩ => .confusedUniversal
    | ⟨1, _⟩ => .articulatedParticular
  left_inv := by
    intro s
    cases s <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> { ext; simp [descriptionStageToNat] }

theorem descriptionStageEquivFin2_val (s : DescriptionStage) :
    (descriptionStageEquivFin2 s : ℕ) = descriptionStageToNat s := by
  cases s <;> simp [descriptionStageEquivFin2, descriptionStageToNat]

/-!
## Mathlib model: `DescriptionStage` as the standard 2-element chain

`RelIso` / `OrderIso` to `Fin 2` (with the inherited `≤` on `Fin` from
`Nat`) makes explicit that Menn’s Reading B axis is not an ad hoc order
invented in this file: it is the same order type as the first nontrivial
finite total order in mathlib. This is a **structural** bridge only: it does
not identify description stages with Γ-style senses of “being” (see the
`PartialOrder` docstring above and `Menn_AimAndArgument_Map.md`).
-/

theorem descriptionStageEquivFin2_monotone : Monotone (descriptionStageEquivFin2 : DescriptionStage → Fin 2) := by
  intro a b hab
  rw [Fin.le_iff_val_le_val, descriptionStageEquivFin2_val, descriptionStageEquivFin2_val]
  exact hab

theorem descriptionStageEquivFin2_symm_monotone :
    Monotone (descriptionStageEquivFin2.symm : Fin 2 → DescriptionStage) := by
  intro i j hij
  rw [Fin.le_iff_val_le_val] at hij
  fin_cases i <;> fin_cases j
  · apply le_refl
  · exact confused_le_articulated
  · exfalso
    norm_num at hij
  · apply le_refl

/-- Order isomorphism: Reading B = the two-point chain `({0,1}, ≤)` in `Fin 2`. -/
def descriptionStageOrderIsoFin2 : DescriptionStage ≃o Fin 2 :=
  descriptionStageEquivFin2.toOrderIso
    descriptionStageEquivFin2_monotone
    descriptionStageEquivFin2_symm_monotone

@[simp] theorem descriptionStageOrderIsoFin2_toEquiv :
    (descriptionStageOrderIsoFin2 : DescriptionStage ≃o Fin 2).toEquiv = descriptionStageEquivFin2 :=
  Equiv.toOrderIso_toEquiv _ _ _

@[simp] theorem descriptionStageOrderIsoFin2_apply (s : DescriptionStage) : descriptionStageOrderIsoFin2 s = descriptionStageEquivFin2 s :=
  rfl

theorem descriptionStageOrderIsoFin2_bot : descriptionStageOrderIsoFin2 ⊥ = (0 : Fin 2) := by
  rw [show (⊥ : DescriptionStage) = .confusedUniversal from rfl, descriptionStageOrderIsoFin2_apply]
  ext
  simp [descriptionStageEquivFin2, descriptionStageToNat]

theorem descriptionStageOrderIsoFin2_top : descriptionStageOrderIsoFin2 ⊤ = (1 : Fin 2) := by
  rw [show (⊤ : DescriptionStage) = .articulatedParticular from rfl, descriptionStageOrderIsoFin2_apply]
  ext
  simp [descriptionStageEquivFin2, descriptionStageToNat]

/-!
### Universal property (OrderHom to an arbitrary `PartialOrder`)

A monotone map out of a two-point total order is nothing more than a
non-decreasing *pair* in the codomain. Here `DescriptionStage` is the same
2-chain as `Fin 2` (via `descriptionStageOrderIsoFin2`); the lemma family below
makes the same fact explicit without a detour through `Fin`.

This is order theory, not a reduction of the ὅτι/διότι *or* the Posterior
*middle* to Reading B: `InquiryBoundary.lean` keeps inquiry rôles on a
separate axis from `DescriptionStage` (see the module prologue and
`reaskedWhyAim_ne_problemAim`).

(If Menn and Smith "agree" on anything in this neighbourhood, it is a negative
one: a single **step in clarity of principle-description** must not be
assimilated, without new axioms, to a demonstrative *middle* or to a
relabelled *why-question* role.)
-/

/-- A pair `p ≤ q` in `P` is exactly one monotone `DescriptionStage → P`: the
Reading B step, mapped to that step. -/
def orderHomOfReadingB {P : Type*} [PartialOrder P] (p q : P) (hle : p ≤ q) : DescriptionStage →o P where
  toFun
    | .confusedUniversal => p
    | .articulatedParticular => q
  monotone' := by
    intro a b hab
    cases a <;> cases b
    · apply le_refl
    · exact hle
    ·
      exfalso
      simp [menn_readingBPartialOrder, descriptionStageToNat] at hab
    · apply le_refl

@[simp] theorem orderHomOfReadingB_apply {P : Type*} [PartialOrder P] (p q : P) (hle : p ≤ q) (s : DescriptionStage) :
    (orderHomOfReadingB p q hle) s = match s with
      | .confusedUniversal => p
      | .articulatedParticular => q := rfl

@[simp] theorem orderHomOfReadingB_apply_bot {P : Type*} [PartialOrder P] (p q : P) (hle : p ≤ q) :
    orderHomOfReadingB p q hle ⊥ = p := rfl

@[simp] theorem orderHomOfReadingB_apply_top {P : Type*} [PartialOrder P] (p q : P) (hle : p ≤ q) :
    orderHomOfReadingB p q hle ⊤ = q := rfl

theorem orderHomOfReadingB_injective_endpoints {P : Type*} [PartialOrder P] (p q p' q' : P) (hle : p ≤ q) (hle' : p' ≤ q')
    (heq : orderHomOfReadingB p q hle = orderHomOfReadingB p' q' hle') : p = p' ∧ q = q' := by
  have hp := congrArg (fun w : DescriptionStage →o P => w ⊥) heq
  have ht := congrArg (fun w : DescriptionStage →o P => w ⊤) heq
  exact ⟨by simpa using hp, by simpa using ht⟩

/-- Every `OrderHom` from the Reading B chain is determined by the endpoints, hence is
`orderHomOfReadingB` of those endpoints and the necessary `f ⊥ ≤ f ⊤`. -/
theorem orderHomOfReadingB_eq {P : Type*} [PartialOrder P] (f : DescriptionStage →o P) :
    f = orderHomOfReadingB (f ⊥) (f ⊤) (f.monotone (OrderTop.le_top ⊥)) := by
  ext s
  cases s <;> rfl

theorem orderHom_readingB_ext {P : Type*} [PartialOrder P] {f g : DescriptionStage →o P} (h₀ : f ⊥ = g ⊥) (h₁ : f ⊤ = g ⊤) :
    f = g := by
  ext s
  cases s
  · exact h₀
  · exact h₁

/-!
`Equiv` of `OrderHom` spaces: transport along `DescriptionStage ≃o Fin 2`. This
packages the “same 2-point chain, two labellings” idea from mathlib: once the
`OrderIso` to `Fin 2` is fixed, *precomposition* yields a *bijection* of order
maps out of the two types, not just an inclusion of the endpoint construction
`orderHomOfReadingB` (which is the *special* `Fin` case: `0` and `1` in place of
`DescriptionStage`’s constructors). Still no merge with the ὅτι/διότι axis or
Smith on *demonstrative* middles: those stay in the analytics and
`InquiryBoundary` layers.
-/

/-- Precomposition with `descriptionStageOrderIsoFin2` (and precomposition the
other way with its `symm`) is a bijection between `OrderHom` spaces. -/
def orderHomEquivReadingBFin2 (P : Type*) [PartialOrder P] : (DescriptionStage →o P) ≃ (Fin 2 →o P) where
  toFun f := f.comp (descriptionStageOrderIsoFin2.symm : Fin 2 →o DescriptionStage)
  invFun g := g.comp (descriptionStageOrderIsoFin2 : DescriptionStage →o Fin 2)
  left_inv f := by
    ext a
    exact congrArg f (OrderIso.symm_apply_apply descriptionStageOrderIsoFin2 a)
  right_inv g := by
    ext a
    exact congrArg g (OrderIso.apply_symm_apply descriptionStageOrderIsoFin2 a)

theorem orderHomEquivReadingBFin2_toFun_apply {P : Type*} [PartialOrder P] (f : DescriptionStage →o P) (i : Fin 2) :
    (orderHomEquivReadingBFin2 P f) i = f (descriptionStageOrderIsoFin2.symm i) := rfl

theorem orderHomEquivReadingBFin2_invFun_apply {P : Type*} [PartialOrder P] (g : Fin 2 →o P) (s : DescriptionStage) :
    (orderHomEquivReadingBFin2 P).symm g s = g (descriptionStageOrderIsoFin2 s) := rfl

/-!
### Rank as `OrderHom` into `ℕ`, and *rigidity* of the 2-point chain

The “rank” of a `DescriptionStage` in `ℕ` (via `descriptionStageToNat`) is
exactly a bundled order homomorphism: the unique order map `DescriptionStage →o ℕ`
with endpoints `0` and `1` in the **standard** order on `ℕ`.

Separately, any *order* automorphism of `DescriptionStage` is trivial. On a
bounded 2-point chain there is no nontrivial order-theoretic “rebranding” of
confused vs articulate: the directed Reading B axis is *rigid*. This is not a
claim that physics or *first philosophy* cannot re-express the *same* principle
differently at the *content* level (`PathToPrinciples` already fixes that
non-collapse); it is only a fact about the **skeleton** `DescriptionStage` and
`mathlib`’s `OrderIso`.
-/

def descriptionStageRankHom : DescriptionStage →o ℕ :=
  orderHomOfReadingB 0 1 (by norm_num : (0 : ℕ) ≤ 1)

theorem descriptionStageRankHom_eq_descriptionStageToNat (s : DescriptionStage) :
    (descriptionStageRankHom : DescriptionStage → ℕ) s = descriptionStageToNat s := by
  cases s <;> rfl

/-- The canonical numeric rank: `0` for the bottom stage, `1` for the top. -/
theorem descriptionStageRankHom_apply (s : DescriptionStage) : descriptionStageRankHom s = descriptionStageToNat s :=
  descriptionStageRankHom_eq_descriptionStageToNat s

/-- On Reading B, the standard `0/1` rank into `ℕ` is determined by the endpoints (cf. `orderHomOfReadingB_eq`). -/
theorem eq_descriptionStageRankHom_of_map_bot_map_top
    (f : DescriptionStage →o ℕ) (hbot : f ⊥ = 0) (htop : f ⊤ = 1) : f = descriptionStageRankHom := by
  have h0 : f DescriptionStage.confusedUniversal = 0 := by
    simpa [menn_readingBBot, Bot.bot] using hbot
  have h1' : f DescriptionStage.articulatedParticular = 1 := by
    simpa [menn_readingBTop, Top.top] using htop
  refine OrderHom.ext f descriptionStageRankHom (funext fun s : DescriptionStage => ?_)
  cases s
  · simp [h0, descriptionStageRankHom_apply, descriptionStageToNat]
  · simp [h1', descriptionStageRankHom_apply, descriptionStageToNat]

theorem orderIso_readingB_map_top (e : DescriptionStage ≃o DescriptionStage) : e ⊤ = ⊤ := by
  have hbot : e ⊥ = ⊥ := OrderIso.map_bot e
  cases h : e ⊤
  ·
    exfalso
    have heq : e ⊤ = e ⊥ := h.trans hbot.symm
    have hbad : ⊤ = ⊥ := e.injective heq
    have hbad' : (DescriptionStage.articulatedParticular) = (DescriptionStage.confusedUniversal) := by
      simp [menn_readingBTop, menn_readingBBot] at hbad ⊢
    cases hbad'
  ·
    simp [menn_readingBTop]

theorem orderIso_readingB_eq_refl (e : DescriptionStage ≃o DescriptionStage) : e = OrderIso.refl _ := by
  ext x
  cases x
  · exact OrderIso.map_bot e
  · exact orderIso_readingB_map_top e

theorem confused_stage_eq_bot
    {Item : Type} [PathToPrinciples Item] (d : PrincipleDescription Item)
    (h : d.stage = .confusedUniversal) : d.stage = ⊥ := by
  have heq : (DescriptionStage.confusedUniversal : DescriptionStage) = ⊥ := rfl
  exact h.trans heq.symm

theorem articulate_principleDescription_stage_eq_top
    {Item : Type} [PathToPrinciples Item] (d : PrincipleDescription Item)
    (h : d.stage = .confusedUniversal) :
    (PathToPrinciples.articulate d).stage = ⊤ := by
  simpa [menn_readingBTop] using PathToPrinciples.articulate_sharpens d h

/--
Along Menn’s Physics I.1, Reading B, a confused `PrincipleDescription` sits at the
bottom of the epistemic chain and `PathToPrinciples.articulate` carries it to the
top (sharper label at the `⊤` stage).
-/
theorem readingB_bot_to_top_stages
    {Item : Type} [PathToPrinciples Item] (d : PrincipleDescription Item)
    (h : d.stage = .confusedUniversal) :
    d.stage = ⊥ ∧ (PathToPrinciples.articulate d).stage = ⊤ :=
  ⟨confused_stage_eq_bot d h, articulate_principleDescription_stage_eq_top d h⟩

/--
Reading B in one conjunction: from confused description **same underlying item**
(`PathToPrinciples.preserves_principle`), description stages run `⊥` → `⊤` on the
epistemic order. This is the Lean condensation of Menn’s “same *archai*, clearer
articulation” thesis—**not** a claim about causes of *being qua being* (see
`Menn_AimAndArgument_Map.md`).
-/
theorem readingB_stages_and_samePrinciple
    {Item : Type} [PathToPrinciples Item] (d : PrincipleDescription Item)
    (h : d.stage = .confusedUniversal) :
    d.stage = ⊥ ∧
      (PathToPrinciples.articulate d).stage = ⊤ ∧
      (PathToPrinciples.articulate d).principle = d.principle :=
  ⟨confused_stage_eq_bot d h,
    articulate_principleDescription_stage_eq_top d h,
    PathToPrinciples.preserves_principle d⟩

/--
Along Menn’s Physics I.1, Reading B, articulation never moves a description
"backward" on the epistemic chain: a confused `PrincipleDescription` is at
most as articulate as its image under `PathToPrinciples.articulate`.
(When the input is not confused, we make no content claim: the class
only forces the confused case.)
-/
theorem le_principleDescription_self_of_confused
    {Item : Type} [PathToPrinciples Item] (d : PrincipleDescription Item)
    (h : d.stage = .confusedUniversal) :
    d.stage ≤ (PathToPrinciples.articulate d).stage := by
  have hart := PathToPrinciples.articulate_sharpens d h
  have heq : (PathToPrinciples.articulate d).stage = .articulatedParticular := hart
  rw [h, heq]
  exact confused_le_articulated

/-!
## `InquiryAim` as the same 2-point *chain* (Posterior / Core; Smith-parallel *role*), not the same *predicates*

`Philosophy.Aristotle.Core.InquiryAim` (ὅτι/διότι) and `DescriptionStage` (Menn, Reading
B) are *different* inductive types, used in different subsystems: the former
indexes **inquiry rôle and demonstrative aim** (`InquiryBoundary`, *Post. An.*),
the latter the **clarity of a single principle’s description in Physics I.1
Reading B** (`PathToPrinciples`).

**They share only the order-theoretic skeleton of a 2-point chain** indexed by
`0 < 1` in `ℕ`. The explicit `OrderIso` below, built from two `OrderIso`s to
`Fin 2` in mathlib, makes that *shape* isomorphism concrete. It is **not** a
license to identify **dialectical** `hoti` with *physics-layer* "confused
universal" or to reduce **Smith-style** *demonstrative* middles (`Term`, figures
in `PosteriorAnalytics`) to this axis: those are separate formal layers (see
`reaskedWhyAim_ne_problemAim` just below, and
`InquiryBoundary.problemWhyQuestion_differentAim_of_statement`).
Uses `Philosophy.Aristotle.Core.InquiryAim` throughout to avoid ambiguity with
re-exported names in `Dialectic` / `PosteriorAnalytics` namespaces.
-/

@[simp]
def inquiryAimToNat (a : Philosophy.Aristotle.Core.InquiryAim) : ℕ :=
  match a with
  | .hoti => 0
  | .dioti => 1

theorem inquiryAimToNat_injective : Function.Injective inquiryAimToNat := by
  intro a b h
  match a, b with
  | .hoti, .hoti => rfl
  | .dioti, .dioti => rfl
  | .hoti, .dioti => simp [inquiryAimToNat] at h
  | .dioti, .hoti => simp [inquiryAimToNat] at h

instance inquiryAim2PointPartialOrder : PartialOrder Philosophy.Aristotle.Core.InquiryAim where
  le a b := inquiryAimToNat a ≤ inquiryAimToNat b
  le_refl a := by
    cases a <;> simp
  le_trans a b c hab hbc := Nat.le_trans hab hbc
  le_antisymm a b hab hba := by
    have hnat : inquiryAimToNat a = inquiryAimToNat b := Nat.le_antisymm hab hba
    exact inquiryAimToNat_injective hnat

theorem hoti_le_dioti :
    (Philosophy.Aristotle.Core.InquiryAim.hoti : Philosophy.Aristotle.Core.InquiryAim) ≤
      Philosophy.Aristotle.Core.InquiryAim.dioti := by
  simp [inquiryAim2PointPartialOrder, inquiryAimToNat]

instance inquiryAim2PointBot : Bot Philosophy.Aristotle.Core.InquiryAim where
  bot := .hoti

instance inquiryAim2PointOrderBot : OrderBot Philosophy.Aristotle.Core.InquiryAim where
  bot_le a := by
    cases a
    · apply le_refl
    · exact hoti_le_dioti

instance inquiryAim2PointTop : Top Philosophy.Aristotle.Core.InquiryAim where
  top := .dioti

instance inquiryAim2PointOrderTop : OrderTop Philosophy.Aristotle.Core.InquiryAim where
  le_top a := by
    cases a
    · exact hoti_le_dioti
    · apply le_refl

instance inquiryAim2PointBounded : BoundedOrder Philosophy.Aristotle.Core.InquiryAim := {}

def inquiryAimEquivFin2 : Philosophy.Aristotle.Core.InquiryAim ≃ Fin 2 where
  toFun a :=
    ⟨inquiryAimToNat a, by
      cases a
      · exact Nat.zero_lt_two
      · exact Nat.one_lt_two⟩
  invFun
    | ⟨0, _⟩ => .hoti
    | ⟨1, _⟩ => .dioti
  left_inv := by
    intro a
    cases a <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> { ext; simp [inquiryAimToNat] }

theorem inquiryAimEquivFin2_val (a : Philosophy.Aristotle.Core.InquiryAim) :
    (inquiryAimEquivFin2 a : ℕ) = inquiryAimToNat a := by
  cases a <;> simp [inquiryAimEquivFin2, inquiryAimToNat]

theorem inquiryAimEquivFin2_monotone :
    Monotone (inquiryAimEquivFin2 : Philosophy.Aristotle.Core.InquiryAim → Fin 2) := by
  intro a b hab
  rw [Fin.le_iff_val_le_val, inquiryAimEquivFin2_val, inquiryAimEquivFin2_val]
  exact hab

theorem inquiryAimEquivFin2_symm_monotone :
    Monotone (inquiryAimEquivFin2.symm : Fin 2 → Philosophy.Aristotle.Core.InquiryAim) := by
  intro i j hij
  rw [Fin.le_iff_val_le_val] at hij
  fin_cases i <;> fin_cases j
  · apply le_refl
  · exact hoti_le_dioti
  · exfalso; simp at hij
  · apply le_refl

def inquiryAimOrderIsoFin2 : Philosophy.Aristotle.Core.InquiryAim ≃o Fin 2 :=
  inquiryAimEquivFin2.toOrderIso inquiryAimEquivFin2_monotone inquiryAimEquivFin2_symm_monotone

/-- The Core `0/1` tag on `InquiryAim` agrees with the `Fin 2` coordinate: pulling back along
`inquiryAimOrderIsoFin2.symm` is the same numerals as for `DescriptionStage` pulled back along
`descriptionStageOrderIsoFin2.symm` (`descriptionStageToNat_of_fin2_symm`). This is the *inquiry* chart
of the same directed skeleton, not a second `ℕ` convention. -/
theorem inquiryAimToNat_inquiryAimOrderIsoFin2_symm (i : Fin 2) :
    inquiryAimToNat ((inquiryAimOrderIsoFin2.symm : Fin 2 → Philosophy.Aristotle.Core.InquiryAim) i) = (i : ℕ) := by
  fin_cases i <;> rfl

def inquiryAimReadingBOrderIso : Philosophy.Aristotle.Core.InquiryAim ≃o DescriptionStage :=
  inquiryAimOrderIsoFin2.trans descriptionStageOrderIsoFin2.symm

theorem inquiryAimReadingBOrderIso_hoti :
    inquiryAimReadingBOrderIso (Philosophy.Aristotle.Core.InquiryAim.hoti) =
      DescriptionStage.confusedUniversal := by
  have hf0 : (inquiryAimOrderIsoFin2) (Philosophy.Aristotle.Core.InquiryAim.hoti) = (0 : Fin 2) := by
    ext
    rfl
  have h0eq : (0 : Fin 2) = (descriptionStageOrderIsoFin2) (⊥ : DescriptionStage) :=
    (descriptionStageOrderIsoFin2_bot : (descriptionStageOrderIsoFin2 : _ → Fin 2) ⊥ = 0).symm
  rw [inquiryAimReadingBOrderIso, OrderIso.trans_apply, hf0, h0eq, OrderIso.symm_apply_apply]
  rfl

theorem inquiryAimReadingBOrderIso_dioti :
    inquiryAimReadingBOrderIso (Philosophy.Aristotle.Core.InquiryAim.dioti) =
      DescriptionStage.articulatedParticular := by
  have hf1 : (inquiryAimOrderIsoFin2) (Philosophy.Aristotle.Core.InquiryAim.dioti) = (1 : Fin 2) := by
    ext
    rfl
  have h1eq : (1 : Fin 2) = (descriptionStageOrderIsoFin2) (⊤ : DescriptionStage) :=
    (descriptionStageOrderIsoFin2_top : (descriptionStageOrderIsoFin2 : _ → Fin 2) ⊤ = 1).symm
  rw [inquiryAimReadingBOrderIso, OrderIso.trans_apply, hf1, h1eq, OrderIso.symm_apply_apply]
  rfl

/-!
### Uniqueness of the `Fin 2` charts and the Reading B bridge

On a bounded 2-point chain, an `OrderIso` to `Fin 2` (or between the two
concrete 2-chains) is **forced** by `OrderIso.map_bot` / `OrderIso.map_top`: the
endpoints are determined. The mathlib isomorphisms in this file are not an
*arbitrary* tie-in at the order-theoretic level: there is no nontrivial
alternative to sending `⊥, ⊤` to `0, 1` in `Fin 2` or, respectively, to the
Reading B endpoints on `DescriptionStage`. Only *labels* in different subsystems
differ, not the directed `0/1` skeleton (Menn, `hoti`/`dioti`, and `Fin 2` are
the three labellings tracked here; Smith-style *demonstrative* `Term` and
*middle* structure remain in `PosteriorAnalytics`—see
`reaskedWhyAim_ne_problemAim` and the Smith bundle there).
-/

theorem fin2_bot_eq_zero : (⊥ : Fin 2) = (0 : Fin 2) := by
  ext
  decide

theorem fin2_top_eq_one : (⊤ : Fin 2) = (1 : Fin 2) := by
  ext
  decide

theorem orderIso_inquiryAim_Fin2_unique
    (e : Philosophy.Aristotle.Core.InquiryAim ≃o Fin 2) :
    e = inquiryAimOrderIsoFin2 := by
  -- `e ⊥` and `e .hoti` coincide because `bot` is `hoti` in `inquiryAim2PointBot` (and dually for `⊤`).
  apply DFunLike.ext
  intro a
  cases a
  · have h1 : e .hoti = (0 : Fin 2) := (OrderIso.map_bot e).trans fin2_bot_eq_zero
    have h2 : inquiryAimOrderIsoFin2 .hoti = (0 : Fin 2) :=
      (OrderIso.map_bot (f := inquiryAimOrderIsoFin2)).trans fin2_bot_eq_zero
    exact h1.trans h2.symm
  · have h1 : e .dioti = (1 : Fin 2) := (OrderIso.map_top e).trans fin2_top_eq_one
    have h2 : inquiryAimOrderIsoFin2 .dioti = (1 : Fin 2) :=
      (OrderIso.map_top (f := inquiryAimOrderIsoFin2)).trans fin2_top_eq_one
    exact h1.trans h2.symm

theorem orderIso_DescriptionStage_Fin2_unique
    (e : DescriptionStage ≃o Fin 2) : e = descriptionStageOrderIsoFin2 := by
  apply DFunLike.ext
  intro a
  cases a
  · have h1 : e .confusedUniversal = (0 : Fin 2) := (OrderIso.map_bot e).trans fin2_bot_eq_zero
    have h2 : descriptionStageOrderIsoFin2 .confusedUniversal = (0 : Fin 2) :=
      (OrderIso.map_bot (f := descriptionStageOrderIsoFin2)).trans fin2_bot_eq_zero
    exact h1.trans h2.symm
  · have h1 : e .articulatedParticular = (1 : Fin 2) := (OrderIso.map_top e).trans fin2_top_eq_one
    have h2 : descriptionStageOrderIsoFin2 .articulatedParticular = (1 : Fin 2) :=
      (OrderIso.map_top (f := descriptionStageOrderIsoFin2)).trans fin2_top_eq_one
    exact h1.trans h2.symm

theorem orderIso_inquiryAim_DescriptionStage_unique
    (e : Philosophy.Aristotle.Core.InquiryAim ≃o DescriptionStage) :
    e = inquiryAimReadingBOrderIso := by
  apply DFunLike.ext
  intro a
  cases a
  · have h1 : e .hoti = (DescriptionStage.confusedUniversal) := by
      have h := (OrderIso.map_bot e)
      have hop : (⊥ : Philosophy.Aristotle.Core.InquiryAim) = Philosophy.Aristotle.Core.InquiryAim.hoti := rfl
      rw [hop] at h
      simpa [menn_readingBBot, Bot.bot] using h
    have h2 : inquiryAimReadingBOrderIso .hoti = (DescriptionStage.confusedUniversal) := by
      simp [inquiryAimReadingBOrderIso_hoti]
    exact h1.trans h2.symm
  · have h1 : e .dioti = (DescriptionStage.articulatedParticular) := by
      have h := (OrderIso.map_top e)
      have hop : (⊤ : Philosophy.Aristotle.Core.InquiryAim) = Philosophy.Aristotle.Core.InquiryAim.dioti := rfl
      rw [hop] at h
      simpa [menn_readingBTop, Top.top] using h
    have h2 : inquiryAimReadingBOrderIso .dioti = (DescriptionStage.articulatedParticular) := by
      simp [inquiryAimReadingBOrderIso_dioti]
    exact h1.trans h2.symm

/-!
### `OrderHom` spaces: three `Equiv`ent charts and one triangle

`orderHomEquivReadingBFin2` and the analogous *inquiry* chart (below) re-use
mathlib’s *precomposition* with an `OrderIso` to *swap the domain* of
`OrderHom` while fixing the same codomain `P`. A third `Equiv` transports
across `inquiryAimReadingBOrderIso` alone. The nontrivial point—proved as
`orderHomEquivInquiryAimFin2_eq_trans`—is that the **Fin 2** and **DescriptionStage**
transports *compose* to the same `Equiv` as the *direct* `InquiryAim`↔`Fin 2`
chart: the bridge is the **categorical** mediator between the Menn/Reading B
and `hoti`/`dioti` labellings. This is still *order homotopy* data, not a
Smith-style *middle* or `UniqueMiddleIn` in `PosteriorAnalytics`: the comparison
in-repos is only that both layers admit clean mathlib *transport* along the
same 2-point skeleton, not that “middle” in demonstration *is* an epistemic
stage-increase in Physics I.1.
-/

def orderHomEquivInquiryAimFin2 (P : Type*) [PartialOrder P] :
    (Philosophy.Aristotle.Core.InquiryAim →o P) ≃ (Fin 2 →o P) where
  toFun f := f.comp (inquiryAimOrderIsoFin2.symm : Fin 2 →o Philosophy.Aristotle.Core.InquiryAim)
  invFun g := g.comp (inquiryAimOrderIsoFin2 : Philosophy.Aristotle.Core.InquiryAim →o Fin 2)
  left_inv f := by
    ext a
    exact congrArg f (OrderIso.symm_apply_apply inquiryAimOrderIsoFin2 a)
  right_inv g := by
    ext a
    exact congrArg g (OrderIso.apply_symm_apply inquiryAimOrderIsoFin2 a)

theorem orderHomEquivInquiryAimFin2_toFun_apply
    {P : Type*} [PartialOrder P] (f : Philosophy.Aristotle.Core.InquiryAim →o P) (i : Fin 2) :
    (orderHomEquivInquiryAimFin2 P) f i = f (inquiryAimOrderIsoFin2.symm i) := rfl

def orderHomEquivInquiryAimDescriptionStage (P : Type*) [PartialOrder P] :
    (Philosophy.Aristotle.Core.InquiryAim →o P) ≃ (DescriptionStage →o P) where
  toFun g := g.comp (inquiryAimReadingBOrderIso.symm : DescriptionStage →o Philosophy.Aristotle.Core.InquiryAim)
  invFun f := f.comp (inquiryAimReadingBOrderIso : Philosophy.Aristotle.Core.InquiryAim →o DescriptionStage)
  left_inv g := by
    ext a
    exact congrArg g (OrderIso.symm_apply_apply inquiryAimReadingBOrderIso a)
  right_inv f := by
    ext a
    exact congrArg f (OrderIso.apply_symm_apply inquiryAimReadingBOrderIso a)

theorem orderHomEquivInquiryAimDescriptionStage_toFun_apply
    {P : Type*} [PartialOrder P] (g : Philosophy.Aristotle.Core.InquiryAim →o P) (s : DescriptionStage) :
    (orderHomEquivInquiryAimDescriptionStage P) g s = g (inquiryAimReadingBOrderIso.symm s) := rfl

theorem inquiryAimOrderIsoFin2_eq_comp_orderHom :
    (inquiryAimOrderIsoFin2 : Philosophy.Aristotle.Core.InquiryAim →o Fin 2) =
      (descriptionStageOrderIsoFin2 : _ →o _).comp
        (inquiryAimReadingBOrderIso : Philosophy.Aristotle.Core.InquiryAim →o DescriptionStage) := by
  ext a
  /-
  `inquiryAimReadingBOrderIso` is `inquiryAimOrderIsoFin2.trans` the inverse of
  `descriptionStageOrderIsoFin2`; pre-composing the latter rejoins a `Fin` point to the
  same `InquiryAim` coordinate. This is `OrderIso.apply_symm_apply` on
  `descriptionStageOrderIsoFin2` (enforced by the simp set below).
  -/
  simp [OrderHom.comp, inquiryAimReadingBOrderIso]

theorem inquiryAimOrderIsoFin2_symm_path (i : Fin 2) :
    (inquiryAimOrderIsoFin2.symm : Fin 2 → Philosophy.Aristotle.Core.InquiryAim) i =
      (inquiryAimReadingBOrderIso.symm (descriptionStageOrderIsoFin2.symm i) : _) := by
  /-
  `inquiryAimReadingBOrderIso = inquiryAimOrderIsoFin2.trans (descriptionStageOrderIsoFin2.symm)`.
  For order isomorphisms, `(e₁.trans e₂).symm c = e₁.symm (e₂.symm c)` (`OrderIso.symm_trans_apply`):
  the outer `c` is a `DescriptionStage` point, so `e₂.symm` brings it to `Fin 2` and cancels
  the leading `e₂` from the bridge.
  -/
  rw [inquiryAimReadingBOrderIso, OrderIso.symm_trans_apply]
  -- `e₂ = descriptionStageOrderIsoFin2.symm` so `e₂.symm` is `descriptionStageOrderIsoFin2` on
  -- `c = e₂ (descriptionStageOrderIsoFin2.symm i)`; cancel to `i` in the inner argument to `e₁.symm`.
  congr 1
  exact (OrderIso.apply_symm_apply (e := descriptionStageOrderIsoFin2) (x := i)).symm

theorem orderHomEquivInquiryAimFin2_eq_trans (P : Type*) [PartialOrder P] :
    orderHomEquivInquiryAimFin2 P =
      (orderHomEquivInquiryAimDescriptionStage P).trans (orderHomEquivReadingBFin2 P) := by
  refine Equiv.ext ?_
  intro f
  ext i
  /-
  The forward maps agree because the two routes send each `i : Fin 2` to the *same* argument
  in `InquiryAim` (`inquiryAimOrderIsoFin2_symm_path`); apply `f` to get the same
  `P` value. See `inquiryAimOrderIsoFin2_eq_comp_orderHom` for the *forward*
  `InquiryAim`→`Fin 2` leg.
  -/
  -- See `inquiryAimOrderIsoFin2_symm_path` for the single `InquiryAim` coordinate behind both charts.
  change f (inquiryAimOrderIsoFin2.symm i) =
      f (inquiryAimReadingBOrderIso.symm (descriptionStageOrderIsoFin2.symm i))
  rw [inquiryAimOrderIsoFin2_symm_path i]

/-!
### Functoriality: post-composition and two-point extensionality (still no *middle* conflation)

Precomposition with a fixed `OrderIso` is the usual **mathlib** reindexing of
`OrderHom`. Post-composition with a fixed `g : P →o Q` is a second, independent
operation (change of *codomain* order, not a new principle-description or a
relabel of `WhyQuestion` / `Term`). These lemmas record that the three `Equiv`s
on `OrderHom` spaces—`Fin 2` chart, Menn/Reading B chart, and the
`InquiryAim`–`DescriptionStage` bridge—**commute** with `g` on the left: the
triangle in `orderHomEquivInquiryAimFin2_eq_trans` is natural in the usual
1-categorical sense for `PartialOrder` and `OrderHom`.

This is *not* a Smith-style claim about *demonstrative* middles or
`UniqueMiddleIn` in `PosteriorAnalytics`—only functoriality of the order
reindexing story Menn and Smith can both *use* as background order theory
without identifying their **objects** of study.
-/

theorem orderHomEquivInquiryAimFin2_comp_orderHom
    {P Q : Type*} [PartialOrder P] [PartialOrder Q] (g : P →o Q)
    (f : Philosophy.Aristotle.Core.InquiryAim →o P) :
    (orderHomEquivInquiryAimFin2 Q) (g.comp f) = g.comp ((orderHomEquivInquiryAimFin2 P) f) := by
  ext i
  simp [orderHomEquivInquiryAimFin2_toFun_apply, OrderHom.comp, Function.comp]

theorem orderHomEquivReadingBFin2_comp_orderHom
    {P Q : Type*} [PartialOrder P] [PartialOrder Q] (g : P →o Q) (f : DescriptionStage →o P) :
    (orderHomEquivReadingBFin2 Q) (g.comp f) = g.comp ((orderHomEquivReadingBFin2 P) f) := by
  ext i
  simp [orderHomEquivReadingBFin2_toFun_apply, OrderHom.comp, Function.comp]

theorem orderHomEquivInquiryAimDescriptionStage_comp_orderHom
    {P Q : Type*} [PartialOrder P] [PartialOrder Q] (g : P →o Q)
    (f : Philosophy.Aristotle.Core.InquiryAim →o P) :
    (orderHomEquivInquiryAimDescriptionStage Q) (g.comp f) =
      g.comp ((orderHomEquivInquiryAimDescriptionStage P) f) := by
  ext s
  simp [orderHomEquivInquiryAimDescriptionStage_toFun_apply, OrderHom.comp, Function.comp]

/-- Naturality of the *composed* `DescriptionStage`↔`Fin 2` detour, by `orderHomEquivInquiryAimFin2_eq_trans`
and `orderHomEquivInquiryAimFin2_comp_orderHom`. The same `g` post-composition law holds whether one uses
the one-step `orderHomEquivInquiryAimFin2` or the Menn/Reading B two-step transport. -/
theorem orderHomEquivInquiryAimDescriptionStage_trans_ReadingBFin2_comp_orderHom
    {P Q : Type*} [PartialOrder P] [PartialOrder Q] (g : P →o Q) (f : Philosophy.Aristotle.Core.InquiryAim →o P) :
    ((orderHomEquivInquiryAimDescriptionStage Q).trans (orderHomEquivReadingBFin2 Q)) (g.comp f) =
      g.comp (((orderHomEquivInquiryAimDescriptionStage P).trans (orderHomEquivReadingBFin2 P)) f) := by
  simpa [orderHomEquivInquiryAimFin2_eq_trans] using orderHomEquivInquiryAimFin2_comp_orderHom g f

theorem inquiryAimOrderHom_ext {P : Type*} [PartialOrder P] {f g : Philosophy.Aristotle.Core.InquiryAim →o P}
    (h0 : f (Philosophy.Aristotle.Core.InquiryAim.hoti) = g (Philosophy.Aristotle.Core.InquiryAim.hoti))
    (h1 : f (Philosophy.Aristotle.Core.InquiryAim.dioti) = g (Philosophy.Aristotle.Core.InquiryAim.dioti)) :
    f = g := by
  refine OrderHom.ext f g (funext fun a : Philosophy.Aristotle.Core.InquiryAim => ?_)
  cases a
  · exact h0
  · exact h1

/-!
### Rank in `ℕ` commutes with the shape `OrderIso` (`InquiryAim` ↔ `DescriptionStage`)

The numeric encodings `inquiryAimToNat` and `descriptionStageToNat` are the *same
function* once we transport along `inquiryAimReadingBOrderIso`. This is the
cleanest formal sense in which the two 2-chains are **one** *abstract* `0/1`
skeleton (Menn’s Reading B labels and Core’s `hoti`/`dioti` rôle labels) and
**two** *concrete* inductive presentations: there is no second “secret”
numerical convention—only the two type-specific names for the endpoints.
-/

theorem inquiryAimToNat_eq_descriptionStageToNat_of_readingB
    (a : Philosophy.Aristotle.Core.InquiryAim) :
    inquiryAimToNat a = descriptionStageToNat (inquiryAimReadingBOrderIso a) := by
  cases a
  · simp [inquiryAimToNat, descriptionStageToNat, inquiryAimReadingBOrderIso_hoti]
  · simp [inquiryAimToNat, descriptionStageToNat, inquiryAimReadingBOrderIso_dioti]

theorem inquiryAimToNat_eq_descriptionStageToNat_comp :
    inquiryAimToNat = descriptionStageToNat ∘ inquiryAimReadingBOrderIso := by
  funext a
  exact inquiryAimToNat_eq_descriptionStageToNat_of_readingB a

/-!
The same `0/1` story at the `OrderHom` level: the canonical `ℕ` rank on
`InquiryAim` is *definitionally* the Reading B rank on `DescriptionStage`, pulled
back along the shape `OrderIso`—a single *mathlib* `OrderHom` path (composition in
`OrderHom`, not a second `Fin`-endpoint construction on `InquiryAim`).
-/

/-- Canonical `0/1` rank of an inquiry rôle, as a bundled `OrderHom` into the
standard order on `ℕ`. Definitionally, `descriptionStageRankHom` after
`inquiryAimReadingBOrderIso` (Menn’s Reading B skeleton) rather than a second
endpoint construction. -/
def inquiryAimRankHom : Philosophy.Aristotle.Core.InquiryAim →o ℕ :=
  descriptionStageRankHom.comp (OrderHomClass.toOrderHom inquiryAimReadingBOrderIso)

theorem inquiryAimRankHom_eq_comp :
    inquiryAimRankHom = descriptionStageRankHom.comp (OrderHomClass.toOrderHom inquiryAimReadingBOrderIso) :=
  rfl

/-!
`Fin 2` ↔ `DescriptionStage` ↔ `ℕ` is a third *presentation* of the same directed `0/1` **rank** (not a
new numeric convention): the Mathlib `orderHomEquivReadingBFin2` rewrites `DescriptionStage` maps into
`Fin 2` maps, and the canonical Menn/Reading B rank pulls back to `Fin` values `0,1` on
`0,1 : Fin 2`. A monotone `Fin 2 →o ℕ` is determined by the two endpoints, just as for
`orderHomOfReadingB` (but here the *domain* is the abstract `Fin 2` 2-point order, not the
Reading B *names*).
-/

/-- Reading B’s `0/1` `ℕ` rank, transported to `Fin 2` along `DescriptionStageOrderIsoFin2` (Menn/Reading
B in `Fin`’s *coordinates*). See `inquiryAimToNat` / `inquiryAimOrderIsoFin2` for the parallel on
`InquiryAim` instead of this third chart. -/
def fin2ReadingBRankHom : Fin 2 →o ℕ :=
  (orderHomEquivReadingBFin2 ℕ) descriptionStageRankHom

theorem descriptionStageToNat_of_fin2_symm (i : Fin 2) :
    descriptionStageToNat ((descriptionStageOrderIsoFin2.symm : Fin 2 → DescriptionStage) i) = (i : ℕ) := by
  fin_cases i <;> rfl

theorem fin2ReadingBRankHom_apply (i : Fin 2) : (fin2ReadingBRankHom i : ℕ) = (i : ℕ) := by
  rw [fin2ReadingBRankHom, orderHomEquivReadingBFin2_toFun_apply, descriptionStageRankHom_eq_descriptionStageToNat]
  exact descriptionStageToNat_of_fin2_symm i

theorem fin2OrderHom_eq_of_apply_zero_one
    {P : Type*} [PartialOrder P] {f g : Fin 2 →o P} (h0 : f 0 = g 0) (h1 : f 1 = g 1) : f = g := by
  refine OrderHom.ext f g (funext fun i : Fin 2 => ?_)
  fin_cases i
  · exact h0
  · exact h1

theorem eq_fin2ReadingBRankHom_of
    (f : Fin 2 →o ℕ) (h0 : f 0 = 0) (h1 : f 1 = 1) : f = fin2ReadingBRankHom := by
  apply fin2OrderHom_eq_of_apply_zero_one
  · exact h0.trans (fin2ReadingBRankHom_apply 0).symm
  · exact h1.trans (fin2ReadingBRankHom_apply 1).symm

theorem inquiryAimRankHom_apply (a : Philosophy.Aristotle.Core.InquiryAim) :
    (inquiryAimRankHom : _ → ℕ) a = inquiryAimToNat a := by
  have hcomp : (inquiryAimRankHom : _ → ℕ) a =
      (descriptionStageRankHom : DescriptionStage → ℕ) (inquiryAimReadingBOrderIso a) :=
    rfl
  rw [hcomp, descriptionStageRankHom_eq_descriptionStageToNat]
  exact (inquiryAimToNat_eq_descriptionStageToNat_of_readingB a).symm

/-- The `orderHomEquivInquiryAimFin2` reindexing of `inquiryAimRankHom` (the pulled-back Menn/Reading
B rank on `InquiryAim`, see `inquiryAimRankHom_eq_comp`) is the same `Fin 2 →o ℕ` as
`fin2ReadingBRankHom`: the direct **Core** `InquiryAim` chart and the **DescriptionStage** chart
through `orderHomEquivReadingBFin2` give one map on `Fin 2`—a concrete union of the “three
labellings” with no separate `Fin` endpoint construction. -/
theorem orderHomEquivInquiryAimFin2_inquiryAimRankHom_eq :
    (orderHomEquivInquiryAimFin2 ℕ) inquiryAimRankHom = fin2ReadingBRankHom := by
  ext i
  rw [orderHomEquivInquiryAimFin2_toFun_apply, inquiryAimRankHom_apply, inquiryAimToNat_inquiryAimOrderIsoFin2_symm,
    fin2ReadingBRankHom_apply]

/-- Same map as the `orderHomEquivInquiryAimFin2` reindexing, stated as
`inquiryAimRankHom` pre-composed with the `Fin` chart—useful in longer `comp` calculation blocks. -/
theorem inquiryAimRankHom_comp_inquiryAimOrderIsoFin2symm_eq :
    inquiryAimRankHom.comp
        (OrderHomClass.toOrderHom (inquiryAimOrderIsoFin2.symm : Fin 2 ≃o Philosophy.Aristotle.Core.InquiryAim)) =
      fin2ReadingBRankHom :=
  orderHomEquivInquiryAimFin2_inquiryAimRankHom_eq

/-- Pre-indexing the Core rank along `inquiryAimReadingBOrderIso` on `OrderHom` *spaces* sends it to
Menn/Reading B’s `descriptionStageRankHom`—a **non-definitional** re-expressions of
`inquiryAimRankHom = descriptionStageRankHom.comp …`, recorded at the *equiv* of charts rather
than as pointwise `ℕ` (cf. `inquiryAimToNat_eq_descriptionStageToNat_of_readingB`). -/
theorem orderHomEquivInquiryAimDescriptionStage_inquiryAimRankHom :
    (orderHomEquivInquiryAimDescriptionStage ℕ) inquiryAimRankHom = descriptionStageRankHom := by
  ext s
  -- Pointwise: `inquiryAimToNat` after a round-trip in `inquiryAimReadingBOrderIso` is
  -- `descriptionStageToNat` (`inquiryAimToNat_eq_descriptionStageToNat_of_readingB` at `bridge.symm s`).
  rw [orderHomEquivInquiryAimDescriptionStage_toFun_apply, inquiryAimRankHom_apply, inquiryAimToNat_eq_descriptionStageToNat_of_readingB,
    OrderIso.apply_symm_apply, descriptionStageRankHom_eq_descriptionStageToNat]

/-- The inverse of that chart takes Reading B’s canonical `ℕ` rank to Core’s `inquiryAimRankHom`.
This is definitionally the same bundle as `inquiryAimRankHom_eq_comp`, but stated as
`(Equiv on OrderHom) ⁻¹ ·`. -/
theorem orderHomEquivInquiryAimDescriptionStage_symm_descriptionStageRankHom :
    (orderHomEquivInquiryAimDescriptionStage ℕ).symm descriptionStageRankHom = inquiryAimRankHom := rfl

/-- The two-step `InquiryAim`→`DescriptionStage`→`Fin` rescreening of `inquiryAimRankHom` agrees
with the one-step `InquiryAim`→`Fin` transport (`orderHomEquivInquiryAimFin2_eq_trans` applied to
a fixed hom). This is a non-promise “diagram commutes in `OrderHom` up to the bridge”. -/
theorem orderHomEquiv_ReadingB_trans_inquiryAimRankHom_eq :
    ((orderHomEquivInquiryAimDescriptionStage ℕ).trans (orderHomEquivReadingBFin2 ℕ)) inquiryAimRankHom =
      fin2ReadingBRankHom := by
  have h := congrArg
    (fun (e : (Philosophy.Aristotle.Core.InquiryAim →o ℕ) ≃ (Fin 2 →o ℕ)) => e inquiryAimRankHom)
    (orderHomEquivInquiryAimFin2_eq_trans (ℕ))
  /- `h` rewrites the two-step transport to the one-step `orderHomEquivInquiryAimFin2` on this hom. -/
  exact h.symm.trans orderHomEquivInquiryAimFin2_inquiryAimRankHom_eq

/-- `InquiryAim` only tags `0` and `1` in `ℕ`: no third epistemic “rung” in this 2-point skeleton. -/
theorem inquiryAimToNat_exhaustive (n : ℕ) :
    (∃ a : Philosophy.Aristotle.Core.InquiryAim, inquiryAimToNat a = n) ↔ n = 0 ∨ n = 1 := by
  constructor
  · rintro ⟨a, ha⟩
    cases a
    · left; exact ha.symm
    · right; exact ha.symm
  · rintro (h | h)
    · use Philosophy.Aristotle.Core.InquiryAim.hoti; simp [h, inquiryAimToNat]
    · use Philosophy.Aristotle.Core.InquiryAim.dioti; simp [h, inquiryAimToNat]

/-- The directed 2-point chain of inquiry rôles is **strict** between the endpoints, not
coarser-than (`=`). (Still only order theory; `Problem` / `WhyQuestion` remain separate layers
above this skeleton.) -/
theorem hoti_lt_dioti : (Philosophy.Aristotle.Core.InquiryAim.hoti : _) < (Philosophy.Aristotle.Core.InquiryAim.dioti) := by
  refine lt_of_le_of_ne (α := _) hoti_le_dioti ?_
  intro h
  exact Nat.zero_ne_one (congrArg inquiryAimToNat h)

theorem inquiryAimRankHom_coe_eq_inquiryAimToNat :
    (inquiryAimRankHom : Philosophy.Aristotle.Core.InquiryAim → ℕ) = inquiryAimToNat := by
  funext a
  exact inquiryAimRankHom_apply a

/-- A monotone `InquiryAim →o ℕ` is *forced* by its values on the two rôles: there is at most one
`0,1` placement compatible with the inherited two-point `PartialOrder` and the standard order on
`ℕ`. (Compare `orderHomOfReadingB_eq` for `DescriptionStage` alone.) -/
theorem eq_inquiryAimRankHom_of_map_bot_map_top
    (f : Philosophy.Aristotle.Core.InquiryAim →o ℕ)
    (hbot : f (Philosophy.Aristotle.Core.InquiryAim.hoti) = 0) (htop : f (Philosophy.Aristotle.Core.InquiryAim.dioti) = 1) :
    f = inquiryAimRankHom := by
  refine OrderHom.ext f inquiryAimRankHom (funext fun a : Philosophy.Aristotle.Core.InquiryAim => ?_)
  cases a <;> simp [hbot, htop, inquiryAimRankHom_apply, inquiryAimToNat]

theorem inquiryAimOrderHom_coe_eq_inquiryAimToNat_of_map_bot_map_top
    (f : Philosophy.Aristotle.Core.InquiryAim →o ℕ)
    (hbot : f (Philosophy.Aristotle.Core.InquiryAim.hoti) = 0) (htop : f (Philosophy.Aristotle.Core.InquiryAim.dioti) = 1) (a : Philosophy.Aristotle.Core.InquiryAim) :
    f a = inquiryAimToNat a := by
  rw [eq_inquiryAimRankHom_of_map_bot_map_top f hbot htop, inquiryAimRankHom_apply]

/-!
### Dialectic vs Menn: one common `0/1` *rank*, two different *rôles* (Smith in `PosteriorAnalytics`, Menn in Reading B)

`inquiryAimToNat` is a pure order-theoretic `0/1` tag of `InquiryAim` on the **Core** rôle line. The
dialectical `Problem` and scientific `WhyQuestion` each fix that rôle in their own layer (see
`Problem.hoti_only` and `WhyQuestion.dioti_only` in the Analytics packages). The two lemmas below are
*only* the induced numerics: they do **not** identify Menn’s description stages with either dialectic
or demonstration, and they are not a reduction of `Term` or *middle* to the Reading B chain.
-/

theorem inquiryAimToNat_Problem_aim (p : Problem) : inquiryAimToNat p.aim = 0 := by
  simp [Problem.hoti_only, inquiryAimToNat]

theorem inquiryAimToNat_WhyQuestion_aim (q : WhyQuestion) : inquiryAimToNat q.aim = 1 := by
  simp [WhyQuestion.dioti_only, inquiryAimToNat]

/-- The `0/1` rank at the **aim** of a `Problem` is always **not** the rank of a
`WhyQuestion.aim` (dialectical *whether* vs Post An. *why* in distinct inquiry rôles, not a
contradiction in one rôle). -/
theorem inquiryAimToNat_problemAim_ne_whyQuestionAim
    (p : Problem) (q : WhyQuestion) : inquiryAimToNat p.aim ≠ inquiryAimToNat q.aim := by
  rw [inquiryAimToNat_Problem_aim, inquiryAimToNat_WhyQuestion_aim]
  exact Nat.zero_ne_one

/--
A reminder-lemma in the Menn idiom: the dialectical *whether* of a
`Problem` and the *why*-question form on the *same* categorical
content are never the same *inquiry rôle* (`Aristotle.md`, `InquiryBoundary`).
This is a different non-collapse from Reading B: do not read `hoti` as
"confused description stage".

(Equivalently: the optional `problemWhyQuestion?` packages the re-asked
`WhyQuestion` when a statement is present, and that role still differs from
`Problem.aim`; see `problemWhyQuestion_differentAim_of_statement` in
`InquiryBoundary`.)
-/
theorem reaskedWhyAim_ne_problemAim
    (problem : Problem) {c : Categorical} (hstmt : problem.statement? = some c) :
    (WhyQuestion.ofConclusion c).aim ≠ problem.aim := by
  exact problemWhyQuestion_differentAim_of_statement hstmt

end Aristotle.MennAlignment
