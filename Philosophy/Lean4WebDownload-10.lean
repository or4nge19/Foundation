import Mathlib

universe u v

namespace Philosophy.Kant.Laywine

/-!
# Formalizing Laywine's Reading of Kant in Lean 4 / Mathlib

## Sources

* Alison Laywine, *Kant's Early Metaphysics and the Origins of the Critical Philosophy*,
  North American Kant Society Studies in Philosophy 3, Ridgeview Publishing, 1993.

* Alison Laywine, *Kant's Transcendental Deduction: A Cosmology of Experience*,
  Oxford University Press, 2020.

## Overview

Laywine's interpretive arc traces how Kant's *pre-critical* general cosmology became the
structural template for the *Transcendental Deduction* in the first *Critique*. The key
ideas formalized here are:

1. **Negative Magnitudes (1763)**: The distinction between logical contradiction
   (Nihil Negativum) and real opposition / equilibrium (Nihil Privativum).
2. **Cosmology and Commercium**: Kant's rejection of Leibniz's pre-established harmony
   in favour of a "world-whole" unified by reciprocal physical influx.
3. **Ekthesis and Cartography**: Laywine's reading of the *exposition of appearances*
   (R4674 in the Duisburg Nachlaß) as a practice of map-making, projecting local
   "sightings" of appearances onto the a priori coordinate grid of pure intuition.
4. **The Categories as a Structure Groupoid**: The pure concepts of the understanding
   as the invariant rules constraining how local charts are glued.
5. **The Transcendental Deduction as a Cosmology of Experience**: Laywine's thesis
   that the epistemological deduction of the categories structurally recapitulates
   God's legislation of cosmological laws in the early metaphysics.
-/


/-!
# Part I: Negative Magnitudes (1763)

Laywine (1993, Ch. 3) shows that Kant's break from rationalism began with the
distinction between *logical* grounds and *real* grounds, introduced in the
*Attempt to Introduce Negative Magnitudes into Philosophy* (1763/1764).

Logical opposition (P ∧ ¬P) is a contradiction yielding absolute nothingness (False).
Real opposition is when two genuinely existing forces cancel to an equilibrium (zero),
while both forces remain perfectly real entities — a "Nihil Privativum."
-/

/-- **Logical opposition (Nihil Negativum)**: A proposition and its negation
jointly entail `False`. This is type-level annihilation. -/
theorem logical_opposition (P : Prop) (h1 : P) (h2 : ¬P) : False :=
  h2 h1

/-- **Real opposition (Nihil Privativum)**: Two opposing intensive magnitudes
(forces) in a shared space cancel to an equilibrium (zero), while both forces
remain perfectly real entities. This maps to the additive inverse law in an
`AddCommGroup`. -/
theorem real_opposition {Magnitude : Type u} [AddCommGroup Magnitude]
    (force : Magnitude) : force + (-force) = 0 :=
  add_neg_cancel force


/-!
# Part II: Cosmology and Commercium

Laywine (1993, Ch. 1–2; 2020, Ch. 1 & Conclusion) emphasizes that Kant's
"World-Whole" requires *Commercium*: universal, reciprocal physical influx
among all substances, rejecting Leibniz's pre-established harmony.

A world, for the early Kant, is not merely the sum-total of all substances;
it is a whole unified by God's universal laws of community that externally
relate every substance to every other. Laywine (2020) then shows how Kant
repurposed this metaphysical structure for the Deduction: experience is
"the whole of all possible appearances unified by the universal laws human
understanding gives to nature."
-/

variable (Substance : Type u) [CategoryTheory.Category.{v} Substance]
open CategoryTheory

/-- **Leibniz's Pre-Established Harmony**: Monads are "windowless." They can
undergo internal change (endomorphisms `A ⟶ A`), but no causal morphisms
exist between distinct monads. Categorically: every morphism is an
endomorphism. -/
class LeibnizianHarmony : Prop where
  windowless : ∀ (A B : Substance), (A ⟶ B) → (A = B)

/-- **Kant's Commercium** (Laywine's reconstruction): A "World" is defined
by *reciprocal interaction*. If a causal morphism exists from A to B, one
must also exist from B to A. This captures the mutual determination
required by Kant's world-whole. -/
class KantianCommercium : Prop where
  reciprocal_influx : ∀ (A B : Substance), Nonempty (A ⟶ B) ↔ Nonempty (B ⟶ A)

/-- A stronger condition: The category of substances is *connected*, ensuring
no substance is isolated from the Commercium. This matches Laywine's
insistence that the world-whole is a single unified totality. -/
class KantianCosmology : Prop where
  world_whole : IsConnected Substance


/-!
# Part III: Ekthesis and the Cartography of Sensibility

Laywine (2020, Ch. 4 "A Cosmology of Experience — §26 of the B-Deduction")
develops the idea that perception is *map-making*. The key term is *ekthesis*
(ἔκθεσις), borrowed from the presentation convention of geometrical proofs
in Euclid and Apollonius: after the general enunciation, the ekthesis provides
a labelled illustration of a "representative case" (Laywine 2020, p. 31,
discussing R4674 of the Duisburg Nachlaß).

The mind projects local "sightings" of raw appearances onto the a priori
coordinate grid of space and time (Pure Intuition). An un-unified, merely
empirical stream of such sightings is an atlas of local charts — a
`ChartedSpace` — without any guarantee of global consistency.
-/

/- Pure Space and Time: the a priori geometric coordinate grid (Model Space). -/
variable (PureIntuition : Type u) [TopologicalSpace PureIntuition]

/- The unconceptualized, raw manifold of empirical appearances. -/
variable (SensibleManifold : Type u) [TopologicalSpace SensibleManifold]

/-- **Ekthesis (A Local Perceptual Sighting)**: An active construction of a
local perceptual map. A `PartialHomeomorph` captures Laywine's "local
sighting": projecting a restricted patch of raw sense data onto Pure
Intuition. (In current Mathlib, `OpenPartialHomeomorph` is used for charts.) -/
abbrev PerceptualSighting := OpenPartialHomeomorph SensibleManifold PureIntuition

/-- **The Empirical Atlas**: An un-unified, Humean stream of perceptions is
merely a `ChartedSpace` — an empirical atlas of local maps without any
guarantee of global consistency. -/
abbrev EmpiricalAtlas := ChartedSpace PureIntuition SensibleManifold


/-!
# Part IV: The Categories as a Structure Groupoid

The Pure Concepts of the Understanding (the Categories) are the invariant
*a priori* rules of projection that constrain how subjective local sightings
can be glued together. They dictate the valid transition functions (e.g.,
Causality, Community) allowed when moving from one subjective chart to another.

In Mathlib, a `StructureGroupoid` on a model space `H` is a set of partial
homeomorphisms of `H` closed under composition, inversion, restriction, and
containing the identity — precisely the kind of invariant constraint Laywine
describes.
-/

variable {PureIntuition}
/- The Categories constitute a Structure Groupoid on Pure Intuition. -/
variable (Categories : StructureGroupoid PureIntuition)


/-!
# Part V: The Transcendental Deduction (A Cosmology of Experience)

Laywine's masterstroke (2020): The epistemological deduction of the categories
is structurally identical to God legislating physical laws in the early
cosmology. Where God's intellect once prescribed universal laws to the world
of substances, the human understanding now prescribes universal laws to the
world of appearances (nature). The "I think" forces local empirical maps
to conform to universal laws.

Formally: by enforcing the Categories (as a Structure Groupoid), local
representations are forced to glue together consistently. In Mathlib,
`HasGroupoid M G` asserts that the maximal atlas of M is compatible with
the structure groupoid G — every chart transition belongs to G.
-/

/-- **The Transcendental Unity of Apperception** (Cosmology of Experience).

By enforcing the rules of projection (the Categories), local representations
continuously and uniquely glue together into a single objective nature.

`HasGroupoid SensibleManifold Categories` asserts that the maximal atlas of
the sensible manifold is strictly compatible with the transition rules of the
`Categories` Structure Groupoid. This is Laywine's "cosmology of experience":
the understanding legislates universal laws to nature just as God once
legislated cosmological laws to the world of substances. -/
class CosmologyOfExperience (SensibleManifold : Type u) [TopologicalSpace SensibleManifold]
    [ChartedSpace PureIntuition SensibleManifold] : Prop where
  /-- The "I Think" forces local empirical maps to conform to universal laws. -/
  unity_of_apperception : HasGroupoid SensibleManifold Categories


/-!
# Appendix: The Sheaf-Theoretic Perspective

An alternative formalization of the Unity of Apperception uses the sheaf
condition on presheaves. A presheaf over the topological space of appearances
assigns representations (concepts) to local regions of experience. The sheaf
condition states that local representations must uniquely glue to global
sections — precisely the content of Kant's dictum that "the 'I think' must
be able to accompany all my representations" (B131–132).

This perspective complements the StructureGroupoid formalization above;
both express the same Kantian requirement of global consistency from local
data. Laywine's cartographic metaphor makes the manifold / atlas perspective
primary, with the sheaf condition as a consequence of proper chart
compatibility.
-/

section SheafPerspective

variable {X : TopCat.{u}} (Experience : TopCat.Presheaf (Type v) X)

/-- The **Unity of Apperception** expressed sheaf-theoretically:
local subjective representations glue into a globally consistent objective
Nature. The "I think" (Objective Nature) is the global section over `⊤`. -/
class UnityOfApperceptionSheaf where
  /-- Local charts must uniquely glue together (the Sheaf Condition). -/
  is_sheaf : Experience.IsSheaf
  /-- The "I think" — objective nature as a global section. -/
  i_think : Experience.obj (Opposite.op ⊤)

end SheafPerspective

end Philosophy.Kant.Laywine