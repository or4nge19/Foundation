import Mathlib

universe u v w

namespace Philosophy.Kant.Laywine

open CategoryTheory Opposite TopologicalSpace

/-!
# A Mathlib-Style Formalization of Laywine's Reading of Kant

## Sources

* Alison Laywine, *Kant's Early Metaphysics and the Origins of the Critical Philosophy*,
  North American Kant Society Studies in Philosophy 3, Ridgeview Publishing, 1993.

* Alison Laywine, "Kant's Laboratory of Ideas in the 1770s," in *A Companion to Kant*,
  ed. Graham Bird, Blackwell, 2006, pp. 63–77.

* Alison Laywine, *Kant's Transcendental Deduction: A Cosmology of Experience*,
  Oxford University Press, 2020.

## Architecture

The formalization follows Laywine's developmental-historical arc:

  I.  Negative Magnitudes (1763): Real vs logical opposition.
  II. Pre-critical Cosmology: The world-whole and Commercium.
  III. The Intellectus Archetypus and Finite Understanding (Herz letter, 1772).
  IV. The Duisburg Nachlaß (≈1775): Functions of apperception and
      the exposition of appearances.
  V.  Ekthesis and Cartography of Sensibility (2020 reading of §26 B-Deduction).
  VI. The Transcendental Deduction as a Cosmology of Experience.
-/


-- ============================================================================
-- PART I: NEGATIVE MAGNITUDES (1763)
-- ============================================================================

/-!
# Part I: Negative Magnitudes (1763)

Laywine (1993, Ch. 3) shows that Kant's break from Wolffian rationalism began
with the distinction between *logical* and *real* grounds, introduced in the
*Attempt to Introduce Negative Magnitudes into Philosophy* (Ak 2:165–204).

Logical opposition (P ∧ ¬P) yields absolute nothingness — a *Nihil Negativum*.
Real opposition yields an equilibrium (zero) in which both opposing forces
remain perfectly real entities — a *Nihil Privativum*.
-/

section NegativeMagnitudes

/-- **Nihil Negativum**: Logical opposition annihilates into `False`.
A proposition and its negation cannot coexist. -/
theorem nihil_negativum (P : Prop) (h1 : P) (h2 : ¬P) : False :=
  h2 h1

/-- **Nihil Privativum**: Real opposition (equilibrium).
Two opposing intensive magnitudes cancel to zero while both remain real.
This is the additive inverse law in any `AddCommGroup`. -/
theorem nihil_privativum {M : Type u} [AddCommGroup M]
    (force : M) : force + (-force) = 0 :=
  add_neg_cancel force

/-- The distinction matters: the *result* of real opposition is mathematically
zero (an element of the group), not logical nothingness (`False`). Zero is
a perfectly legitimate magnitude — the point of Kant's essay. -/
example {M : Type u} [AddCommGroup M] : (0 : M) = (0 : M) := rfl

end NegativeMagnitudes


-- ============================================================================
-- PART II: PRE-CRITICAL COSMOLOGY AND COMMERCIUM
-- ============================================================================

/-!
# Part II: Pre-Critical Cosmology and Commercium

Laywine (1993, Ch. 1–2; 2006, §2) emphasizes that Kant's pre-critical cosmology
requires a "world-whole" unified by *universal laws of community* (Commercium).

A "world" for the early Kant is not merely the sum-total of created substances;
it is a whole whose parts are universally and externally related to one another
through reciprocal interaction. God's intellect takes as its object "the principles
of the form of a world" (Inaugural Dissertation §13, Ak 2:398) — the universal
laws that cause substances to arrange themselves into a world "on their own
steam" (Laywine 2006, p. 66).

This conception rejects Leibniz's pre-established harmony, where monads are
"windowless" and only God coordinates their internal states.
-/

section Cosmology

variable (Substance : Type u) [Category.{v} Substance]

/-- **Leibniz's Pre-Established Harmony**: Monads are "windowless."
Internal change (endomorphisms) is possible, but no *real causal morphism*
exists between distinct substances. Every morphism collapses to an
endomorphism. -/
class LeibnizianHarmony : Prop where
  windowless : ∀ (A B : Substance), (A ⟶ B) → (A = B)

/-- **Kant's Commercium** (1755–1770): The world-whole requires *reciprocal
physical influx*. If a causal relation exists from A to B, then one must
also exist from B to A. This captures the mutual determination Kant
demands of a genuine world (Nova Dilucidatio, Proposition XIII). -/
class KantianCommercium : Prop where
  reciprocal_influx : ∀ (A B : Substance), Nonempty (A ⟶ B) ↔ Nonempty (B ⟶ A)

/-- **World-Whole as Connected Category**: No substance is isolated from the
Commercium. The category of substances must be connected, ensuring every
substance participates in the web of mutual determination. -/
class WorldWhole : Prop where
  connected : IsConnected Substance

end Cosmology


-- ============================================================================
-- PART III: THE INTELLECTUS ARCHETYPUS AND FINITE UNDERSTANDING
-- ============================================================================

/-!
# Part III: Divine vs Finite Understanding (Herz Letter, 1772)

Laywine (2006, §2) emphasizes that the contrast between divine and finite
understanding drives Kant's development in the 1770s. The letter to Marcus
Herz (Ak 10:129–35) sets up the problem:

* **Intellectus Archetypus** (divine): "representations create their own
  objects" (Ak 10:130). The act of thinking and the object thought are
  identical; hence God cannot fail to know his creation.

* **Intellectus Ectypus** (finite/human): Cannot create its objects
  (unlike God), cannot be merely affected by them (unlike sensibility).
  Its representations must relate to objects by some *third way*.

Laywine (2006, p. 65): "a finite understanding cannot create its objects
and must therefore relate its representations to them in some other way."

We formalize this with a `MindType` distinction. The divine mind is
"archetypal": its representation functor is an equivalence (creating and
knowing are the same act). The finite mind is "ectypal": its representation
functor is merely faithful — it preserves distinctions but does not
generate its objects.
-/

section IntellectualFinitude

/- The type of possible objects of thought (noumena / things in themselves). -/
variable (Noumenon : Type u) [Category.{v} Noumenon]

/- The type of representations in the mind. -/
variable (Representation : Type u) [Category.{v} Representation]

/-- **Intellectus Archetypus** (Divine Understanding):
The representation functor is an *equivalence* — the act of representing
and the act of creating are identical. "We conceive of divine cognitions
as the models [Urbilder] of things" (Herz letter, Ak 10:130). -/
class IntellectusArchetypus (F : Functor Noumenon Representation) : Prop where
  creative : F.IsEquivalence

/-- **Intellectus Ectypus** (Finite Understanding):
The representation functor is merely *faithful* — it preserves the
distinctness of objects but cannot generate them. The finite mind
"cannot create its objects and must therefore relate its representations
to them in some other way" (Laywine 2006, p. 65). -/
class IntellectusEctypus (F : Functor Noumenon Representation) : Prop where
  receptive : F.Faithful

end IntellectualFinitude


-- ============================================================================
-- PART IV: THE DUISBURG NACHLAß (≈1775)
-- ============================================================================

/-!
# Part IV: The Duisburg Nachlaß — Functions of Apperception

Laywine (2006, §§3–5) reconstructs the "philosophical laboratory" of the
Duisburg Nachlaß (R 4674–4684, Ak 17:643–673), dateable to ≈1775 by a
letter on the reverse of the paper.

## The Three Functions of Apperception

Kant identifies three "exponents" or "titles of the understanding" — relations
that the thinking self has to its own thoughts, and which serve as patterns
(*Urbilder*) for all empirical thought:

1. **Substance / Accident** (Inhärenz): The self as absolute subject underlying
   its thoughts as predicates. → Categorical judgments (S is P).

2. **Ground / Consequence** (Dependenz): The relation of thoughts as following
   from one another. → Hypothetical judgments (If P then Q).

3. **Part / Whole** (Composition): Thoughts composed into a composite totality.
   → Disjunctive judgments (P or Q or R).

Laywine (2006, p. 73) quotes R 4674 (Ak 17:647):
"Apperception is the consciousness of thought . . . Herewith are three
exponents: 1. that of the relation [of my thoughts as accidents to myself as]
subject, 2. of the relation of consequences with one another, [3.] that of
the composition."

## The Exposition of Appearances

The "exposition of appearances" is the operation of *making appearances
objective* by subjecting them to the functions of apperception. Objectivity
= determinability by universal laws = necessary relations among appearances
in a unified spatiotemporal whole.

R 4674 (Ak 17:643): exposition is "the determination of the ground upon
which rests the joining [Zusammenhang] of sensations in appearances."
-/

section DuisburgNachlass

/-- The three **Functions of Apperception** (Funktionen der Apperzeption),
also called "exponents" or "titles of the understanding."

These are the relational patterns the thinking self finds in its own
self-awareness and projects onto appearances. -/
inductive FunctionOfApperception : Type where
  /-- **Inhärenz**: Substance / Accident.
  "The I expresses the substantial" (L1, Ak 28[1]:225–6). -/
  | inherence : FunctionOfApperception
  /-- **Dependenz**: Ground / Consequence.
  Thoughts relate as ground to consequence. -/
  | dependence : FunctionOfApperception
  /-- **Composition**: Part / Whole.
  Thoughts compose into a totality. -/
  | composition : FunctionOfApperception

/-- Each function of apperception gives rise to a specific logical form
of judgment. This maps to the table of judgments. -/
inductive JudgmentForm : Type where
  /-- Categorical: S is P (from Inhärenz). -/
  | categorical : JudgmentForm
  /-- Hypothetical: If P then Q (from Dependenz). -/
  | hypothetical : JudgmentForm
  /-- Disjunctive: P or Q or R (from Composition). -/
  | disjunctive : JudgmentForm

/-- The functions of apperception ground the logical forms of judgment.
"The mind is thus itself the model [das Urbild] of such a synthesis
through original and not derived thought" (R 4674, Ak 17:646–7). -/
def apperceptionToJudgment : FunctionOfApperception → JudgmentForm
  | .inherence  => .categorical
  | .dependence => .hypothetical
  | .composition => .disjunctive

/- An **Appearance** is raw sensory content that is not yet "objective."
Objectivity requires subjection to the functions of apperception. -/
variable (Appearance : Type u)

/-- A **Perception** is an appearance of which we are conscious
(R 4679, Ak 17:664). -/
structure Perception (Appearance : Type u) where
  content : Appearance
  conscious : Prop  -- "those appearances of which [the mind] is conscious"

/-- The **Exposition of Appearances**: "the determination of the ground
upon which rests the joining of sensations in appearances"
(R 4674, Ak 17:643).

An exposition assigns to each perception a function of apperception
under which it is subsumed. "Every perception must stand under a title
of the understanding, because otherwise it gives no concept and nothing
is thought thereby" (R 4679, Ak 17:664). -/
def Exposition (Appearance : Type u) :=
  Perception Appearance → FunctionOfApperception

/-- **Objectivity** in the Duisburg sense: An appearance is made objective by
bringing it under a function of apperception. This means it is "determined
from the universal and will be represented objectively"
(R 4677, Ak 17:658). -/
structure ObjectiveRepresentation (Appearance : Type u) where
  perception : Perception Appearance
  function   : FunctionOfApperception
  /-- The perception stands under this title of the understanding. -/
  subsumed   : Prop

end DuisburgNachlass


-- ============================================================================
-- PART V: EKTHESIS AND CARTOGRAPHY OF SENSIBILITY
-- ============================================================================

/-!
# Part V: Ekthesis and the Cartography of Sensibility

Laywine (2020, Ch. 4; reviewed in Buholzer 2021) develops the idea that
perception is *map-making*. The key term is *ekthesis* (ἔκθεσις), from
the presentation convention of geometrical proofs in Euclid: after the
enunciation of a general rule, the ekthesis provides a labelled
illustration of a "representative case" (Laywine 2020, p. 31, on R 4674).

The mind projects local "sightings" of raw appearances onto the a priori
coordinate grid of Space and Time (Pure Intuition). An un-unified stream
of such sightings is a `ChartedSpace` — an atlas of local maps — without
any guarantee of global consistency.

Laywine (2006, §4) already sketches this in terms of empirical thought:
"your thinking will play itself out against a grid of throughways laid out
in one and the same space and persisting through one and the same time"
(p. 68). The 2020 book makes the cartographic metaphor systematic.
-/

section Cartography

/- Pure Space and Time: the a priori coordinate grid (the Model Space). -/
variable (PureIntuition : Type u) [TopologicalSpace PureIntuition]

/- The raw manifold of empirical appearances (the space to be charted). -/
variable (SensibleManifold : Type u) [TopologicalSpace SensibleManifold]

/-- **Ekthesis (A Single Perceptual Sighting)**: A local chart projecting
a patch of sense data onto Pure Intuition. A `PartialHomeomorph` captures
the restricted, local character of each perceptual act. -/
abbrev PerceptualSighting := OpenPartialHomeomorph SensibleManifold PureIntuition

/-- **The Empirical Atlas (Humean Stream of Perceptions)**: An un-unified
collection of local sightings is merely a `ChartedSpace` — an atlas
without global consistency. This is the state *before* the categories
impose unity. -/
abbrev EmpiricalAtlas := ChartedSpace PureIntuition SensibleManifold

end Cartography


-- ============================================================================
-- PART VI: THE TRANSCENDENTAL DEDUCTION AS A COSMOLOGY OF EXPERIENCE
-- ============================================================================

/-!
# Part VI: The Transcendental Deduction — A Cosmology of Experience

Laywine's central thesis (2020): the epistemological deduction of the
categories *structurally recapitulates* God's legislation of cosmological
laws in the early metaphysics.

In the pre-critical cosmology, God's intellect prescribed universal laws
to substances, causing them to form a world-whole. In the Transcendental
Deduction, the *human understanding* prescribes universal laws to
*appearances*, causing them to form a unified experience (= nature).

Laywine (2006, p. 76): "the understanding is not best characterized as a
faculty of thought or even judging, but rather as a faculty for giving
laws to nature" (cf. A 126–7). This is the claim that "the understanding
makes nature itself possible."

## The StructureGroupoid Formalization

The Pure Concepts of the Understanding (Categories) are the invariant
*a priori* rules constraining how local perceptual charts may be glued.
A `StructureGroupoid` on the model space (Pure Intuition) specifies the
valid transition functions between charts.

`HasGroupoid M G` then asserts that every chart transition in the
maximal atlas of M belongs to G — the Categories constrain all possible
experience. This is the formal content of the "I think must be able to
accompany all my representations" (B 131).

## The Sheaf-Theoretic Perspective (Appendix)

Alternatively, the Unity of Apperception can be expressed as the
*sheaf condition* on a presheaf of representations: local data must
glue uniquely to global sections. The "I think" = the global section
over the total space.
-/

section TranscendentalDeduction

variable {PureIntuition : Type u} [TopologicalSpace PureIntuition]

/- The **Categories** as a Structure Groupoid on Pure Intuition.

The categories dictate the valid transition functions (Causality, Community,
etc.) allowed when moving from one subjective perception to another.
A `StructureGroupoid H` is a set of partial homeomorphisms of H, closed
under composition, inversion, restriction, and containing the identity. -/
variable (Categories : StructureGroupoid PureIntuition)

/-- **The Cosmology of Experience** (Laywine's central thesis).

By enforcing the Categories (as a Structure Groupoid), local empirical
maps are forced to glue consistently. `HasGroupoid M G` asserts that
every chart transition in M's maximal atlas belongs to G.

This is the formal analog of Laywine's claim that the Deduction
structurally recapitulates the early cosmology: where God once legislated
cosmological laws to substances, the understanding now legislates the
categories to appearances.

"The understanding is . . . a faculty for giving laws to nature" (A 126–7). -/
class CosmologyOfExperience (SensibleManifold : Type u) [TopologicalSpace SensibleManifold]
    [ChartedSpace PureIntuition SensibleManifold] : Prop where
  /-- The "I Think" forces local empirical maps to conform to universal laws:
  every chart transition belongs to the Categories groupoid. -/
  unity_of_apperception : HasGroupoid SensibleManifold Categories

end TranscendentalDeduction


section SheafPerspective

/-!
## Appendix: The Sheaf-Theoretic Perspective

A presheaf `F : Presheaf C X` over the topological space of appearances
assigns representations to local open regions. The sheaf condition states
that compatible local sections glue uniquely to global sections —
precisely the content of "the I think must be able to accompany all my
representations" (B 131–132).
-/

variable {X : TopCat.{u}} (F : TopCat.Presheaf (Type v) X)

/-- **Unity of Apperception** (sheaf-theoretically):
Local representations glue into a globally consistent objective Nature. -/
class UnityOfApperception where
  /-- The sheaf condition: local representations must uniquely glue. -/
  is_sheaf : F.IsSheaf
  /-- The "I think" — objective nature as the global section over `⊤`. -/
  i_think : F.obj (op ⊤)

end SheafPerspective


-- ============================================================================
-- PART VII: THE PRODUCTIVE IMAGINATION (POST-PARALOGISMS)
-- ============================================================================

/-!
# Part VII: The Productive Imagination (Post-Paralogisms)

Laywine (2006, §5) notes that Kant's discovery of the Paralogisms of Pure
Reason undermined the metaphysical psychology grounding the Duisburg Nachlaß
story. He could no longer dogmatically claim that the functions of
apperception derive from intellectual intuition of the soul as substance.

The solution: the **productive imagination** replaces the metaphysical
psychology. Kant characterizes the understanding anew as "the unity of
apperception in relation to the faculty of imagination" (B 12, Ak 23:18).
The categories become "representations of something (appearance) as such
insofar as it is represented through transcendental synthesis of the
imagination" (Ak 23:19).

Formally: where the Duisburg Nachlaß grounded synthesis in intellectual
self-intuition, the critical philosophy grounds it in the productive
imagination operating under the categories. The StructureGroupoid
formalization survives this transition — what changes is the *justification*
for the groupoid constraints, not the constraints themselves.
-/

section ProductiveImagination

/- The **Synthesis of the Imagination** bridges sensibility and understanding.
It is a functor from the empirical atlas (local perceptual data) to the
category of objective representations (conceptualized experience).

The synthesis takes raw chart data and produces representations that
satisfy the groupoid constraints imposed by the Categories. -/
variable (EmpiricalData : Type u) [Category.{v} EmpiricalData]
variable (ObjectiveExperience : Type u) [Category.{v} ObjectiveExperience]

/-- Productive imagination as a functor from raw sensory data to
objective experience. Unlike the intellectus archetypus, this functor
need not be an equivalence; unlike mere association (Humean habit),
it must be faithful to the categorical structure. -/
class ProductiveImagination (Synth : Functor EmpiricalData ObjectiveExperience) : Prop where
  /-- The synthesis preserves the categorical structure (is faithful). -/
  faithful : Synth.Faithful
  /-- The synthesis is not merely receptive — it actively produces
  the objective ordering (is not conservative/identity on objects). -/
  productive : ¬Function.Injective Synth.obj ∨ ¬Function.Surjective Synth.obj

end ProductiveImagination


-- ============================================================================
-- PART VIII: THE PRINCIPLE OF CONVENIENCE AND REGULATIVE UNITY
-- ============================================================================

/-!
# Part VIII: The Principle of Convenience and Regulative Unity

Laywine (2006, §2) discusses how the Inaugural Dissertation restricts
cosmological ambitions. The physical universe, if infinite, can never be
completely given in experience. Our thought of it as governed by universal
laws everywhere is a "purely subjective principle of convenience"
(Inaugural Dissertation §30, Ak 2:417–18).

"We simply cannot renounce it without renouncing at the same time all
rational motivation for investigating the world around us" (Laywine 2006,
p. 67).

This becomes the *regulative* use of reason in the first Critique: the
idea of a complete world-whole is a *focus imaginarius* that directs but
never constitutes knowledge.
-/

section RegulativeIdeas

/-- A **Regulative Ideal** is a directed system (filtered diagram) that
guides inquiry without being reachable as a completed whole. The totality
of experience is such an ideal: we can always extend our empirical atlas
but never complete it.

Formally: a filtered category indexing an ascending chain of ever-larger
subworlds of experience. -/
class RegulativeIdeal (J : Type u) [Category.{v} J] : Prop where
  /-- The indexing category is filtered (directed): any two stages can
  be extended to a common later stage. -/
  filtered : IsFilteredOrEmpty J
  /-- The system is genuinely open-ended: no terminal object exists
  (the totality is never completed "once and for all"). -/
  no_terminus : ∀ (t : J), IsEmpty (CategoryTheory.Limits.IsTerminal t)

end RegulativeIdeas

end Philosophy.Kant.Laywine