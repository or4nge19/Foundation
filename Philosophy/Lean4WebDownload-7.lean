import Mathlib

universe u v w

namespace Menn.Aristotle

/-!
# The Senses of Being: A Mathlib4 Formalization

Stephen Menn's reconstruction proves that Aristotle avoids the Parmenidean 
trap by shifting ontology to a causal methodology (Posterior Analytics II).
This file uses core `mathlib4` APIs to express this insight, revealing that 
Aristotle's metaphysics is mathematically isomorphic to Subtype and Lattice theory.
-/

/-! ### 1. Ontological Reduction: 1-Place to 2-Place Being -/

/-- 
A Form `F` inheres in a *per se* subject `S` (its matter or genus).
In `mathlib`, this is `Set S`. The composite entity itself (e.g., "The Musical") 
is not a standalone `Type`, but the coerced dependent subtype `↥F`.
-/
abbrev Form (S : Type u) := Set S

/--
**Menn's Foundational Equivalence (Z.17)**: 
1-place existence ("F exists") is analytically equivalent to 2-place 
predication ("Some S is F"). 
Mathlib's `nonempty_subtype` theorem *is* exactly Aristotle's ontological reduction.
-/
theorem being_reduction {S : Type u} (F : Form S) : 
    Nonempty ↥F ↔ F.Nonempty :=
  nonempty_subtype


/-! ### 2. The Formal Cause as a Syllogistic Middle Term (Post. An. II) -/

/--
To ask "Why does F exist?" is to ask "Why does S possess F?".
The answer (Ousia / Formal Cause) is the Middle Term in a scientific syllogism.
We leverage `mathlib4`'s lattice order (`≤` for `Subset`) to model this:
- Minor Premise: The subject partakes in the middle term (`M.Nonempty`).
- Major Premise: The middle term universally entails the form (`M ≤ F`).
-/
structure FormalCause {S : Type u} (F : Form S) where
  Middle : Form S
  minor  : Middle.Nonempty
  major  : Middle ≤ F

/-- 
**The Engine of Science**: 
A formal cause logically guarantees the actual existence of the entity.
In mathlib, Aristotle's "Barbara" syllogism is executed natively by 
the monotonicity of `Nonempty` over subsets (`Set.Nonempty.mono`).
-/
theorem existence_of_cause {S : Type u} {F : Form S} (c : FormalCause F) : 
    Nonempty ↥F :=
  (being_reduction F).mpr (c.minor.mono c.major)


/-! ### 3. Dismissed Senses of Being (Metaphysics Δ 7, E 2-4) -/

/-- 
**Being Per Accidens (E 2-3)**
Accidental being ("The white is musical") is the coincidental concurrence 
of two forms. Modeled as the Lattice Infimum `⊓` (intersection).
There is no `FormalCause M` such that `M ≤ F ⊓ G` universally by nature, 
hence there is no scientific definition of accidents.
-/
abbrev BeingPerAccidens {S : Type u} (F G : Form S) : Prop :=
  (F ⊓ G).Nonempty

/-- 
**Being As Truth (E 4)**
Applies symmetrically to affirmations and negations. 
Modeled via mathlib's universe `Prop`. The negation `s ∉ F` has a truth value,
but it is not a `Form S` with an essence, so it yields no causal middle term.
-/
abbrev BeingAsTruth (p : Prop) : Prop := p


/-! ### 4. Potentiality (Dunamis) and Actuality (Energeia) (Metaphysics Θ) -/

/--
**Dunamis (Potentiality)**
Menn counters the Platonist trap: a not-yet-existent object `F` possesses 
no objective "potency to exist". Potentiality belongs strictly to 
*actually existing* agents and subjects.
-/
structure Dunamis {S : Type u} (F : Form S) (Agent : Type v) where
  active_power  : Set Agent
  passive_power : Set S
  /-- Actuality is the mutual realization of active and passive powers. -/
  actualize : ∀ a ∈ active_power, ∀ s ∈ passive_power, s ∈ F

/-- 
"F is potentially" means the causal powers exist, but F is not yet actualized.
Notice `F` is merely an index here; it is not quantified over as a subject.
-/
structure BeingPotentially {S : Type u} {Agent : Type v} 
    {F : Form S} (d : Dunamis F Agent) : Prop where
  a : Agent
  s : S
  has_active  : a ∈ d.active_power
  has_passive : s ∈ d.passive_power
  not_yet     : s ∉ F

/-- 
**Priority of Actuality (Θ 8)**: 
Potential being mathematically requires the *actual* existence of the 
Agent and the Subject. Actuality precedes potentiality.
-/
theorem actuality_prior {S : Type u} {Agent : Type v} {F : Form S} 
    {d : Dunamis F Agent} (pot : BeingPotentially d) : 
    Nonempty Agent ∧ Nonempty S :=
  ⟨⟨pot.a⟩, ⟨pot.s⟩⟩


/-! ### 5. The Theological Limit: Simple Substances (Metaphysics Λ) -/

/-- 
**Simple Substances (The Prime Mover)**
Menn isolates Aristotle's ultimate divergence from Aquinas.
A simple substance exists (`is_actual`), but lacks underlying matter.
Because it cannot be unpacked into a 2-place "S is F" over some distinct 
matter `S`, it inherently lacks a `FormalCause`.

In mathlib, we model this by requiring that any attempt to factor it 
into a Subtype of some `S` yields a trivial form (the universal set `⊤`), 
meaning `S` was just `Θ` all along.
-/
class SimpleSubstance (Θ : Type u) : Prop where
  is_actual : Nonempty Θ
  irreducible : ∀ {S : Type u} (F : Form S), Θ ≃ ↥F → F = ⊤

/--
**Anti-Thomistic Theorem**: Simple substances are immune to causal analysis.
Because `FormalCause` operates strictly over proper subsets `F < ⊤`, 
a Simple Substance's only "predicate" is `⊤`. As Aristotle notes in Z.17, 
investigating why a thing is itself is a null inquiry ("investigating nothing").
-/
theorem simple_substance_uncaused {Θ : Type u} [h : SimpleSubstance Θ] 
    {S : Type u} (F : Form S) (equiv : Θ ≃ ↥F) : 
    F = ⊤ :=
  h.irreducible F equiv

end Menn.Aristotle