import Mathlib

universe u v w

namespace Menn.Aristotle

/-!
# Menn's Causal Ontology in Lean 4

Stephen Menn demonstrates that Aristotle avoids the Parmenidean trap by shifting 
ontology to a causal methodology (Posterior Analytics II). This file utilizes 
`mathlib4`'s native Set Theory, Order Theory, and Well-Founded Relations to 
mathematically execute Aristotelian metaphysics.
-/

/-! ### 1. The Hylomorphic Nexus (Solving Extensional Collapse) -/

/--
An `Ontology` defines a scientific domain. It strictly separates **Intensional Forms** 
(the terms/essences of science) from **Extensional Matter** (the subjects of predication).
By separating these, we avoid the "extensional collapse" where two distinct forms 
that happen to share the same matter are deemed logically identical.
-/
class Ontology (Matter : Type u) (Form : Type v) where
  /-- The extensional realization of a Form in the material domain. -/
  ext : Form → Set Matter
  
  /-- 
  The explanatory causal order. `causes M F` means `M` is the syllogistic 
  middle term (Formal Cause/Ousia) that directly explains why `F` exists.
  -/
  causes : Form → Form → Prop
  
  /-- Aristotle's Axiom of Finite Causality (Metaphysics α 2): 
      There is no infinite regress of explanatory causes. -/
  wf_causes : WellFounded causes
  
  /-- 
  The Syllogistic Axiom (Posterior Analytics II): 
  If M formally causes F, then M universally entails F in the material domain.
  -/
  causes_subset : ∀ {M F}, causes M F → ext M ⊆ ext F

export Ontology (ext causes wf_causes causes_subset)

/-! ### 2. Ontological Reduction (1-Place to 2-Place Being) -/

/-- 1-place existence. Parasitic on the coerced dependent subtype `↥(ext F)`. -/
abbrev ExistsOnePlace {Matter Form} [Ontology Matter Form] (F : Form) : Prop := 
  Nonempty ↥(ext F)

/-- 2-place predication ("Some Matter is F"). -/
abbrev ExistsTwoPlace {Matter Form} [Ontology Matter Form] (F : Form) : Prop := 
  (ext F).Nonempty

/--
**Menn's Foundational Equivalence (Z.17)**: 
1-place existence is analytically equivalent to 2-place predication.
Mathlib's `Set.nonempty_coe_sort` theorem *is* Aristotle's ontological reduction.
-/
theorem being_reduction {Matter Form} [Ontology Matter Form] (F : Form) : 
    ExistsOnePlace F ↔ ExistsTwoPlace F :=
  Set.nonempty_coe_sort


/-! ### 3. The Engine of Science (Posterior Analytics II) -/

/-- A `FormalCause` of F is an instantiated middle term M that causes F. -/
structure FormalCause {Matter Form} [Ontology Matter Form] (F : Form) where
  Middle : Form
  is_cause : causes Middle F
  is_instantiated : ExistsTwoPlace Middle

/-- 
**Scientific Actuality**: A formal cause logically guarantees existence.
Aristotle's syllogism is executed by native Lattice monotonicity (`Set.Nonempty.mono`).
-/
theorem existence_of_cause {Matter Form} [Ontology Matter Form] {F : Form} 
    (c : FormalCause F) : ExistsOnePlace F := by
  rw [being_reduction]
  exact c.is_instantiated.mono (causes_subset c.is_cause)

/-- A Causal Chain is the reflexive-transitive closure of direct formal causes. -/
abbrev CausalChain {Matter Form} [Ontology Matter Form] := 
  Relation.ReflTransGen (causes (Matter := Matter) (Form := Form))

/-- 
**Scientific Deduction**:
If a chain of causes links M to F, M mathematically guarantees F.
-/
theorem actualization_of_effect {Matter Form} [Ontology Matter Form] 
    {M F : Form} (chain : CausalChain M F) : ext M ⊆ ext F := by
  induction chain with
  | refl => exact fun _ h => h
  | head h_step _ ih => exact Set.Subset.trans (causes_subset h_step) ih

/-- An Archa (First Principle) is a Form with no prior formal cause. -/
def IsArcha {Matter Form} [Ontology Matter Form] (A : Form) : Prop := 
  ∀ M, ¬ causes M A

/-- 
**Theorem (Metaphysics α 2 / Z.17)**: 
Every form mathematically traces back to an uncaused First Principle (`Archa`).
Menn (p. 8): "we will find them by beginning with some effect and reasoning back... 
until we reach a stopping-point of explanation."
-/
theorem resolves_to_archa {Matter Form} [Ontology Matter Form] (F : Form) : 
    ∃ A, CausalChain A F ∧ IsArcha A := by
  induction F using (wf_causes (Matter := Matter) (Form := Form)).induction with
  | h X ih =>
    by_cases hX : IsArcha X
    · exact ⟨X, Relation.ReflTransGen.refl, hX⟩
    · dsimp [IsArcha] at hX
      push_neg at hX
      rcases hX with ⟨M, hM⟩
      rcases ih M hM with ⟨A, chain_A_M, archa_A⟩
      exact ⟨A, Relation.ReflTransGen.head hM chain_A_M, archa_A⟩


/-! ### 4. Dismissed Senses of Being (Metaphysics E 2-4) -/

/-- A target set of matter has a unified cause if an intensional Form M necessitates it. -/
def HasUnifiedCause {Matter Form} [Ontology Matter Form] (target : Set Matter) : Prop :=
  ∃ M : Form, ext M ⊆ target ∧ (ext M).Nonempty

/-- 
**Being Per Accidens (E 2-3)**
Accidental being is the intersection (`∩`) of two forms. 
Menn notes accidental being is dismissed from science because there is no 
single intensional Form `M` that universally causes a coincidental intersection.
-/
def IsAccidental {Matter Form} [Ontology Matter Form] (F G : Form) : Prop :=
  (ext F ∩ ext G).Nonempty ∧ ¬ HasUnifiedCause (ext F ∩ ext G)

/-- 
**Being As Truth (E 4)**
Modeled via mathlib's `Prop`. Truth applies to negations, but negations lack 
an intensional essence (no `Form` for "not-white"), yielding no formal cause.
-/
abbrev BeingAsTruth (P : Prop) : Prop := P


/-! ### 5. Potentiality (Dunamis) and Actuality (Energeia) (Metaphysics Θ) -/

/--
**Dunamis (Potentiality)**
Countering the Parmenidean trap: A not-yet-existent object possesses no power. 
Powers belong strictly to *actually existing* agents and matters.
-/
structure Dunamis {Matter Form : Type u} [Ontology Matter Form] 
    (Agent : Type w) (F : Form) where
  active_power  : Set Agent
  passive_power : Set Matter
  actualizes    : ∀ a ∈ active_power, ∀ m ∈ passive_power, m ∈ ext F

/-- "F is potentially" means the actual preconditions exist, but F is not yet. -/
structure BeingPotentially {Matter Form : Type u} [Ontology Matter Form] 
    {Agent : Type w} {F : Form} (d : Dunamis Agent F) : Prop where
  a : Agent
  m : Matter
  has_active  : a ∈ d.active_power
  has_passive : m ∈ d.passive_power
  not_yet     : m ∉ ext F

/-- 
**Theorem: Priority of Actuality (Θ 8)**: 
Potential being mathematically structurally demands the *actual* (1-place) existence 
of the Agent and the Matter. Actuality strictly precedes potentiality.
-/
theorem priority_of_actuality {Matter Form : Type u} [Ontology Matter Form] 
    {Agent : Type w} {F : Form} {d : Dunamis Agent F} 
    (pot : BeingPotentially d) : Nonempty Agent ∧ Nonempty Matter :=
  ⟨⟨pot.a⟩, ⟨pot.m⟩⟩


/-! ### 6. The Theological Limit: Simple Substances (Metaphysics Λ) -/

/-- 
**Simple Substances (The Prime Mover)**
Menn (p. 30): "If F is a simple immaterial substance, it does not [have a 2-place 
equivalent]... it is immune to causal analysis."

A Simple Substance has no underlying matter. If one attempts to map it 
hylomorphically, the mathematical equivalence `≃` must be `IsEmpty`.
-/
class SimpleSubstance (Θ : Type u) : Prop where
  is_actual : Nonempty Θ
  immaterial : ∀ {Matter Form : Type u} [Ontology Matter Form] (F : Form), 
      IsEmpty (Θ ≃ ↥(ext F))

/-- An entity `X` has a formal cause if it can be hylomorphically mapped to a Form. -/
def HasFormalCause (X : Type u) : Prop :=
  ∃ (Matter Form : Type u) (O : Ontology Matter Form) (F : Form),
    Nonempty (X ≃ ↥(@ext Matter Form O F)) ∧ ∃ (M : Form), @causes Matter Form O M F

/--
**Anti-Thomistic Climax (Z.17 / Λ)**
Because simple substances lack matter, their existence cannot be unrolled 
into "S is P". Therefore, they mathematically cannot possess a formal cause.
They are pure, uncaused Energeia.
-/
theorem simple_substance_uncaused {Θ : Type u} [S : SimpleSubstance Θ] : 
    ¬ HasFormalCause Θ := by
  rintro ⟨Matter, Form, O, F, ⟨equiv⟩, _⟩
  exact (S.immaterial F).false equiv

end Menn.Aristotle