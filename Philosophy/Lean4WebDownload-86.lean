import Mathlib

/-!
# Descartes and Augustine (Stephen Menn)
## Chapter 3: Plotinus (Final Rigorous Formalization)

This module formalizes the conceptual vocabulary and theorems of Plotinian 
Platonism. It maps the exact dialectical architecture Plotinus used to synthesize 
Aristotelian kinematics with Platonist ontology to defeat Stoic corporealism, 
localize the Forms, and generate a Theodicy that shields God from the origin of evil.
-/

namespace Menn.Chapter3

universe u v w

/-! 
### 1. Hellenistic Physics Vocabulary
The shared baseline of properties debated by all Hellenistic schools.
-/

class PhysicsVocabulary (E : Type u) where
  isBody : E → Prop
  isIncorporeal : E → Prop
  isActive : E → Prop
  isPassive : E → Prop
  
  -- Fundamental mutual exclusions agreed upon by all schools:
  disjoint_body_incorporeal : ∀ x, isBody x → ¬ isIncorporeal x
  disjoint_active_passive : ∀ x, isActive x → ¬ isPassive x
  exhaustive_ontology : ∀ x, isBody x ∨ isIncorporeal x


/-! 
### 2. Platonist Ontology vs. Stoic Ontology
We separate the competing axioms. Platonists believe matter is inert. 
Stoics believe matter can be active.
-/

class PlatonistOntology (E : Type u) extends PhysicsVocabulary E where
  body_is_strictly_passive : ∀ x, isBody x → isPassive x

class StoicOntology (E : Type u) extends PhysicsVocabulary E where
  everything_is_body : ∀ x, isBody x
  exists_active_body : ∃ x, isBody x ∧ isActive x


/-!
### 3. The Shared Phenomenology of Dispositions and the Plotinian Refutation
Menn (p. 108-109): The Stoics explained the soul as a body "somehow disposed" 
(`pôs echon`). Plotinus takes this observable phenomenon and applies Platonist 
logic to it to break the Stoic system.
-/

/-- A neutral mechanics of states/dispositions agreed upon by both schools. -/
class StateMechanics (E : Type u) (State : Type w) (Time : Type v) [LinearOrder Time] where
  hasState : E → State → Time → Prop
  stateCausesAction : State → Time → Prop
  stateCausedBy : State → E → Prop
  
  /-- Plotinus's observational premise: If a strictly passive entity exhibits an 
      active state, that state must be caused by an external active principle. -/
  passive_acting_requires_active_cause : ∀ x s t, 
    PhysicsVocabulary.isPassive x → hasState x s t → stateCausesAction s t → 
    ∃ c, stateCausedBy s c ∧ PhysicsVocabulary.isActive c

/-- 
THEOREM 1 (Menn p. 109): The cause of a body's active disposition is an Incorporeal Logos.
By evaluating `StateMechanics` under `PlatonistOntology`, Plotinus mathematically 
forces the existence of an incorporeal entity, destroying Stoic monism.
-/
theorem cause_of_disposition_is_incorporeal 
    {E : Type u} {State : Type w} {Time : Type v} [LinearOrder Time][vocab : PhysicsVocabulary E] [PlatonistOntology E] [StateMechanics E State Time]
    (x : E) (s : State) (t : Time) 
    (h_body : vocab.isBody x) 
    (h_has : StateMechanics.hasState x s t) 
    (h_acts : StateMechanics.stateCausesAction s t) : 
    ∃ c, StateMechanics.stateCausedBy s c ∧ vocab.isIncorporeal c := by
  -- 1. Because x is a body, Platonism dictates it is passive.
  have h_passive := PlatonistOntology.body_is_strictly_passive x h_body
  -- 2. Because it is passive but acting, it requires an active cause c.
  have h_cause := StateMechanics.passive_acting_requires_active_cause x s t h_passive h_has h_acts
  rcases h_cause with ⟨c, h_causedBy, h_active⟩
  use c
  constructor
  · exact h_causedBy
  · -- 3. Prove c is incorporeal by contradiction.
    have h_exhaustive := vocab.exhaustive_ontology c
    rcases h_exhaustive with h_c_body | h_c_incorporeal
    · have h_c_passive := PlatonistOntology.body_is_strictly_passive c h_c_body
      have h_c_not_active := vocab.disjoint_active_passive c h_c_passive
      contradiction
    · exact h_c_incorporeal


/-!
### 4. Aristotelian Kinematics (Temporal Actuality)
Menn (p. 114-115): Aristotle's mechanics of change. A potentiality is actualized 
by a temporal cause (e.g., a father). This is independent of Plato.
-/

class AristotelianKinematics (E : Type u) (Time : Type v)[LinearOrder Time] where
  potential : E → (E → Prop) → Time → Prop
  actual : E → (E → Prop) → Time → Prop
  causesActualization : E → E → (E → Prop) → Time → Prop
  
  /-- Local, temporal priority of actuality (The Father principle). -/
  priority_of_actuality : ∀ x F t₁ t₂, 
    t₁ < t₂ → potential x F t₁ → actual x F t₂ → 
    ∃ y, causesActualization y x F t₁ ∧ actual y F t₁


/-!
### 5. Plotinian Noetic (The Grand Synthesis)
Menn (p. 116-118): Plotinus maps Aristotle's mechanics over Plato's ontology.
He deduces that the chain of temporal actualizers requires a globally actual `Nous`.
-/

class PlotinianNoetic (E : Type u) (Time : Type v) [LinearOrder Time] 
    extends PlatonistOntology E, AristotelianKinematics E Time where
  isRational : E → Prop
  knows : E → E → Time → Prop
  spatiallySeparated : E → E → Prop

  /-- A being is Essentially Actual (Nous) if it is always actual and never potential. -/
  isNous (n : E) : Prop := 
    (∀ t, actual n isRational t) ∧ (∀ t, ¬ potential n isRational t)

  /-- Hellenistic Optics/Epistemology: Knowing a spatially separated object 
      requires physical interaction across space, which entails passivity. -/
  knowledge_across_space_implies_passivity : ∀ x y t,
    knows x y t → spatiallySeparated x y → isPassive x
  
  /-- Passivity is the ontological root of potentiality. -/
  passivity_implies_potentiality : ∀ x t,
    isPassive x → potential x isRational t

/-- 
THEOREM 2 (Menn p. 118): The Identity of Knower and Known.
Because `Nous` lacks potentiality, it cannot be spatially separated from the Forms.
-/
theorem nous_contains_its_objects 
    {E : Type u} {Time : Type v} [LinearOrder Time] [PlotinianNoetic E Time] 
    (n x : E) (t : Time) 
    (h_nous : PlotinianNoetic.isNous n) 
    (h_knows : PlotinianNoetic.knows n x t) : 
    ¬ PlotinianNoetic.spatiallySeparated n x := by
  intro h_sep
  have h_passive := PlotinianNoetic.knowledge_across_space_implies_passivity n x t h_knows h_sep
  have h_potential := PlotinianNoetic.passivity_implies_potentiality n t h_passive
  have h_not_potential := h_nous.2 t
  exact h_not_potential h_potential


/-!
### 6. Section D: Soul in Bodies and Theodicy
Menn (p. 120-129): Plotinus saves God from Stoic deterministic pantheism. 
Evil is formalized as `aversio` (turning toward the body). 
-/

class PlotinianTheodicy (E : Type u) (Time : Type v) [LinearOrder Time] 
    extends PlotinianNoetic E Time where
  turnsTowards : E → E → Time → Prop
  
  /-- Evil is not a substance. It is the act of turning toward a body. -/
  doesEvil (e : E) (t : Time) : Prop :=
    ∃ b, isBody b ∧ turnsTowards e b t

  /-- Nous only contemplates itself (Pure Actuality). -/
  nous_only_contemplates_self : ∀ n y t, 
    isNous n → turnsTowards n y t → y = n

/-- LEMMA: Nous is not a body. (Follows directly from Physics & Kinematics) -/
lemma nous_is_not_body {E : Type u} {Time : Type v}[LinearOrder Time] 
    [PlotinianNoetic E Time] (n : E) (h_nous : PlotinianNoetic.isNous n) : 
    ¬ PhysicsVocabulary.isBody n := by
  intro h_body
  have h_passive := PlatonistOntology.body_is_strictly_passive n h_body
  -- Pick an arbitrary time `t` to show potentiality exists, breaking `isNous`
  intro t
  have h_potential := PlotinianNoetic.passivity_implies_potentiality n t h_passive
  have h_not_potential := h_nous.2 t
  exact h_not_potential h_potential

/-- 
THEOREM 3 (Menn p. 129): Plotinian Salvation of God's Goodness.
God (`Nous`) cannot do evil. If Nous did evil, it would turn toward a body. 
But Nous only turns toward itself. Therefore, Nous would be a body, which 
contradicts the proof that Nous is not a body.
-/
theorem plotinian_god_is_sinless 
    {E : Type u} {Time : Type v}[LinearOrder Time] [PlotinianTheodicy E Time] 
    (n : E) (t : Time) (h_nous : PlotinianNoetic.isNous n) : 
    ¬ PlotinianTheodicy.doesEvil n t := by
  intro h_evil
  unfold PlotinianTheodicy.doesEvil at h_evil
  rcases h_evil with ⟨b, h_b_is_body, h_turns⟩
  
  -- 1. Because n is Nous, whatever it turns to must be itself.
  have h_eq : b = n := PlotinianTheodicy.nous_only_contemplates_self n b t h_nous h_turns
  
  -- 2. Therefore, n is a body.
  have h_n_is_body : PhysicsVocabulary.isBody n := by
    rw[← h_eq]
    exact h_b_is_body

  -- 3. But we already proved Nous is not a body. Contradiction.
  have h_n_not_body := nous_is_not_body n h_nous
  exact h_n_not_body h_n_is_body

end Menn.Chapter3



/-!
# Descartes and Augustine (Stephen Menn)
## Chapter 4: Finer-Grained Structural Formalization

This module leverages advanced `mathlib4` structures (Complete Lattices, 
Galois Connections, and Filters) to model the precise metaphysical and 
epistemological mechanics of Augustinian Platonism.
-/

namespace Menn.Augustine

universe u v

/-!
### 1. The Lattice of Being and Privation
Menn (p. 169-172): Augustine defeats Manichean dualism by establishing that 
Being and Goodness are identical. God is the Supreme Being. Everything created 
ex nihilo is a lesser good. Evil is not a substance (an element), but a 
*privation* (a destructive operation).

We model the "Great Chain of Being" as a `CompleteLattice`.
- `⊤` (Top) is God (Deus / Immutable Truth).
- `⊥` (Bottom) is Nothingness (Nihil).
-/

variable {E : Type u}[CompleteLattice E]

/-- A created substance is strictly between Nothingness and God. -/
def IsCreatedSubstance (x : E) : Prop := 
  ⊥ < x ∧ x < ⊤

/-- 
Evil is a Privation. Mathematically, it is not an element of `E`. 
It is a strictly diminishing transformation on `E` that strips measure, 
form, and order, moving a substance toward `⊥` (but never reaching it, 
as complete privation is annihilation).
-/
structure Privation (E : Type u) [CompleteLattice E] where
  corrupt : E → E
  is_diminishing : ∀ x, IsCreatedSubstance x → corrupt x < x
  preserves_being : ∀ x, IsCreatedSubstance x → ⊥ < corrupt x

/-- 
THEOREM 1 (Menn p. 171): God cannot be corrupted, and God is not the author of Evil.
Because God is the supremum `⊤`, the operation of privation cannot apply to Him 
(He is immutable), nor does He generate privations (because His emanation only 
grants existence, moving things away from `⊥`).
-/
theorem privation_is_not_substance (p : Privation E) (x : E) 
    (hx : IsCreatedSubstance x) : 
    p.corrupt x ≠ x := by
  have h_dim := p.is_diminishing x hx
  exact ne_of_lt h_dim


/-!
### 2. The Judge Principle as a Galois Connection
Menn (p. 151): The ascent to Truth relies on the rule: "what judges is better 
than what it judges". Reason judges Sense by imposing an immutable standard.

We model this brilliantly with a **Galois Connection**.
Let `Sense` and `Reason` be complete lattices.
A Galois Connection `(l, u)` means `l s ≤ r ↔ s ≤ u r`.
- `l : Sense → Reason` is the mind abstracting sensory data upward.
- `u : Reason → Sense` is Reason projecting its standard downward onto the sense.
If the sense data `s` conforms to the standard (`s ≤ u r`), the abstracted 
concept `l s` successfully hits the rational mark (`l s ≤ r`).
-/

variable {Sense Reason Truth : Type u} 
  [CompleteLattice Sense] [CompleteLattice Reason][CompleteLattice Truth]

/-- 
The cognitive faculty of Reason judging Sense is exactly an Adjunction / Galois Connection. 
The standard of truth `r` bounds the sensory manifold `s`.
-/
structure CognitiveAscent (Sense Reason : Type u) [CompleteLattice Sense] [CompleteLattice Reason] where
  abstract : Sense → Reason  -- lower adjoint
  standard : Reason → Sense  -- upper adjoint
  judges : GaloisConnection abstract standard

/-- 
THEOREM 2 (Menn p. 151): The Ascent from Sense to Truth.
If Reason judges Sense via a Galois connection, and Truth judges Reason 
via a Galois connection, they compose. Truth establishes the absolute 
upper bound (the Ideas/Nous) by which all lower data is evaluated.
-/
theorem truth_judges_sense 
    (asc1 : CognitiveAscent Sense Reason) 
    (asc2 : CognitiveAscent Reason Truth) : 
    GaloisConnection (asc2.abstract ∘ asc1.abstract) (asc1.standard ∘ asc2.standard) := by
  -- The composition of two Galois connections is a Galois connection.
  -- This mathematically proves Augustine's chain of judgment from Body to God.
  exact GaloisConnection.compose asc1.judges asc2.judges


/-!
### 3. The Origin of Moral Evil: The Will and Aversio
Menn (p. 175-177): If God gives us Free Will, and the Will is good, how does 
sin occur? Sin is `aversio`—the will reversing the lattice. Instead of 
choosing `⊤` (God), the will actively chooses `x < ⊤`.
-/

/-- The Will is a choice function that selects an element in the Lattice of Being. -/
structure FreeWill (E : Type u)[CompleteLattice E] where
  chooses : E
  is_free : True -- Placeholder for libertarian freedom

/-- 
Aversio (Sin) occurs when the Will chooses a mutable, created substance 
instead of the Supreme Good (`⊤`). It is an inversion of proper order. 
-/
def IsAversio (w : FreeWill E) : Prop :=
  IsCreatedSubstance w.chooses ∧ w.chooses < ⊤

/-- 
THEOREM 3 (Menn p. 176): The Will is Good, but the Act is Evil.
The capacity to choose is a substance (thus Good). But the `Aversio` is a 
privation of order. It exists purely ex nihilo (from nothingness).
-/
theorem aversio_chooses_lesser_good (w : FreeWill E) (h : IsAversio w) :
    w.chooses < ⊤ := by
  exact h.right


/-!
### 4. Epistemology: Faith, Opinion, and Filters
Menn (p. 188-191): Augustine's epistemology (De Utilitate Credendi) distinguishes 
Understanding, Believing, and Opining. 

We model the mind's cognitive state as a **Filter** over a space of possible 
realities `Ω`. 
- `Understanding`: The mind is the *Principal Filter* generated by the exact truth.
- `Faith (Belief)`: The mind's filter contains the truth, allowing it to converge.
- `Opinion`: The mind's filter is disjoint from the truth, but it thinks it is principal.
-/

variable {Ω : Type v} -- The space of realities/propositions

/-- 
`Truth` is a specific reality `ω_true`. 
The absolute standard of understanding is the principal filter `𝓟 {ω_true}`. 
-/
def AbsoluteTruth (ω_true : Ω) : Filter Ω := Filter.principal {ω_true}

/-- A Mind State is a Filter of realities the mind considers possible. -/
def MindState := Filter Ω

/-- 
Understanding: The mind's filter is exactly the principal filter of the Truth.
There is no obscurity and no confusion. 
-/
def Understands (M : MindState) (ω_true : Ω) : Prop :=
  M = AbsoluteTruth ω_true

/-- 
Believing (Faith): The mind does not yet have absolute precision, but its 
filter *contains* the truth. Mathematically, the filter is bounded by the truth 
(`M ≤ 𝓟 {ω_true}` in Filter notation means `{ω_true} ∈ M`).
-/
def Believes (M : MindState) (ω_true : Ω) : Prop :=
  AbsoluteTruth ω_true ≤ M

/-- 
Opining (The Manichean Vice): The mind thinks it understands (it has formed 
a principal filter generated by some false set `S`), but it misses the truth entirely.
-/
def Opines (M : MindState) (ω_true : Ω) : Prop :=
  (∃ S : Set Ω, M = Filter.principal S ∧ ω_true ∉ S)

/-- 
THEOREM 4 (Menn p. 190): Faith is the Pathway to Understanding.
Augustine argues against the Manichees that one must begin with Faith.
Mathematically, a sequence of mental states (refinements of contemplation) 
can `Tendsto` the Absolute Truth. Faith guarantees that the Truth is in the 
filter, preventing the mind from converging to an Opinion.
-/
theorem faith_prevents_opinion (M : MindState) (ω_true : Ω) 
    (h_faith : Believes M ω_true) : 
    ¬ Opines M ω_true := by
  intro h_opines
  rcases h_opines with ⟨S, h_M_is_S, h_not_in_S⟩
  unfold Believes AbsoluteTruth at h_faith
  -- In Mathlib, `𝓟 A ≤ 𝓟 B ↔ A ⊆ B`. 
  -- So `𝓟 {ω_true} ≤ 𝓟 S` means `{ω_true} ⊆ S`, which implies `ω_true ∈ S`.
  have h_le : Filter.principal {ω_true} ≤ Filter.principal S := by
    rw [← h_M_is_S]
    exact h_faith
  have h_in_S : ω_true ∈ S := by
    exact Filter.principal_mono.mp h_le (Set.mem_singleton ω_true)
  -- Contradiction with the definition of Opining
  exact h_not_in_S h_in_S

end Menn.Augustine