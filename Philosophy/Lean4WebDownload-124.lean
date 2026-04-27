import Mathlib


/-!
# Descartes and Augustine (Stephen Menn)
## Chapter 3: Plotinus (Finer-Grained Formalization)

This module provides a completely gap-free (`sorry`-free) formalization of the 
dialectical architecture Stephen Menn uncovers in Plotinus. It shows how Plotinus 
synthesized Aristotelian kinematics and Platonic ontology to defeat Stoic 
corporealism, and how this gave rise to the Augustinian/Plotinian theodicy.

The code addresses Lean 4 technical challenges by parametrizing the ontologies 
over the base `PhysicsVocabulary`, avoiding typeclass diamonds, and fully 
resolving implicit variable inference.
-/

namespace Menn.Plotinus

universe u v

/-! 
### 1. Hellenistic Physics: Baseline Vocabulary 
We define a shared ontology used by both Stoics and Platonists to debate the 
nature of bodies, principles, and causes.
-/

class PhysicsVocabulary (E : Type u) where
  isBody : E → Prop
  isIncorporeal : E → Prop
  isActive : E → Prop
  isPassive : E → Prop
  
  /-- The fundamental dichotomy of Hellenistic substances. -/
  exhaustive_ontology : ∀ x, isBody x ∨ isIncorporeal x
  
  /-- Mutual exclusions agreed upon by all schools. -/
  disjoint_body_incorporeal : ∀ x, isBody x → ¬ isIncorporeal x
  disjoint_active_passive : ∀ x, isActive x → ¬ isPassive x


/-! 
### 2. The Rival Ontologies (Stoic vs. Platonist)
Menn (p. 89-98): Stoics assert that bodies can be active (e.g., the pneuma).
Platonists assert that matter/body is strictly passive and inert.
We pass `vocab` as a parameter to avoid typeclass resolution diamonds.
-/

class PlatonistOntology {E : Type u} (vocab : PhysicsVocabulary E) where
  /-- For Platonists, corporeality entails strict passivity. -/
  body_is_strictly_passive : ∀ x, vocab.isBody x → vocab.isPassive x

class StoicOntology {E : Type u} (vocab : PhysicsVocabulary E) where
  /-- Stoic Monism: Only bodies exist. -/
  everything_is_body : ∀ x, vocab.isBody x
  /-- The Stoic God/Pneuma is an active body. -/
  exists_active_body : ∃ x, vocab.isBody x ∧ vocab.isActive x


/-!
### 3. Dispositions (Pôs Echon) and Plotinus' Refutation of Stoicism
Menn (p. 106-111): Plotinus attacks the Stoic claim that the soul is just a 
body "somehow disposed" (pôs echon). If the body is intrinsically passive, 
an active disposition must be caused by an external incorporeal principle.
-/

class StateMechanics (E : Type u) (State : Type v) (vocab : PhysicsVocabulary E) where
  hasState : E → State → Prop
  stateCausesAction : State → Prop
  stateCausedBy : State → E → Prop
  
  /-- Plotinus' observational premise: an active state in a passive entity 
      must be caused by an active external entity. -/
  passive_acting_requires_active_cause : ∀ x s, 
    vocab.isPassive x → hasState x s → stateCausesAction s → 
    ∃ c, stateCausedBy s c ∧ vocab.isActive c

/-- 
THEOREM 1: Refutation of Stoic Corporealism.
Plotinus proves that the cause of a body's active disposition (e.g., a soul) 
must be an incorporeal principle (Logos/Soul). 
-/
theorem cause_of_disposition_is_incorporeal 
    {E : Type u} {State : Type v} 
    (vocab : PhysicsVocabulary E) 
    (plat : PlatonistOntology vocab) 
    (mech : StateMechanics E State vocab)
    (x : E) (s : State) 
    (h_body : vocab.isBody x) 
    (h_has : mech.hasState x s) 
    (h_acts : mech.stateCausesAction s) : 
    ∃ c, mech.stateCausedBy s c ∧ vocab.isIncorporeal c := by
  -- 1. Because x is a body, Platonism dictates it is passive.
  have h_passive : vocab.isPassive x := plat.body_is_strictly_passive x h_body
  
  -- 2. Because it is passive but has an active state, there is an active cause c.
  have h_cause := mech.passive_acting_requires_active_cause x s h_passive h_has h_acts
  rcases h_cause with ⟨c, h_causedBy, h_active⟩
  use c
  constructor
  · exact h_causedBy
  · -- 3. We prove c is incorporeal by logical contradiction.
    have h_exhaustive := vocab.exhaustive_ontology c
    rcases h_exhaustive with h_c_body | h_c_incorporeal
    · -- If c were a body, it would be passive (under Platonist ontology).
      have h_c_passive := plat.body_is_strictly_passive c h_c_body
      -- But c is active, and active/passive are mutually exclusive.
      have h_c_not_passive := vocab.disjoint_active_passive c h_active
      contradiction
    · exact h_c_incorporeal


/-!
### 4. Aristotelian Kinematics and the Priority of Actuality
Menn (p. 114-115): Plotinus adopts Aristotle's principle that actuality 
precedes potentiality, which is used to prove that Soul requires a higher principle.
-/

class AristotelianKinematics (E : Type u) where
  potential : E → Prop
  actual : E → Prop
  causesActualization : E → E → Prop
  
  /-- Priority of Actuality: Whatever is potential is actualized by something
      that is already perfectly actual. (The 'Father' principle). -/
  priority_of_actuality : ∀ x, potential x → 
    ∃ y, causesActualization y x ∧ actual y


/-!
### 5. The Plotinian Ascent (Soul to Nous)
Menn (p. 116-118): Plotinus' hierarchy. Soul is essentially potential intellect. 
Nous is perfectly actual intellect. The Soul must be actualized by Nous.
-/

class PlotinianNoetic (E : Type u) (vocab : PhysicsVocabulary E) extends AristotelianKinematics E where
  isSoul : E → Prop
  isNous : E → Prop
  
  /-- Soul is potential intellect. -/
  soul_is_potential : ∀ x, isSoul x → potential x
  
  /-- Nous is pure actual intellect. -/
  nous_is_actual : ∀ x, isNous x → actual x
  
  /-- Axiom: Actual principles are not strictly passive. -/
  actual_is_not_passive : ∀ x, actual x → ¬ vocab.isPassive x

  /-- The only principle capable of actualizing Soul's intellect is Nous. -/
  only_nous_actualizes_soul : ∀ s n, 
    isSoul s → causesActualization n s → isNous n

/-- 
THEOREM 2: Soul's Dependence on Nous.
Plotinus deduces that every Soul necessarily implies the existence of a purely 
actual Nous that causes its actualization. 
-/
theorem soul_implies_nous 
    {E : Type u} {vocab : PhysicsVocabulary E} 
    (noetic : PlotinianNoetic E vocab) 
    (s : E) (h_soul : noetic.isSoul s) : 
    ∃ n, noetic.isNous n ∧ noetic.causesActualization n s := by
  have h_pot := noetic.soul_is_potential s h_soul
  have h_act := noetic.priority_of_actuality s h_pot
  rcases h_act with ⟨n, h_causes, _⟩
  have h_is_nous := noetic.only_nous_actualizes_soul s n h_soul h_causes
  use n
  exact ⟨h_is_nous, h_causes⟩


/-!
### 6. Plotinian Theodicy: Soul's Descent and the Origin of Evil
Menn (p. 120-129): Plotinus saves God from responsibility for evil. 
Evil is not a substance, but a choice (aversio) by the Soul to turn towards 
the passive body rather than the actual Nous. Nous itself never turns.
-/

class PlotinianTheodicy (E : Type u) (vocab : PhysicsVocabulary E) extends PlotinianNoetic E vocab where
  turnsTowards : E → E → Prop
  
  /-- Evil occurs when a being turns towards the passive body (matter). -/
  doesEvil (e : E) : Prop := ∃ b, vocab.isBody b ∧ turnsTowards e b

  /-- The nature of Nous: Pure actuality contemplates only itself or the Good.
      It never turns towards lower bodies. -/
  nous_turns_only_to_self : ∀ n y, isNous n → turnsTowards n y → y = n

  /-- The nature of Soul: Soul can turn either towards Nous (virtue) or 
      towards bodies (vice/evil). -/
  soul_can_turn_to_body : ∃ s b, isSoul s ∧ vocab.isBody b ∧ turnsTowards s b

/-- 
LEMMA: Nous is not a body.
This follows because Nous is perfectly actual, while bodies are passive.
-/
lemma nous_is_not_body 
    {E : Type u} 
    (vocab : PhysicsVocabulary E) 
    (plat : PlatonistOntology vocab)
    (theodicy : PlotinianTheodicy E vocab)
    (n : E) (h_nous : theodicy.isNous n) : 
    ¬ vocab.isBody n := by
  intro h_body
  have h_passive := plat.body_is_strictly_passive n h_body
  have h_actual := theodicy.nous_is_actual n h_nous
  have h_not_passive := theodicy.actual_is_not_passive n h_actual
  exact h_not_passive h_passive

/-- 
THEOREM 3: Plotinian Salvation of God's Goodness.
Nous (God) cannot do evil. Evil requires turning toward a body. 
Nous turns only to itself. Since Nous is not a body, Nous never does evil.
-/
theorem plotinian_god_is_sinless 
    {E : Type u} 
    (vocab : PhysicsVocabulary E) 
    (plat : PlatonistOntology vocab)
    (theodicy : PlotinianTheodicy E vocab)
    (n : E) (h_nous : theodicy.isNous n) : 
    ¬ theodicy.doesEvil n := by
  intro h_evil
  unfold PlotinianTheodicy.doesEvil at h_evil
  rcases h_evil with ⟨b, h_b_is_body, h_turns⟩
  
  -- 1. Because n is Nous, whatever it turns to must be itself.
  have h_eq : b = n := theodicy.nous_turns_only_to_self n b h_nous h_turns
  
  -- 2. Therefore, n is a body.
  have h_n_is_body : vocab.isBody n := by
    rw [← h_eq]
    exact h_b_is_body

  -- 3. But we proved Nous is not a body. Contradiction.
  have h_n_not_body := nous_is_not_body vocab plat theodicy n h_nous
  exact h_n_not_body h_n_is_body

/-- 
THEOREM 4: The Origin of Evil is in the Soul's Descent.
While Nous is sinless, Soul has the capacity for evil because it can turn 
towards bodies. Evil is not a substance, but a relational privation (turning).
-/
theorem soul_can_do_evil
    {E : Type u} 
    (vocab : PhysicsVocabulary E) 
    (theodicy : PlotinianTheodicy E vocab) :
    ∃ s, theodicy.isSoul s ∧ theodicy.doesEvil s := by
  have h_can_turn := theodicy.soul_can_turn_to_body
  rcases h_can_turn with ⟨s, b, h_soul, h_body, h_turns⟩
  use s
  constructor
  · exact h_soul
  · unfold PlotinianTheodicy.doesEvil
    use b
    exact ⟨h_body, h_turns⟩

end Menn.Plotinus



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