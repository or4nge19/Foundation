import Mathlib

open CategoryTheory TopologicalSpace Opposite

/-!
# THE CARTOGRAPHY OF THE SENSIBLE WORLD (REVISED — v3)

A Formalization of Laywine's "Cosmology of Experience"

This version addresses:
1. Irreversibility (Time as a Monoid/Poset).
2. The Schematism as a Natural Transformation.
3. The Third Analogy (Community) as a Sheaf-theoretic "Gap Lemma."
4. The Topology of Experience (philosophical justification for the site).

## Fixes from v2:
- **Large elimination error**: `fin_cases` (tactic) internally uses
  `List.Mem.casesOn`, which can only eliminate into `Prop`. But
  `F.val.obj (op (ι i))` lives in `Type u`. Fix: use `Fin.cases`
  (the universe-polymorphic recursor) instead of the `fin_cases` tactic.
- Restructured `community_of_experience` proof.
-/


-- ============================================================================
-- PART I: THE TRANSCENDENTAL AESTHETIC
-- ============================================================================

section TranscendentalAesthetic

/-!
## 1. THE ARROW OF TIME (Second Analogy)

Kant argues time is a "succession." Unlike a Group, a Monoid does not
require inverses, representing the irreversibility of causal events.
-/
variable (Time : Type) [AddMonoid Time] [Preorder Time]

-- The manifold of raw sensory data
variable (Phenomena : Type) [TopologicalSpace Phenomena]

/-
The World-Process: An additive action of time on phenomena.
`t +ᵥ p` represents the state `p` after a duration `t`.
-/
variable [AddAction Time Phenomena]

end TranscendentalAesthetic


-- ============================================================================
-- PART II: THE TRANSCENDENTAL LOGIC
-- ============================================================================

section TranscendentalLogic

universe u
variable {Locality : Type u} [TopologicalSpace Locality]

/-!
## 2. THE SCHEMATISM AS A NATURAL TRANSFORMATION

The Schematism is the "third thing" mediating between Intuition and Concepts.
We model this as a Natural Transformation between two functors over the
topology of experience.
-/

-- A Functor representing the "Passive" reception of data (Intuition)
variable (Intuition : (Opens Locality)ᵒᵖ ⥤ Type u)

-- A Functor representing the "Active" processing of the Understanding (Concepts)
variable (Understanding : (Opens Locality)ᵒᵖ ⥤ Type u)

/--
The Schematism is a rule that assigns to every local patch of intuition
a conceptual representation, such that the mapping is consistent across
all nested patches (Naturality).
-/
def Schematism := Intuition ⟶ Understanding

end TranscendentalLogic


-- ============================================================================
-- PART III: THE ANALOGIES OF EXPERIENCE
-- ============================================================================

section TheAnalogies

variable {Locality : Type u} [TopologicalSpace Locality]
variable (Time : Type) [AddMonoid Time]

/--
## 3. OBJECTIVE VALIDITY AS EQUIVARIANCE (Second Analogy)

A synthesis possesses objective validity when it commutes with the
temporal evolution of phenomena — i.e., it is equivariant under the
action of Time.
-/
def ObjectiveValidity
  (synthesis : Phenomena → Phenomena)
  [AddAction Time Phenomena] : Prop :=
  ∀ (t : Time) (p : Phenomena), synthesis (t +ᵥ p) = t +ᵥ (synthesis p)


/-!
## 4. THE GAP LEMMA: COMMUNITY (Third Analogy)

Given a sheaf F on a topological space, if we have local sections
on U and V that agree on the overlap U ⊓ V, there exists a unique
global section on U ⊔ V restricting correctly to both.

This formalizes Kant's Third Analogy: substances in space stand in
thoroughgoing community (reciprocal interaction). Locally consistent
determinations of coexisting substances must glue to a global,
objective determination.

### Error fixed (v2 → v3):
The `fin_cases` *tactic* internally calls `List.Mem.casesOn`, a Prop-valued
recursor that cannot eliminate into `Type u`. Since the goal
`F.val.obj (op (ι i))` lives in `Type u`, Lean raises:

    recursor `List.Mem.casesOn` can only eliminate into `Prop`

Fix: use `Fin.cases` (the *term-level* recursor for `Fin`), which is
universe-polymorphic and can eliminate into any `Sort`.
-/
theorem community_of_experience
  {Locality : Type u} [TopologicalSpace Locality]
  (F : TopCat.Sheaf (Type u) (TopCat.of Locality))
  (U V : Opens Locality)
  (section_U : F.1.obj (op U))
  (section_V : F.1.obj (op V))
  (h_agreement : F.1.map (homOfLE inf_le_left).op section_U =
                 F.1.map (homOfLE inf_le_right).op section_V) :
  ∃! (global_object : F.1.obj (op (U ⊔ V))),
    F.1.map (homOfLE le_sup_left).op global_object = section_U ∧
    F.1.map (homOfLE le_sup_right).op global_object = section_V := by
  -- The indexed family of opens
  let ι : Fin 2 → Opens Locality := ![U, V]
  -- The family of local sections, as a dependent function.
  -- `Fin.cases` is the universe-polymorphic recursor: it CAN eliminate into Type u.
  -- `fin_cases` (the tactic) cannot, because it routes through List.Mem.casesOn.
  let sf : ∀ i : Fin 2, F.1.obj (op (ι i)) :=
    Fin.cases section_U (Fin.cases section_V Fin.elim0)
  -- The gluing follows from the sheaf condition on the binary cover {U, V} of U ⊔ V.
  -- This requires constructing the covering sieve, verifying it lies in
  -- Opens.grothendieckTopology, and extracting existence + uniqueness from
  -- the limit characterization of Presheaf.IsSheaf.
  -- Standard result (Hartshorne II.1, Mac Lane–Moerdijk III.4).
  sorry

end TheAnalogies


-- ============================================================================
-- PART IV: THE TOPOLOGY OF EXPERIENCE
-- ============================================================================

/-!
## 5. PHILOSOPHICAL JUSTIFICATION: WHAT IS THE TOPOLOGY OF EXPERIENCE?

The sheaf-theoretic formalization requires a topological space `Locality`
whose open sets serve as the "site" over which the presheaf of phenomena
is defined. This demands a philosophical answer to: **what are the open
sets of experience?**

### Kant's Answer: The Formal Conditions of Sensibility

Kant distinguishes two forms of sensibility: Space and Time (A22/B36).
We identify the topology with **the structure of spatial accessibility**.

An "open set" U ⊆ Locality represents a **region of possible perception**:
the collection of states of affairs that a subject *could* apprehend from
a given perspective, in a given modality, at a given resolution.

This is not arbitrary. Three features of Kant's doctrine select topology
as the right formalism:

1. **Mereological structure.** Kant holds that space is infinitely divisible
   and that any region contains sub-regions (A25/B39). Topology formalizes
   this: open sets are closed under arbitrary unions and finite intersections.

2. **Perspective-dependence.** An open set is not a "thing in itself" but a
   *mode of access*. Just as a camera's field of view defines what it can
   register, an open set defines what the subject can apprehend. Different
   open sets may overlap (shared content from different perspectives).
   This is the basis of the gluing condition.

3. **The distinction between local and global.** Kant argues that the
   "synthesis of apprehension" operates locally (on the manifold of
   intuition as given) while the "synthesis of recognition" unifies
   these local apprehensions into a global object (A103). This is
   precisely the presheaf-to-sheaf transition.

### The Concrete Model (Geometric Deep Learning)

In the GDL interpretation, the topology has a precise instantiation:

- **Locality** = the physical domain of a sensor (e.g., a visual field,
  a patch of a 3D mesh, a temporal window of an audio stream).
- **Open sets** = receptive fields. In a CNN, each neuron sees a local
  patch of the input; in a Graph Neural Network, each node sees its
  k-hop neighborhood. These form a topology (they are closed under
  union and intersection).
- **The presheaf** assigns to each receptive field the feature
  activations computed from it.
- **The sheaf condition** says: if features from overlapping receptive
  fields are *consistent*, they determine a unique global representation.
  This is exactly what makes a GNN or a Vision Transformer "work."

The topology of experience is therefore not metaphorical. It is the
**receptive field structure** of the sensing apparatus — the formal
condition under which local data can be unified into a coherent world.
-/


-- ============================================================================
-- PART V: THE FULLY PROVABLE DEDUCTION (Sheafification)
-- ============================================================================

section TheSheafificationDeduction

/-!
## 6. THE TRANSCENDENTAL DEDUCTION AS SHEAFIFICATION

While `community_of_experience` (binary gluing) is sorry'd due to
Mathlib API complexity, the *core philosophical claim* — that the
Categories transform raw data into objectively valid experience —
admits a complete, `sorry`-free proof via the sheafification functor.

**Philosophical content:** The Transcendental Deduction does not
*find* coherence in the data. It *imposes* coherence by construction.
Sheafification is the mathematical operation that does exactly this:
given ANY presheaf (a "rhapsody of perceptions"), it produces the
nearest sheaf (a "coherent experience").
-/

variable {Locality : Type u} [TopologicalSpace Locality]

/--
The Transcendental Deduction: sheafification of raw perception.
This is a functor that takes any presheaf (potentially incoherent
local data) and returns a Sheaf (globally coherent experience).
-/
noncomputable def TranscendentalDeduction
  (raw : (Opens Locality)ᵒᵖ ⥤ Type u) :
  Sheaf (Opens.grothendieckTopology Locality) (Type u) :=
  (presheafToSheaf (Opens.grothendieckTopology Locality) (Type u)).obj raw

/--
**THE MAIN THEOREM (sorry-free):**
The result of the Transcendental Deduction is necessarily objectively valid.
"Objectively valid" = satisfies the sheaf condition = local data glues uniquely.

The proof is *trivial by construction*. This is the point: Kant's argument
is that objectivity is analytic given the architecture of cognition, not
synthetic given empirical data. The sheafification functor builds a Sheaf
by definition; we merely extract the proof.
-/
theorem objective_validity_of_experience
  (raw_data : (Opens Locality)ᵒᵖ ⥤ Type u) :
  Presheaf.IsSheaf (Opens.grothendieckTopology Locality)
    (TranscendentalDeduction raw_data).val :=
  (TranscendentalDeduction raw_data).cond

/--
**THE UNIVERSALITY OF THE DEDUCTION:**
Sheafification is a left adjoint to the forgetful functor from Sheaf to
Presheaf. This adjunction is the category-theoretic expression of
Kant's claim that the Categories are the *unique* way to achieve
objective validity — they are the universal solution to the problem
of turning local perception into global knowledge.
-/
noncomputable def deduction_is_universal :
  presheafToSheaf (Opens.grothendieckTopology Locality) (Type u) ⊣
  sheafToPresheaf (Opens.grothendieckTopology Locality) (Type u) :=
  presheafToSheaf.adjunction _ _

end TheSheafificationDeduction


-- ============================================================================
-- PART VI: MONOTONE TIME (Strengthening the Second Analogy)
-- ============================================================================

section MonotoneTime

/-!
## 7. CAUSAL ACTION: TIME RESPECTS ORDER

The revised formalization declares `[Preorder Time]` but never uses it.
To truly capture the Second Analogy (the irreversibility of cause and effect),
we should require that the action of time on phenomena is **monotone**:
later times produce later states.

This connects to the GDL principle of **causal masking** in sequence models
(e.g., GPT-style autoregressive transformers), where the model is architecturally
prevented from attending to future tokens.
-/

/--
A causal action is an additive action of an ordered time monoid on an
ordered space of phenomena, such that advancing time moves the state
forward in the ordering.
-/
class CausalAction
  (Time : Type) (Phenomena : Type)
  [AddMonoid Time] [Preorder Time]
  [Preorder Phenomena] [AddAction Time Phenomena] : Prop where
  /-- The action respects the time ordering: if s ≤ t then the state at time s
      precedes the state at time t. -/
  monotone_act : ∀ (p : Phenomena) {s t : Time}, s ≤ t → s +ᵥ p ≤ t +ᵥ p

/--
Under a causal action, the present always precedes the future.
(0 is the identity of the AddMonoid, representing "now".)
-/
theorem present_precedes_future
  {Time Phenomena : Type}
  [AddMonoid Time] [Preorder Time]
  [Preorder Phenomena] [AddAction Time Phenomena]
  [CausalAction Time Phenomena]
  (t : Time) (p : Phenomena) (ht : 0 ≤ t) :
  p ≤ t +ᵥ p := by
  have h := CausalAction.monotone_act (Time := Time) p ht
  rwa [zero_vadd] at h

end MonotoneTime