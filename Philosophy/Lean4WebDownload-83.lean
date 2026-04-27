import Mathlib.Order.Basic
import Mathlib.Logic.Basic

/-!
# Descartes and Augustine (Stephen Menn)
## Chapter 3: Plotinus

This module formalizes the conceptual vocabulary and theorems of Plotinian 
Platonism as reconstructed by Stephen Menn. It traces the logical necessity 
that forced Plotinus to posit a separate, incorporeal `Nous` (Intellect) 
that contains its own intelligible objects.
-/

namespace Menn.Chapter3

universe u

/-! 
### 1. Basic Ontology and Stoic Corporealism
Menn (pp. 89-94): The Stoics believed that everything is a body (`soma`). 
To explain active principles like the soul, they posited that the soul is 
just a body (pneuma) "somehow disposed" (`pôs echon`).
-/

/-- The baseline vocabulary for Hellenistic physics. -/
class PhysicsVocabulary (E : Type u) where
  IsBody : E → Prop
  IsIncorporeal : E → Prop
  IsActive : E → Prop
  IsPassive : E → Prop
  -- Definitionally, body and incorporeal are mutually exclusive.
  disjoint_body_incorporeal : ∀ x, IsBody x → ¬ IsIncorporeal x
  disjoint_active_passive : ∀ x, IsActive x → ¬ IsPassive x

/-- The Stoic paradigm: Only bodies exist. Active principles are just bodies. -/
class StoicPhysics (E : Type u) extends PhysicsVocabulary E where
  everything_is_body : ∀ x, IsBody x
  exists_active_body : ∃ x, IsBody x ∧ IsActive x

/-- 
The Stoic category of `pôs echon` (somehow disposed). 
A disposition is not a separate substance, but the base body in a certain state. 
-/
structure PosEchon (E : Type u) [PhysicsVocabulary E] where
  base : E
  is_body : IsBody base


/-! 
### 2. Platonist Ontology and the Defeat of the Stoics
Menn (pp. 108-109): Plotinus refutes the Stoic `pôs echon`. The Platonist core 
axiom is that matter (body) is strictly passive. Therefore, any active 
principle (like the soul) cannot be a body, no matter how it is disposed.
-/

class PlatonistOntology (E : Type u) extends PhysicsVocabulary E where
  /-- The fundamental Platonist axiom: All bodies are strictly passive. -/
  body_is_strictly_passive : ∀ x, IsBody x → IsPassive x

/-- 
THEOREM (Menn p. 108-109): Plotinus' Refutation of the Stoic Soul.
If the Platonist axiom holds, the Stoic active soul (a body pôs echon) 
is a logical contradiction. 
-/
theorem plotinus_refutes_stoic_soul {E : Type u} [PlatonistOntology E] 
    (s : PosEchon E) : ¬ IsActive s.base := by
  intro h_active
  -- 1. By definition, the base of the pôs echon is a body.
  have h_body : IsBody s.base := s.is_body
  -- 2. By the Platonist axiom, because it is a body, it is passive.
  have h_passive : IsPassive s.base := 
    PlatonistOntology.body_is_strictly_passive s.base h_body
  -- 3. By the basic physics vocabulary, it cannot be both active and passive.
  have h_not_active : ¬ IsActive s.base := 
    PhysicsVocabulary.disjoint_active_passive s.base h_passive
  -- 4. Contradiction.
  exact h_not_active h_active


/-! 
### 3. Aristotelian Dynamics (Actuality & Potentiality)
Menn (pp. 114-116): Plotinus borrows Aristotle's De Anima III.5 to construct 
the ascent. The core Aristotelian principle is the Priority of Actuality: 
a potentiality can only be actualized by a cause that is already essentially actual.
-/

/-- 
A parameterized class allowing us to talk about an entity `x` 
having a property `F` either potentially or actually. 
-/
class AristotelianDynamics (E : Type u) extends PlatonistOntology E where
  Potential : E → (E → Prop) → Prop
  Actual : E → (E → Prop) → Prop
  CausesActualization : E → E → Prop
  
  /-- 
  Priority of Actuality: If `x` transitions to actually having `F`, 
  there must exist some cause `y` which actually has `F` by its very essence 
  (i.e., it is NOT potentially `F`, it is purely actual). 
  -/
  priority_of_actuality : ∀ (x : E) (F : E → Prop),
    Potential x F → Actual x F → 
    ∃ (y : E), CausesActualization y x ∧ Actual y F ∧ ¬ Potential y F


/-! 
### 4. Plotinian Noetic (The Ascent to Nous)
Menn (pp. 116-118): Plotinus defines the Soul as *potential* Intellect (Nous). 
By applying the Aristotelian principle, Plotinus proves that a separate, 
purely actual Intellect (`Nous`) must exist.
-/

class PlotinianNoetic (E : Type u) extends AristotelianDynamics E where
  Rationality : E → Prop
  Knows : E → E → Prop
  IsExternalTo : E → E → Prop

  /-- Epistemological Dependence: If `x` knows `y` and `y` is external to `x`, 
      then `x`'s knowledge depends on `y`, meaning `x` is only *potentially* rational 
      (it requires external contact to actualize). -/
  external_knowledge_implies_potentiality : ∀ (x y : E),
    Knows x y → IsExternalTo y x → Potential x Rationality

/-- The Plotinian definition of Soul: It is potentially rational. -/
def IsSoul {E : Type u} [PlotinianNoetic E] (x : E) : Prop :=
  AristotelianDynamics.Potential x PlotinianNoetic.Rationality

/-- The Plotinian definition of Nous: It is essentially, purely actual rationality. -/
def IsNous {E : Type u} [PlotinianNoetic E] (x : E) : Prop :=
  AristotelianDynamics.Actual x PlotinianNoetic.Rationality ∧ 
  ¬ AristotelianDynamics.Potential x PlotinianNoetic.Rationality

/-- 
THEOREM (Menn p. 116): The Ascent to Nous.
Plotinus' proof that if a Soul becomes actually rational, there must exist 
a separate, prior, purely actual `Nous`.
-/
theorem ascent_to_nous {E : Type u} [PlotinianNoetic E] (s : E)
    (h_is_soul : IsSoul s)
    (h_becomes_rational : AristotelianDynamics.Actual s PlotinianNoetic.Rationality) :
    ∃ (n : E), IsNous n ∧ AristotelianDynamics.CausesActualization n s := by
  -- By the Priority of Actuality, there must exist a cause `y`...
  have h_cause := AristotelianDynamics.priority_of_actuality s PlotinianNoetic.Rationality h_is_soul h_becomes_rational
  rcases h_cause with ⟨n, h_causes, h_actual, h_not_potential⟩
  -- This cause exactly fulfills the definition of Nous.
  use n
  constructor
  · unfold IsNous
    exact ⟨h_actual, h_not_potential⟩
  · exact h_causes

/-- 
THEOREM (Menn p. 118): The Identity of Knower and Known.
Plotinus' radical departure from normal epistemology: 
Because `Nous` is purely actual, the Intelligibles (Forms/Objects of knowledge) 
cannot be external to `Nous`. "It is itself the things it thinks."
-/
theorem nous_contains_its_objects {E : Type u} [PlotinianNoetic E] (n x : E)
    (h_nous : IsNous n) 
    (h_knows : PlotinianNoetic.Knows n x) : 
    ¬ PlotinianNoetic.IsExternalTo x n := by
  intro h_external
  -- If x were external to n, then n would be potentially rational.
  have h_potential := PlotinianNoetic.external_knowledge_implies_potentiality n x h_knows h_external
  -- But Nous, by definition, is NOT potentially rational.
  have h_not_potential := h_nous.2
  -- Contradiction.
  exact h_not_potential h_potential

end Menn.Chapter3