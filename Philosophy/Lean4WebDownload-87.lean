import Mathlib

/-!
# Descartes and Augustine (Stephen Menn)
## Chapter 3: Plotinus (Custom Foundation: Mereology & Causality)

This module builds a historically faithful foundational logic for Hellenistic 
and late-antique philosophy. It defines:
1. Strict Mereology (to define extension/corporeality).
2. Per Se vs Per Accidens causality.
3. Ontological dependence (Grades of Being).
-/

namespace Menn.Plotinus.CustomLogic

universe u

/-!
### 1. Hellenistic Mereology: Extension and Corporeality
Instead of assuming a topological space, we define what it means to be a "Body" 
strictly through mereological part-whole relations. A body is an extended substance, 
meaning it has proper parts. An incorporeal principle is unextended.
-/

class HellenisticMereology (Substance : Type u) where
  partOf : Substance → Substance → Prop
  
  -- Axioms of a partial order for parthood
  refl : ∀ x, partOf x x
  trans : ∀ x y z, partOf x y → partOf y z → partOf x z
  antisymm : ∀ x y, partOf x y → partOf y x → x = y

  /-- x is a proper part of y if it is a part of y but not identical to y -/
  properPart (x y : Substance) : Prop := partOf x y ∧ x ≠ y

  /-- A substance is extended (corporeal) if it has proper parts. -/
  isExtended (x : Substance) : Prop := ∃ p, properPart p x

  /-- A substance is unextended (incorporeal) if it has no proper parts. -/
  isUnextended (x : Substance) : Prop := ∀ p, ¬ properPart p x


/-!
### 2. Causality: Per Se vs. Per Accidens
Aristotle and Plotinus distinguish between an accidental chain of temporal 
causes (which can go to infinity, like fathers and sons) and an essential 
chain of ontological dependence (which cannot).
-/



class AristotelianCausality (Substance : Type u) extends HellenisticMereology Substance where
  causesPerAccidens : Substance → Substance → Prop -- Temporal causality
  causesPerSe : Substance → Substance → Prop       -- Ontological dependence
  
  -- Per Se causality is strictly asymmetric and transitive
  per_se_asymm : ∀ x y, causesPerSe x y → ¬ causesPerSe y x
  per_se_trans : ∀ x y z, causesPerSe x y → causesPerSe y z → causesPerSe x z

  /-- A First Principle (like Nous) has no prior per se cause. -/
  isFirstPrinciple (x : Substance) : Prop := ∀ y, ¬ causesPerSe y x


/-!
### 3. Plotinian Ontology vs. Stoic Monism
We now define the properties of bodies and principles. The Stoics argue that 
active principles (like the soul) are extended bodies. Plotinus counters that 
matter is purely passive; therefore, if a body acts, its *per se* cause must 
be unextended.
-/

class PlotinianOntology (Substance : Type u) extends AristotelianCausality Substance where
  isPassive : Substance → Prop
  isActive : Substance → Prop

  /-- Disjointness of active and passive (shared premise). -/
  active_not_passive : ∀ x, isActive x → ¬ isPassive x

  /-- Platonist Premise 1: All extended substances (bodies) are purely passive. -/
  extended_is_passive : ∀ x, isExtended x → isPassive x

  /-- Platonist Premise 2: Any proper part of an extended substance is also extended. 
      (Matter is infinitely divisible into matter). -/
  parts_are_extended : ∀ p x, isExtended x → properPart p x → isExtended p

  /-- Observational Premise: If a substance acts, it requires a strictly active `per se` cause. -/
  action_requires_active_cause : ∀ x, isActive x → ∃ c, causesPerSe c x ∧ isActive c


/-!
### 4. The Grand Refutation of the Stoics
Menn (p. 108-111): Plotinus proves that the Stoic *pôs echon* (a body disposed 
to act) is a contradiction. If a body acts, its essential cause cannot be a body 
(nor a part of a body), because all bodies and parts of bodies are passive. 
Therefore, the true cause of the action is an unextended (incorporeal) principle.
-/

/-- 
THEOREM 1: The Principle of Action is Unextended (Incorporeal).
If an extended body exhibits action, the `per se` cause of that action 
must be an entirely unextended substance.
-/
theorem active_principle_is_unextended 
    {Substance : Type u} 
    [ontology : PlotinianOntology Substance] 
    (body : Substance) 
    (h_ext : ontology.isExtended body) 
    (h_acts : ontology.isActive body) : 
    ∃ c, ontology.causesPerSe c body ∧ ontology.isUnextended c := by
  
  -- 1. Because the body acts, it requires an active per se cause (c).
  have h_cause_exists := ontology.action_requires_active_cause body h_acts
  rcases h_cause_exists with ⟨c, h_caused_by, h_c_active⟩
  
  use c
  constructor
  · exact h_caused_by
  · -- 2. We prove c is unextended by contradiction.
    intro h_c_extended
    unfold PlotinianOntology.isUnextended
    
    -- Assume c is extended.
    by_contra h_c_not_unextended
    -- In Lean, `¬(∀ p, ¬ P p)` is classically equivalent to `∃ p, P p`, 
    -- but we can prove it directly from our definitions: 
    -- If it is not unextended, it must be extended.
    have h_c_is_ext : ontology.isExtended c := by
      -- Unfold the logic of extension. If ¬(∀ p, ¬ properPart p c), 
      -- then it has proper parts, meaning it is extended.
      unfold HellenisticMereology.isExtended
      push_neg at h_c_not_unextended
      exact h_c_not_unextended

    -- 3. If c is extended, Platonism dictates it must be passive.
    have h_c_passive := ontology.extended_is_passive c h_c_is_ext

    -- 4. But c is active (it is the active cause).
    have h_not_passive := ontology.active_not_passive c h_c_active

    -- 5. Contradiction.
    exact h_not_passive h_c_passive


/-!
### 5. The Hypostases: Grades of Being


Menn (p. 118): Because Nous is the first principle, it cannot be caused `per se`. 
Therefore, Nous cannot be a body.
-/

class Hypostases (Substance : Type u) extends PlotinianOntology Substance where
  isNous : Substance → Prop
  isSoul : Substance → Prop

  /-- Nous is defined as the First Principle (the Uncaused Cause in the Per Se order). -/
  nous_is_first_principle : ∀ n, isNous n → isFirstPrinciple n

  /-- Axiom: Every active principle is either Nous, or has Nous as its ultimate Per Se cause. -/
  nous_is_ultimate_act : ∀ c, isActive c → ∃ n, isNous n ∧ (n = c ∨ causesPerSe n c)


/-- 
THEOREM 2: Nous is Incorporeal.
Because Nous is a first principle, it cannot be extended (a body). If Nous were 
extended, it would be passive, requiring an active prior cause, contradicting 
its status as a first principle.
-/
theorem nous_is_unextended
    {Substance : Type u} 
    [hyp : Hypostases Substance] 
    (n : Substance) 
    (h_nous : hyp.isNous n) 
    (h_active : hyp.isActive n) : 
    hyp.isUnextended n := by
  
  -- Assume Nous is extended to derive a contradiction.
  by_contra h_n_not_unextended
  have h_n_ext : hyp.isExtended n := by
    unfold HellenisticMereology.isExtended
    push_neg at h_n_not_unextended
    exact h_n_not_unextended

  -- If Nous is extended, it is passive.
  have h_n_passive := hyp.extended_is_passive n h_n_ext
  
  -- But we know Nous is active. This is a contradiction.
  have h_not_passive := hyp.active_not_passive n h_active
  exact h_not_passive h_n_passive

end Menn.Plotinus.CustomLogic