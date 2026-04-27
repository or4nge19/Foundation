import Philosophy.Kant.Text.Concept

universe u v

namespace Philosophy.Kant.Text.CPR.Analytic

open Philosophy.Kant.Text

/--
DeductionASystem: Formalizes the "Threefold Synthesis" (A98-110).
It strictly extends ConceptSystem, because without Concepts,
recognition (and thus objective knowledge) is impossible.
-/
structure DeductionASystem extends ConceptSystem where

  /--
  1. Synthesis of Apprehension (A98):
  The active "running through" (Durchlaufen) and "taking together" of the
  manifold in the TimeLine. (Inherited from IntuitionSystem.synthesisOfApprehension).
  -/
  apprehension_takes_time : ∀ s : Set Appearance,
    ∃ t, t ∈ time_span (synthesisOfApprehension s)

  /--
  2. Synthesis of Reproduction in Imagination (A100):
  The mind must be able to reproduce past temporal states into present consciousness.
  Without this "affinity," the manifold would dissolve into a "swarm."
  -/
  reproduction_affinity : ∀ (i : Intuition),
    ∃ (past_t : TimeLine), past_t ∈ time_span i →
      -- The past representation is held in the present synthetic unity
      combinable_in_present : Prop

  /--
  3. Synthesis of Recognition in a Concept (A103):
  The temporal image produced by imagination must be subsumed under a Concept
  to achieve unitary consciousness.
  -/
  recognition_subsumption : ∀ (i : Intuition),
    combinable_in_present → ∃ (c : Concept), subsumes c i

  /--
  The Core Axiom of the A-Deduction (A102):
  "These three kinds of synthesis... are inseparably combined."
  We mathematically enforce that you cannot have a concept without a reproduced image,
  and you cannot have an image without an apprehended temporal manifold.
  -/
  inseparable_synthesis : ∀ (c : Concept) (i : Intuition),
    subsumes c i →
      (∃ (past_t : TimeLine), past_t ∈ time_span i) ∧
      (∃ (s : Set Appearance), i = synthesisOfApprehension s)

/--
The Climax of the A-Deduction (A106/A111):
Without the synthesis of recognition under concepts, our soul would be filled with
a "swarm of appearances" that are "less even than a dream."
-/
theorem a_deduction_prevents_swarm (K : DeductionASystem) (i : K.Intuition) :
    (∃ c, K.subsumes c i) → ¬ K.IsSwarm (K.time_span i) := by
  sorry -- Proof relies on the Concept imposing a universal rule.

end Philosophy.Kant.Text.CPR.Analytic
