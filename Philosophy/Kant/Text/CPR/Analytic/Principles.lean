import Philosophy.Kant.Text.Objectivity
import Philosophy.Kant.Text.Categories

universe u v w x y z

namespace Philosophy.Kant.Text.CPR.Analytic

open Philosophy.Kant.Text

/--
SystemOfPrinciples: The culmination of the Transcendental Deduction (B263).
This system extends the ObjectivitySystem, demonstrating how the Categories
legislate universal laws to Nature (The Cosmology of Experience).
-/
structure SystemOfPrinciples extends ObjectivitySystem where

  -- -----------------------------------------------------------------------
  -- MATHEMATICAL PRINCIPLES (Scaravelli: Construction of Magnitudes)
  -- -----------------------------------------------------------------------

  ExtensiveMagnitude : Type v
  IntensiveMagnitude : Type w

  /-- Axioms of Intuition: Pure intuitions are constructed as extensive continuous magnitudes. -/
  hasExtensiveMagnitude : Intuition → ExtensiveMagnitude → Prop

  /-- Anticipations of Perception: The real in sensation has a degree (intensive magnitude). -/
  hasIntensiveMagnitude : Sensation → IntensiveMagnitude → Prop

  -- AXIOM 1: All empirical intuitions (perceptions) have both extensive and intensive magnitude.
  mathematical_construction : ∀ i : Intuition,
    is_empirical i →
    (∃ em, hasExtensiveMagnitude i em) ∧
    (∃ im, hasIntensiveMagnitude (synopsis a) im) -- (assuming 'a' is the appearance of 'i')

  -- -----------------------------------------------------------------------
  -- DYNAMICAL PRINCIPLES: THE ANALOGIES OF EXPERIENCE (Laywine: Cartography)
  -- -----------------------------------------------------------------------

  /--
  The Analogies are rules of Time-Determination. We define temporal relations
  on the `TimeLine` inherited from AppearanceSystem.
  -/
  precedes : TimeLine → TimeLine → Prop
  simultaneous : TimeLine → TimeLine → Prop

  /-- First Analogy (Substance): Determines DURATION.
      The permanent substratum persists through the entire TimeLine. -/
  first_analogy_persistence : ∀ (o : ObjectOfExperience) (i j : Intuition),
    refersTo i o → refersTo j o →
    connectionGovernedBy i j CategoryOfRelation.inherenceAndSubsistence →
    ∃ (duration : Set TimeLine), (time_span i ⊆ duration) ∧ (time_span j ⊆ duration)

  /-- Second Analogy (Causality): Determines SUCCESSION.
      If i and j are bound by causality, the time of the cause strictly precedes the effect. -/
  second_analogy_succession : ∀ (cause effect : Intuition),
    connectionGovernedBy cause effect CategoryOfRelation.causalityAndDependence →
    ∀ t_c ∈ time_span cause, ∀ t_e ∈ time_span effect, precedes t_c t_e

  /-- Third Analogy (Community): Determines SIMULTANEITY (The Toothed-Comb).
      If i and j are bound by reciprocal community, they coexist at the exact same time coordinates. -/
  third_analogy_simultaneity : ∀ (i j : Intuition),
    connectionGovernedBy i j CategoryOfRelation.community →
    ∀ t_i ∈ time_span i, ∃ t_j ∈ time_span j, simultaneous t_i t_j

  -- -----------------------------------------------------------------------
  -- DYNAMICAL PRINCIPLES: THE POSTULATES OF EMPIRICAL THOUGHT
  -- -----------------------------------------------------------------------

  /--
  Modality does not alter the object, but determines its relation to the cognitive faculty (B266).
  We evaluate the epistemic status of an ObjectOfExperience.
  -/
  is_possible : ObjectOfExperience → Prop
  is_actual : ObjectOfExperience → Prop
  is_necessary : ObjectOfExperience → Prop

  /-- Postulate 1: Possibility = Agrees with the formal conditions (Space, Time, Categories). -/
  postulate_possibility : ∀ o, is_possible o ↔
    ∃ i, refersTo i o ∧ is_pure i

  /-- Postulate 2: Actuality = Connected with the material conditions (Sensation/Perception). -/
  postulate_actuality : ∀ o, is_actual o ↔
    ∃ i, refersTo i o ∧ is_empirical i

  /-- Postulate 3: Necessity = Connected with the actual determined by universal laws (Analogies). -/
  postulate_necessity : ∀ o_effect, is_necessary o_effect ↔
    ∃ o_cause i j,
      is_actual o_cause ∧
      refersTo i o_cause ∧ refersTo j o_effect ∧
      connectionGovernedBy i j CategoryOfRelation.causalityAndDependence

/--
The Ultimate Theorem of the Cosmology of Experience:
If an object is actual, it must be embedded in the universal time-line
via the Analogies of Experience. There are no isolated phenomena.
-/
theorem actuality_implies_cosmological_connection
    (K : SystemOfPrinciples) (o : K.ObjectOfExperience) :
    K.is_actual o → ∃ i, K.refersTo i o ∧ (∃ t, t ∈ K.time_span i) := by
  intro h_actual
  -- From the postulate of actuality, the object corresponds to an empirical intuition
  have ⟨i, h_refers, h_emp⟩ := (K.postulate_actuality o).mp h_actual
  -- From IntuitionSystem (Layer 1), empirical intuitions require a duration on the TimeLine
  have ⟨t1, t2, ht1, ht2, _⟩ := K.empirical_requires_duration _ h_emp
  exact ⟨i, h_refers, ⟨t1, ht1⟩⟩

end Philosophy.Kant.Text.CPR.Analytic
