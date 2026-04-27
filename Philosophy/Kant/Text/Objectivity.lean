import Philosophy.Kant.Text.Apperception

universe u v w x y z

namespace Philosophy.Kant.Text

/--
ObjectivitySystem: Formalizes B137 and A104.
An object is NOT a disconnected thing-in-itself. It is the correlate
of the necessary unity of the manifold.
-/
structure ObjectivitySystem extends SynthesisSystem where
  ObjectOfExperience : Type z
  refersTo : Intuition → ObjectOfExperience → Prop

  -- Laywine's Anti-Aporetic Axiom (A104-105):
  -- "Outside our knowledge, we have nothing that we could set over and against it."
  -- Objective reference is strictly constrained by lawful, categorical connection.
  -- If two intuitions refer to the same object, their combination must be governed by a category.
  reference_requires_lawful_connection : ∀ i j o,
    refersTo i o → refersTo j o →
    combineInOneConsciousness i j → ∃ c, connectionGovernedBy i j c

/-- Objective validity is the successful reference to an object of possible experience. -/
def ObjectivelyValid (K : ObjectivitySystem) (i : K.Intuition) : Prop :=
  ∃ o, K.refersTo i o

/--
The bridge from the "I think" to the Object (B137):
"The unity of consciousness is that which alone constitutes the relation
of representations to an object, therewith their objective validity."
-/
def ReferenceFromUnity (K : ObjectivitySystem) : Prop :=
  ∀ i, UnifiedInOneConsciousness K.toSynthesisSystem i → ObjectivelyValid K i

/--
Conditions of Possible Experience (B161).
The three pillars of the B-Deduction's conclusion.
-/
def ConditionOfPossibleExperience (K : ObjectivitySystem) : Prop :=
  UnityOfApperception K.toSynthesisSystem ∧
  LawfulSynthesis K.toSynthesisSystem ∧
  ReferenceFromUnity K

/--
The Flagship Theorem of Layer 1 (The Kernel Deduction).
If the mind satisfies the conditions of possible experience (i.e., it is a
lawful legislator of the sensible world), then its synthesis guarantees Objective Validity.
-/
theorem lawful_synthesis_yields_objective_validity
    (K : ObjectivitySystem)
    (h_cond : ConditionOfPossibleExperience K)
    (i : K.Intuition) :
    ObjectivelyValid K i := by
  -- 1. Extract the fact that the system is a Lawful Synthesis
  have h_lawful : LawfulSynthesis K.toSynthesisSystem := h_cond.2.1
  -- 2. Prove that Lawful Synthesis guarantees the Transcendental Unity of Apperception
  have h_unity : UnityOfApperception K.toSynthesisSystem :=
    lawful_synthesis_preserves_unified_consciousness h_lawful
  -- 3. Apply the ReferenceFromUnity bridge to deduce Objective Validity
  have h_bridge : ReferenceFromUnity K := h_cond.2.2
  exact h_bridge i (h_unity i)

end Philosophy.Kant.Text
