import Mathlib

universe u

namespace Philosophy.Kant.Text.CPR

/--
The marks of a priori knowledge according to B3–B4:
1. Necessity (Not derived from contingent experience).
2. Strict Universality (No exception is allowed as possible).
-/
structure MarkOfApriority (J : Type u) where
  is_necessary : J → Prop
  is_universal : J → Prop

/--
IntroductionSystem: The canonical foundation of the Critique (B1–B30).
It defines the "partition of judgments" that sets the stage for the Deduction.
-/
structure IntroductionSystem where
  Judgment : Type u
  analytic : Judgment → Prop
  synthetic : Judgment → Prop
  apriori : Judgment → Prop
  aposteriori : Judgment → Prop

  -- The marks of the a priori (B3-B4)
  marks : MarkOfApriority Judgment

  -- AXIOM 1 (B3): "Necessity and strict universality are sure marks of a priori knowledge."
  apriori_iff_marks : ∀ j, apriori j ↔ (marks.is_necessary j ∧ marks.is_universal j)

  -- AXIOM 2 (B11): All a posteriori judgments are synthetic.
  aposteriori_is_synthetic : ∀ j, aposteriori j → synthetic j

  -- AXIOM 3 (B12): All analytic judgments are a priori.
  analytic_is_apriori : ∀ j, analytic j → apriori j

  -- AXIOM 4 (B10/11): The Exhaustive Partition.
  -- Every judgment is either analytic or synthetic.
  -- Note: We use Mathlib's `Xor'` for exclusive disjunction.
  partition : ∀ j, Xor' (analytic j) (synthetic j)

  -- AXIOM 5 (B2): Definition of a posteriori.
  aposteriori_not_apriori : ∀ j, aposteriori j ↔ ¬ apriori j

/--
The definition of the "Central Problem" (B19).
Synthetic a priori judgments are those where the predicate is not contained in the subject,
yet the judgment is valid independent of experience.
-/
def SyntheticAprioriJudgment (K : IntroductionSystem) (j : K.Judgment) : Prop :=
  K.synthetic j ∧ K.apriori j

/--
Kant's Fundamental Question (B19):
"The real problem of pure reason is contained in the question:
How are synthetic a priori judgments possible?"
-/
def HowAreSyntheticAprioriPossible (K : IntroductionSystem) : Prop :=
  ∃ j : K.Judgment, SyntheticAprioriJudgment K j

/--
Theorem: There are no analytic a posteriori judgments.
This confirms that the "logical space" defined by the system is consistent with B11-B12.
-/
theorem no_analytic_aposteriori (K : IntroductionSystem) (j : K.Judgment) :
    ¬(K.analytic j ∧ K.aposteriori j) := by
  intro ⟨h_an, h_post⟩
  -- From Axiom 3, analytic judgments are a priori
  have h_pri := K.analytic_is_apriori j h_an
  -- From Axiom 5, a posteriori judgments are NOT a priori
  have h_not_pri := (K.aposteriori_not_apriori j).mp h_post
  exact h_not_pri h_pri

end Philosophy.Kant.Text.CPR
