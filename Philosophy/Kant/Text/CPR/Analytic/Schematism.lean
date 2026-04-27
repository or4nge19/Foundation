import Philosophy.Kant.Text.Categories
import Philosophy.Kant.Text.Intuition

universe u v w x y

namespace Philosophy.Kant.Text.CPR.Analytic

open Philosophy.Kant.Text

/--
SchematismSystem: Formalizes the "Transcendental Doctrine of Judgment" (A137/B176).
It extends FullCategorySystem to show HOW the categories are applied to
the sensible manifold via the Productive Imagination.
-/
structure SchematismSystem extends FullCategorySystem where

  /--
  A TimeDetermination is not an opaque type, but a structural rule applied to the
  'TimeLine' (inherited from our foundational AppearanceSystem).
  It represents the cartographic geometry of time (e.g., duration, succession).
  -/
  TimeDetermination := TimeLine → Prop

  /--
  The Transcendental Schema (A140/B179):
  "The representation of a universal procedure of the imagination."
  It maps a Category to a specific TimeDetermination rule.
  -/
  schemaOfRelation : CategoryOfRelation → TimeDetermination

  /--
  HOMOGENEITY 1 (Sensible Homogeneity):
  The schema is fundamentally temporal. It applies directly to the TimeLine,
  which is the formal a priori condition of all appearances.
  -/
  sensible_homogeneity : ∀ (c : CategoryOfRelation),
    ∃ (t : TimeLine), schemaOfRelation c t

  /--
  HOMOGENEITY 2 (Intellectual Homogeneity):
  The schema is a universal rule that governs how the category synthesizes intuitions.
  If two intuitions are connected by a category, the time-spans of those intuitions
  MUST satisfy the schema's temporal rule.
  -/
  intellectual_homogeneity : ∀ (c : CategoryOfRelation) (i j : Intuition),
    connectionGovernedBy i j c →
    ∀ t_i ∈ time_span i, schemaOfRelation c t_i

  /--
  Scaravelli/Laywine Concrete Expositio (A144/B183).
  The Schema of Substance is the persistence of the real in time.
  It is a time-determination that holds for ALL time (duration).
  -/
  schema_of_substance_is_persistence :
    schemaOfRelation CategoryOfRelation.inherenceAndSubsistence = (fun _ => True)

/--
The Mediation Theorem (A138/B177).
Because the schema is both a temporal determination (Sensible) and a universal
rule governing connection (Intellectual), it successfully mediates the application
of the pure Category to the empirical Intuition.

This replaces the trivial 'rfl' proof with a rigorous logical deduction.
-/
theorem schema_enables_objective_subsumption
    (K : SchematismSystem)
    (c : CategoryOfRelation)
    (i j : K.Intuition)
    (h_conn : K.connectionGovernedBy i j c)
    (h_emp_i : K.is_empirical i) :
    ∃ (t : K.TimeLine), K.schemaOfRelation c t := by

  -- 1. From IntuitionSystem: An empirical intuition must occupy a duration of time.
  have ⟨t_i, _, h_in_span, _, _⟩ := K.empirical_requires_duration _ h_emp_i

  -- 2. From Intellectual Homogeneity: The categorical connection forces the intuition's
  -- time-span to conform to the Category's Schema.
  have h_schema_applies := K.intellectual_homogeneity c i j h_conn t_i h_in_span

  -- 3. Therefore, the Schema successfully determines a point in Sensible Time.
  exact ⟨t_i, h_schema_applies⟩

end Philosophy.Kant.Text.CPR.Analytic
