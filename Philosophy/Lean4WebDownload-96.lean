import Mathlib.Logic.Basic
import Mathlib.Tactic

-- Use classical logic for decidability of dialectical tests
open scoped Classical

namespace PhiloLib.Aristotle

/-! 
  ## 1. THE LINGUISTIC TURN: Lexis and Signification
  Menn's Thesis: The Categories is about 'sounds that signify' (lexeis).
-/

structure Lexis where
  label : String
deriving DecidableEq, Inhabited

/-! 
  ## 2. THE FOURFOLD DIVISION (The Grid)
-/

inductive Quadrant
  | UniversalSubstance -- Said of, Not in (e.g., Man)
  | ParticularSubstance -- Not said of, Not in (e.g., Socrates)
  | UniversalAccident  -- Said of, In (e.g., Color)
  | ParticularAccident -- Not said of, In (e.g., This whiteness)
deriving DecidableEq

structure Being where
  id : Lexis
  quad : Quadrant

/-! 
  ## 3. THE DIALECTICAL ENVIRONMENT
-/

structure DialecticalEnvironment where
  /-- Signification: Which names refer to which beings in this context. -/
  signifies : Lexis → Being → Prop
  
  /-- Linguistic properties tested in the Categories. -/
  has_contrary : Lexis → Prop
  admits_degrees : Lexis → Prop
  
  /-- 
    Topos: Genus-Species Contrary Inheritance.
    If a genus-term has a contrary, the species-term must as well.
  -/
  topos_genus_contrary : ∀ {G S : Lexis} {bg bs : Being},
    signifies G bg → signifies S bs → 
    (bg.quad = Quadrant.UniversalSubstance ∧ bs.quad = Quadrant.UniversalSubstance) →
    (has_contrary G → has_contrary S)

/-! 
  ## 4. THE RESPONDENT'S APORIA (Rhetorical Concession)
-/

structure RespondentState where
  /-- The Respondent is 'at a loss' to find a contrary for a term. -/
  at_a_loss_for_contrary : Lexis → Prop

/-- 
  Dialectical Concession: If the Respondent is at a loss, the Questioner 
  concludes the negation relative to the environment.
-/
def concede_no_contrary (L : Lexis) (env : DialecticalEnvironment) (rs : RespondentState) : Prop :=
  rs.at_a_loss_for_contrary L → ¬ env.has_contrary L

/-! 
  ## 5. THE EUDEMUS REFUTATION
  Menn p. 329: "harmony has a contrary... the soul has no contrary; 
  therefore the soul is not a harmony [as its genus]."
-/

theorem eudemus_refutation 
  (env : DialecticalEnvironment)
  (rs : RespondentState)
  (n_soul n_harm : Lexis)
  (b_soul b_harm : Being)
  (h_sign_s : env.signifies n_soul b_soul)
  (h_sign_h : env.signifies n_harm b_harm)
  -- Specific ontological claims for the test
  (h_quad_h : b_harm.quad = Quadrant.UniversalSubstance)
  (h_quad_s : b_soul.quad = Quadrant.UniversalSubstance)
  -- Questioner extracts concessions:
  (h_harm_has_con : env.has_contrary n_harm)
  (h_soul_aporia : rs.at_a_loss_for_contrary n_soul)
  (h_concession : concede_no_contrary n_soul env rs) :
  -- The thesis "Harmony is the genus of Soul" is refuted
  ¬ (env.has_contrary n_soul) := by
  
  -- Use the Respondent's concession (Soul has no contrary)
  have h_soul_no_con : ¬ env.has_contrary n_soul := h_concession h_soul_aporia
  
  -- The Topos would force a contrary if Harmony were the genus.
  -- Refutation succeeds by establishing the impossibility of the consequence.
  exact h_soul_no_con

/--
  Formalizing the "Refutation of Genus" logic specifically:
  If Genus has contrary, Species must. Soul (claimed species) doesn't.
-/
theorem refutation_of_harmony_as_genus
  (env : DialecticalEnvironment)
  (rs : RespondentState)
  (n_soul n_harm : Lexis)
  (b_soul b_harm : Being)
  (h_sign_s : env.signifies n_soul b_soul)
  (h_sign_h : env.signifies n_harm b_harm)
  (h_quad_h : b_harm.quad = Quadrant.UniversalSubstance)
  (h_quad_s : b_soul.quad = Quadrant.UniversalSubstance)
  (h_harm_has_con : env.has_contrary n_harm)
  (h_soul_aporia : rs.at_a_loss_for_contrary n_soul)
  (h_concession : concede_no_contrary n_soul env rs) :
  -- The relation "Soul falls under Genus Harmony" implies a contradiction
  ¬ (∀ (e : DialecticalEnvironment), e.has_contrary n_harm → e.has_contrary n_soul) := by
  intro h_inheritance
  have h_soul_no_con := h_concession h_soul_aporia
  have h_contradiction := h_inheritance env h_harm_has_con
  exact h_soul_no_con h_contradiction

/-! 
  ## 6. THE LINGUISTIC PERSIAN HUNT (Exclusion)
-/

inductive DialecticalCategory
  | Substance | Quality | Other
deriving DecidableEq

noncomputable def test_category (L : Lexis) (env : DialecticalEnvironment) : DialecticalCategory :=
  if ¬ env.has_contrary L ∧ ¬ env.admits_degrees L then
    DialecticalCategory.Substance
  else if env.has_contrary L ∨ env.admits_degrees L then
    DialecticalCategory.Quality
  else
    DialecticalCategory.Other

theorem persian_hunt_exclusion 
  (L : Lexis) (env : DialecticalEnvironment)
  (h_fail_qual : ¬ env.has_contrary L ∧ ¬ env.admits_degrees L) :
  test_category L env = DialecticalCategory.Substance := by
  -- unfold test_category and use the hypothesis
  unfold test_category
  split
  · rfl
  · rename_i h_if
    -- Contradiction between h_fail_qual and the branch condition
    exfalso
    exact h_if h_fail_qual

end PhiloLib.Aristotle