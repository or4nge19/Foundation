import Mathlib.Logic.Basic
import Mathlib.Tactic

open scoped Classical

namespace PhiloLib.Aristotle

/-! 
  ## 1. LEXICAL LINGUISTICS: Figure of Speech
  Menn p. 11: Sophisms arise when the *form* of an expression masks its *category*.
-/

inductive GrammaticalForm
  | ActiveVerb  -- e.g., "to see" (looks like Action)
  | PassiveVerb -- e.g., "to be cut"
  | Noun        -- e.g., "Socrates"
  | Adjective   -- e.g., "White" (Paronymous form)
deriving DecidableEq, Inhabited

structure Lexis where
  label : String
  form  : GrammaticalForm
deriving DecidableEq, Inhabited

inductive Category
  | Substance | Quality | Quantity | Relation | Action | Passion
deriving DecidableEq, Inhabited

/-! 
  ## 2. LOGOS AND SYNONYMY
  Menn p. 13: Synonymy is the requirement that the Name and Definition 
  are both predicated of the subject.
-/

structure Logos where
  definition : String
deriving DecidableEq, Inhabited

structure DialecticalContext where
  signifies : Lexis → Category → Logos → Prop

/-- 
  Menn p. 13: Synonymy check. 
  Two terms are synonymous if they refer to the same definition (logos). 
-/
def is_synonym (ctx : DialecticalContext) (L1 L2 : Lexis) : Prop := 
  ∃ c1 c2 l, ctx.signifies L1 c1 l ∧ ctx.signifies L2 c2 l

/-! 
  ## 3. THE REFINED PREDICATION MATRIX
  Menn's distinction between Synonymy (Genus) and Paronymy (Accident).
-/

structure DialecticalEnvironment extends DialecticalContext where
  /-- Synonymous Predication: The Name and Definition both apply. -/
  said_of_synonymously : Lexis → Lexis → Prop
  
  /-- 
    Paronymous Predication: The Name is derived from a quality, 
    but the definition of that quality does not apply to the subject. 
  -/
  predicated_paronymously : Lexis → Lexis → Prop

  /-- AXIOM: Genus must be synonymous (Menn p. 13). -/
  genus_is_synonymous : ∀ {G S : Lexis}, 
    said_of_synonymously G S → is_synonym toDialecticalContext G S

/-- 
  THEOREM: Refutation via Paronymy (Menn p. 12-13).
  A paronym (like 'white') cannot be a genus because it fails synonymy.
-/
theorem paronymy_excludes_genus 
  (env : DialecticalEnvironment) (X Y : Lexis) 
  (h_paron : env.predicated_paronymously X Y)
  (h_not_syn : ¬ is_synonym env.toDialecticalContext X Y) :
  ¬ (env.said_of_synonymously X Y) := by
  intro h_said
  -- If it were said synonymously, it would be a synonym (by the Genus Axiom)
  have h_syn := env.genus_is_synonymous h_said
  -- But we conceded it is not a synonym (the hallmark of paronymy)
  exact h_not_syn h_syn

/-! 
  ## 4. SOLVING SOPHISMS: Figure of Speech
  Menn p. 11: "Seeing" is a Passion, but we speak of it as an Action.
-/

def is_figure_of_speech (L : Lexis) (cat : Category) : Prop :=
  (L.form = GrammaticalForm.ActiveVerb ∧ cat ≠ Category.Action)

theorem solve_seeing_sophism 
  (L : Lexis) (cat : Category)
  (h_label : L.label = "to see") 
  (h_form : L.form = GrammaticalForm.ActiveVerb) 
  (h_passion : cat = Category.Passion) : 
  is_figure_of_speech L cat := by
  -- Unfold the definition and provide the conjunction
  unfold is_figure_of_speech
  constructor
  · exact h_form
  · rw [h_passion]; simp

/-! 
  ## 5. XENOCRATES: Refutation by Genus Division
  Menn p. 18: refuting "Soul is a Number" using the rule of exhaustive species.
-/

structure GenusDivision (env : DialecticalEnvironment) where
  Genus : Lexis
  Spec1 : Lexis -- e.g., Odd
  Spec2 : Lexis -- e.g., Even
  /-- Exhaustive Division: everything in the Genus falls under a Species. -/
  exhaustive : ∀ (S : Lexis), env.said_of_synonymously Genus S → 
    (env.said_of_synonymously Spec1 S ∨ env.said_of_synonymously Spec2 S)

/-- 
  Xenocrates Refutation (Menn p. 27-28).
  The argument doesn't require "Truth," only "Concession."
-/
theorem xenocrates_refutation 
  (env : DialecticalEnvironment)
  (div : GenusDivision env)
  (Soul : Lexis)
  (h_not_odd  : ¬ env.said_of_synonymously div.Spec1 Soul)
  (h_not_even : ¬ env.said_of_synonymously div.Spec2 Soul) :
  ¬ (env.said_of_synonymously div.Genus Soul) := by
  intro h_thesis
  -- Apply the Topos: If Soul were a Number, it would be Odd or Even.
  have h_cases := div.exhaustive Soul h_thesis
  -- But we have conceded it is neither.
  cases h_cases with
  | inl h_is_odd  => exact h_not_odd h_is_odd
  | inr h_is_even => exact h_not_even h_is_even

end PhiloLib.Aristotle