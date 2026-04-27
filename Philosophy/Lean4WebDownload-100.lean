import Mathlib.Logic.Basic
import Mathlib.Tactic

open scoped Classical

namespace PhiloLib.Aristotle

/-! 
  ## 1. LEXICAL FOUNDATIONS
  Menn p. 11: Dialectic operates on expressions (*lexeis*) and their definitions (*logoi*).
-/

inductive GrammaticalForm
  | ActiveVerb | PassiveVerb | Noun | Adjective
deriving DecidableEq, Inhabited

structure Lexis where
  label : String
  form  : GrammaticalForm
deriving DecidableEq, Inhabited

structure Logos where
  definition : String
deriving DecidableEq, Inhabited

/-! 
  ## 2. THE FOUR-FOLD DIVISION (Categories 2)
  Menn's Thesis: The grid (Said-of / In-subject) is the primary tool.
-/

class Predication (α : Type) where
  said_of : α → α → Prop    -- Essential predication (Genus/Species)
  in_subject : α → α → Prop -- Accidental inherence (Accidents)

export Predication (said_of in_subject)

/-! 
  ## 3. CATEGORICAL TESTS (The Idia)
  Menn Ch. 5-9: Categories are discovered by linguistic tests (contraries, degrees).
-/

inductive Category
  | Substance | Quality | Quantity | Relation | Action | Passion
deriving DecidableEq, Inhabited

class CategoricalTests (α : Type) where
  has_contrary : α → Prop
  admits_degrees : α → Prop
  signifies_this : α → Prop -- "Tode ti" test for substances

export CategoricalTests (has_contrary admits_degrees signifies_this)

/-! 
  ## 4. DIALECTICAL ENVIRONMENT
  The "Missing Link": The Categories provides the classification, 
  the Topics provides the rules for how those classes behave in argument.
-/

structure DialecticalEnvironment where
  Lex : Type
  [instLex : Inhabited Lex]
  [instPred : Predication Lex]
  [instTests : CategoricalTests Lex]
  cat : Lex → Category
  -- Menn p. 21: Substances have no contraries (Linguistic property).
  substance_no_contrary : ∀ l, cat l = Category.Substance → ¬ has_contrary l
  -- Menn p. 10: Essential predication implies category inheritance.
  inheritance : ∀ g s, said_of g s → cat g = cat s

/-! 
  ## 5. VERIFIED REFUTATIONS
-/

section Refutations
variable (env : DialecticalEnvironment)
-- Unpack the bundled instances for use in the theorem signatures
attribute [local instance] env.instPred env.instTests

/-- 
  Xenocrates Refutation (Menn p. 18): 
  Refuting "Soul is a Number" using Species Exhaustion.
  Logic: If the genus is divided into species, and the subject falls 
  under neither, the subject is not the genus.
-/
theorem xenocrates_refutation 
  (Soul Number Odd Even : env.Lex) :
  said_of Number Soul → 
  (∀ s, said_of Number s → (said_of Odd s ∨ said_of Even s)) → 
  ¬ said_of Odd Soul → 
  ¬ said_of Even Soul → 
  False := by
  intros h_said h_div h_not_odd h_not_even
  have h_cases := h_div Soul h_said
  cases h_cases <;> contradiction

/-- 
  Menn's Eudemus Refutation (p. 29):
  Refutation by catching a contradiction between the proponent's claim
  and the Dialectical Manual (Categories).
  
  Logic: 
  1. Thesis: Soul is a Harmony (Said-of relation).
  2. Topos: Genus and Species share a category.
  3. Manual Rule: Substances have no contraries; Harmony (a Quality) does.
-/
theorem soul_not_harmony
  (Soul Harmony : env.Lex)
  (h_soul_sub : env.cat Soul = Category.Substance)
  (h_harm_con : has_contrary Harmony) :
  ¬ (said_of Harmony Soul) := by
  intro h_said
  -- 1. By the rule of inheritance (Topics), Harmony and Soul must share a category
  have h_cat_match := env.inheritance Harmony Soul h_said
  -- 2. Therefore Harmony must be a Substance (since Soul is conceded as one)
  have h_harm_sub : env.cat Harmony = Category.Substance := by rwa [h_cat_match]
  -- 3. But the manual (Categories) establishes that no substance has a contrary
  have h_no_con := env.substance_no_contrary Harmony h_harm_sub
  -- 4. Contradiction between the proponent's term and the categorical test
  exact h_no_con h_harm_con

end Refutations

/-! 
  ## 6. SUPPLEMENTARY: Synonymy vs. Paronymy
  Menn p. 12-13: The distinction is linguistic, not just ontological.
-/

def is_synonymous [Predication Lexis] (ctx : Lexis → Logos) (G S : Lexis) : Prop :=
  said_of G S ∧ ctx G = ctx S

def is_paronymous [Predication Lexis] (P S : Lexis) : Prop :=
  in_subject P S ∧ P.form = GrammaticalForm.Adjective

end PhiloLib.Aristotle

