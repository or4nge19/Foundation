import Mathlib.Logic.Basic
import Mathlib.Tactic

open scoped Classical

namespace PhiloLib.Aristotle

/-! 
  ## 1. LEXICAL FOUNDATIONS
  Menn p. 11-12: Dialectic operates on expressions (*lexeis*).
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
  ## 2. THE FOUR-FOLD DIVISION 
  Distinguishes Genus from Differentia (Menn p. 332) and enforces the 
  Square of Opposition (Menn p. 13).
-/

class Predication (α : Type) where
  genus_of      : α → α → Prop  
  diff_of       : α → α → Prop  
  in_subject    : α → α → Prop  
  is_individual : α → Prop      
  
  said_of (g s : α) : Prop := genus_of g s ∨ diff_of g s
  indiv_not_said_of : ∀ (x y : α), is_individual x → ¬ said_of x y

export Predication (genus_of diff_of said_of in_subject is_individual)

/-! 
  ## 3. CATEGORICAL TESTS (The Idia)
-/

inductive Category
  | Substance | Quality | Quantity | Relation | Action | Passion
deriving DecidableEq, Inhabited

class CategoricalTests (α : Type) where
  has_contrary   : α → Prop
  admits_degrees : α → Prop
  signifies_this : α → Prop 

export CategoricalTests (has_contrary admits_degrees signifies_this)

/-! 
  ## 4. THE DIALECTICAL MANUAL (DISCOVERY MODEL)
  Menn's Thesis: The Category is the *result* of testing.
-/

structure DialecticalEnvironment where
  Lex : Type
  instLex   : Inhabited Lex
  instPred  : Predication Lex
  instTests : CategoricalTests Lex
  
  discovery : Lex → Option Category

  -- RULE 1: Substance Discovery (Menn p. 22)
  assign_substance : ∀ l, signifies_this l → ¬ has_contrary l → discovery l = some Category.Substance

  -- RULE 2: Substance Constraint (Menn p. 13)
  substance_not_in : ∀ l s, discovery l = some Category.Substance → ¬ in_subject l s

  -- RULE 3: Substance and Contraries (Categories 5 / Menn p. 29)
  substance_no_contrary : ∀ l, discovery l = some Category.Substance → ¬ has_contrary l

  -- RULE 4: The Topos of Genus Inheritance (Menn p. 10)
  topos_genus : ∀ g s, genus_of g s → discovery g = discovery s

/-! 
  ## 5. SCIENTIFIC ENVIRONMENT
  Menn p. 312: Science seeks causes; Dialectic does not.
-/

class Causality (α : Type) where
  causes : α → α → Prop 

structure ScientificEnvironment extends DialecticalEnvironment where
  instCause : Causality Lex
  -- Science adds causal demonstration (episteme)
  scientific_demo : ∀ P S, instCause.causes P S → (genus_of P S ∨ diff_of P S)

/-! 
  ## 6. PARONYMY AS A MANUAL TEST
  Menn p. 12: Linguistic form (Adjective) reveals ontological inherence.
-/

def is_paronymous (l : Lexis) : Prop := l.form = GrammaticalForm.Adjective

/-- 
  The Dialectical Topos: An Adjective (Paronym) implies an underlying Quality.
-/
def topos_paronymy_to_quality (env : DialecticalEnvironment) 
  (P : Lexis) (S : env.Lex) : Prop :=
  let _inst := env.instPred -- Register local instance for in_subject
  is_paronymous P → (∃ (A : env.Lex), in_subject A S ∧ env.discovery A = some Category.Quality)

/-! 
  ## 7. VERIFIED REFUTATIONS
-/

section Refutations
variable (env : DialecticalEnvironment)

-- Correctly register bundled instances for the typeclass system
instance : Inhabited env.Lex := env.instLex
instance : Predication env.Lex := env.instPred
instance : CategoricalTests env.Lex := env.instTests

/-- 
  Menn's Eudemus Refutation (p. 29): 
  Using the procedural discovery model to prove the Soul cannot be a Harmony.
-/
theorem soul_not_harmony
  (Soul Harmony : env.Lex)
  (h_soul_this : signifies_this Soul)            
  (h_soul_no_con : ¬ has_contrary Soul)          
  (h_harm_con : has_contrary Harmony) :          
  ¬ (genus_of Harmony Soul) := by
  intro h_is_genus
  
  -- Step 1: Force Category Assignment for Soul via the Manual
  have h_soul_sub : env.discovery Soul = some Category.Substance := 
    env.assign_substance Soul h_soul_this h_soul_no_con
  
  -- Step 2: Inheritance via Topos of Genus
  have h_cat_match : env.discovery Harmony = env.discovery Soul := 
    env.topos_genus Harmony Soul h_is_genus
    
  -- Step 3: Categorical classification of the predicate
  have h_harm_sub : env.discovery Harmony = some Category.Substance := by 
    rw [h_cat_match, h_soul_sub]
    
  -- Step 4: Conflict with the Manual's Rule 3 (Substances have no contraries)
  have h_harm_must_have_no_con := env.substance_no_contrary Harmony h_harm_sub
  
  -- Step 5: Final Refutation
  exact h_harm_must_have_no_con h_harm_con

/-- 
  Xenocrates Refutation (Menn p. 18): 
  Dialectical argument from exclusion.
-/
theorem xenocrates_refutation_is_non_causal 
  (Soul Number Odd Even : env.Lex) :
  said_of Number Soul → 
  (∀ s, said_of Number s → (said_of Odd s ∨ said_of Even s)) → 
  ¬ said_of Odd Soul → 
  ¬ said_of Even Soul → 
  False := by
  intros h_said h_div h_not_odd h_not_even
  unfold said_of at h_said -- essential predication is genus or diff
  have h_cases := h_div Soul h_said
  cases h_cases <;> contradiction

end Refutations

/-! 
  ## 8. LINGUISTIC TRAPS
-/

section LinguisticTraps

def is_homonymous (ctx : Lexis → Logos) (l1 l2 : Lexis) : Prop :=
  l1.label = l2.label ∧ ctx l1 ≠ ctx l2

def is_synonymous [Predication α] (ctx : α → Logos) (P S : α) : Prop :=
  said_of P S ∧ ctx P = ctx S

theorem homonymy_is_not_synonymy [Predication α] (ctx : α → Logos) (l1 l2 : α) :
  (∃ (lx1 lx2 : Lexis), lx1.label = lx2.label ∧ ctx l1 ≠ ctx l2) → 
  ¬ is_synonymous ctx l1 l2 := by
  intro h_hom h_syn
  rcases h_hom with ⟨_, _, _, h_ctx_neq⟩
  rcases h_syn with ⟨_, h_ctx_eq⟩
  exact h_ctx_neq h_ctx_eq

end LinguisticTraps

end PhiloLib.Aristotle