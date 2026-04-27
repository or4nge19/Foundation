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
  The Square of Opposition (Menn p. 13).
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
  | Substance | Quality | Quantity | Relation | Action | Passion | Motion
deriving DecidableEq, Inhabited

class CategoricalTests (α : Type) where
  has_contrary   : α → Prop
  admits_degrees : α → Prop 
  signifies_this : α → Prop 

export CategoricalTests (has_contrary admits_degrees signifies_this)

/-! 
  ## 4. THE DIALECTICAL MANUAL (DISCOVERY MODEL)
  Menn's Thesis: The Category is the *result* of testing. (Menn p. 327)
-/

structure DialecticalEnvironment where
  Lex : Type
  instLex   : Inhabited Lex
  instPred  : Predication Lex
  instTests : CategoricalTests Lex
  
  discovery : Lex → Option Category
  is_prior  : Lex → Lex → Prop -- Categories 12 (Menn p. 17)

  -- Discovery Rules (The Manual's Tests)
  assign_sub_by_contrary : ∀ l, signifies_this l → ¬ has_contrary l → discovery l = some Category.Substance
  assign_sub_by_degree   : ∀ l, signifies_this l → ¬ admits_degrees l → discovery l = some Category.Substance

  -- Constraint Rules (The Manual's Definitions)
  sub_no_contrary : ∀ l, discovery l = some Category.Substance → ¬ has_contrary l
  sub_no_degrees  : ∀ l, discovery l = some Category.Substance → ¬ admits_degrees l
  sub_not_in      : ∀ l s, discovery l = some Category.Substance → ¬ in_subject l s

  -- Topoi (Topics Rules)
  topos_genus : ∀ g s, genus_of g s → discovery g = discovery s

/-! 
  ## 5. VERIFIED REFUTATIONS (Non-Causal)
-/

section Refutations
variable (env : DialecticalEnvironment)
instance : Predication env.Lex := env.instPred
instance : CategoricalTests env.Lex := env.instTests

/-- 
  Eudemus Refutation (Menn p. 329): Harmony has a contrary, Soul does not.
-/
theorem soul_not_harmony_contrary
  (Soul Harmony : env.Lex)
  (h_soul_this : signifies_this Soul)            
  (h_soul_no_con : ¬ has_contrary Soul)          
  (h_harm_con : has_contrary Harmony) :          
  ¬ (genus_of Harmony Soul) := by
  intro h_is_genus
  -- Use Rule: Discovery by Contrary
  have h_soul_sub := env.assign_sub_by_contrary Soul h_soul_this h_soul_no_con
  have h_harm_sub : env.discovery Harmony = some Category.Substance := by 
    rw [env.topos_genus Harmony Soul h_is_genus, h_soul_sub]
  -- Use Constraint: Substance has no contrary
  have h_no_con := env.sub_no_contrary Harmony h_harm_sub
  exact h_no_con h_harm_con

/-- 
  Phaedo Refutation (Menn p. 330): Harmony admits degrees, Soul does not.
-/
theorem soul_not_harmony_degrees
  (Soul Harmony : env.Lex)
  (h_soul_this : signifies_this Soul)
  (h_soul_no_deg : ¬ admits_degrees Soul)
  (h_harm_deg : admits_degrees Harmony) :
  ¬ (genus_of Harmony Soul) := by
  intro h_is_genus
  -- Use Rule: Discovery by Degree
  have h_soul_sub := env.assign_sub_by_degree Soul h_soul_this h_soul_no_deg
  have h_harm_sub : env.discovery Harmony = some Category.Substance := by
    rw [env.topos_genus Harmony Soul h_is_genus, h_soul_sub]
  -- Use Constraint: Substance has no degrees
  have h_no_deg := env.sub_no_degrees Harmony h_harm_sub
  exact h_no_deg h_harm_deg

/-- 
  Xenocrates Refutation (Menn p. 18): Dialectical exclusion.
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

end Refutations

/-! 
  ## 6. THE GRID OF FOUR
-/

def is_primary_substance (env : DialecticalEnvironment) (l : env.Lex) : Prop :=
  let _inst := env.instPred
  is_individual l ∧ env.discovery l = some Category.Substance

def is_secondary_substance (env : DialecticalEnvironment) (l : env.Lex) : Prop :=
  let _inst := env.instPred
  ¬ is_individual l ∧ env.discovery l = some Category.Substance

/-! 
  ## 7. SCIENTIFIC EXTENSION
  Menn p. 312: Science is Dialectic plus Causality.
-/

class Causality (α : Type) where
  causes : α → α → Prop 

structure ScientificEnvironment extends DialecticalEnvironment where
  instCause : Causality Lex
  scientific_demo : ∀ P S, instCause.causes P S → said_of P S

/-! 
  ## 8. LINGUISTIC TRAPS
-/

section LinguisticTraps

def is_homonymous (ctx : Lexis → Logos) (l1 l2 : Lexis) : Prop :=
  l1.label = l2.label ∧ ctx l1 ≠ ctx l2

def is_synonymous [Predication α] (ctx : α → Logos) (P S : α) : Prop :=
  said_of P S ∧ ctx P = ctx S

end LinguisticTraps

end PhiloLib.Aristotle