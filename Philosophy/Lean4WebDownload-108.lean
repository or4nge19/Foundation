import Mathlib.Logic.Basic
import Mathlib.Tactic

open scoped Classical

namespace PhiloLib.Aristotle.V5

/-! 
  ## 1. THE SEMIOTIC TRIANGLE (Word, Definition, Thing)
  Fixing Critique 2: We use a 3-place relation `signifies_as` to represent 
  partiality natively, avoiding the computationally hostile dependent types.
-/

structure Being where id : String deriving DecidableEq, Inhabited
structure Logos where definition : String deriving DecidableEq, Inhabited
structure Lexis where label : String deriving DecidableEq, Inhabited

class Signification where
  -- signifies_as w b l: "Word `w` signifies Being `b` according to Definition `l`"
  signifies_as : Lexis → Being → Logos → Prop

/-- Helper definition: w signifies b if there exists SOME definition linking them. -/
def signifies [Signification] (w : Lexis) (b : Being) : Prop :=
  ∃ l, Signification.signifies_as w b l

def is_synonymous [Signification] (b1 b2 : Being) (w : Lexis) (l : Logos) : Prop :=
  Signification.signifies_as w b1 l ∧ Signification.signifies_as w b2 l

def is_homonymous [Signification] (b1 b2 : Being) (w : Lexis) (l1 l2 : Logos) : Prop :=
  Signification.signifies_as w b1 l1 ∧ Signification.signifies_as w b2 l2 ∧ l1 ≠ l2

/-!
  ## 1b. MORPHOLOGY & PARONYMY
  Fixing Critique 1: Flattened into a pure logical conjunction with no unused proof terms.
-/

class Morphology where
  derives_from : Lexis → Lexis → Prop

/-! 
  ## 2. THE FULL SQUARE OF OPPOSITION
  Fixing Critique 3 & 5: Restored the top-right quadrant (universal accidents).
-/

class Predication (α : Type) where
  genus_of              : α → α → Prop  
  species_of            : α → α → Prop  
  differentia_of        : α → α → Prop  
  universal_accident_of : α → α → Prop  
  in_subject            : α → α → Prop  
  is_individual         : α → Prop      
  
  said_of (p s : α) : Prop := genus_of p s ∨ species_of p s ∨ differentia_of p s
  indiv_not_said_of : ∀ (x y : α), is_individual x → ¬ said_of x y
/-- A Universal Accident is something that is BOTH said of a lower universal 
    AND in a subject (Categories 1a20). -/
def is_universal_accident [Predication Being] (u : Being) : Prop :=
  (∃ s, Predication.said_of u s) ∧ (∃ sub, Predication.in_subject u sub)
  
/-- 
  Paronymy bridges language and ontology natively.
  Example: "Grammatical" (w1) and "Grammar" (w2) signify the Man (b1) and the Science (b2).
-/
def is_paronymous [Signification] [Morphology][Predication Being] 
  (b_complex b_quality : Being) (w_paronym w_root : Lexis) : Prop :=
  signifies w_paronym b_complex ∧ 
  signifies w_root b_quality ∧ 
  Morphology.derives_from w_paronym w_root ∧ 
  -- The quality is an accident (it is in SOME subject)
  ∃ (b_substance : Being), Predication.in_subject b_quality b_substance

/-! 
  ## 3. CATEGORICAL TESTS & COMPLEXITY
  Fixing Critique 4: Added `is_complex_term` to distinguish between simple Beings 
  (which have categories) and complex Beings (which do not).
-/

inductive Category
  | Substance | Quality | Quantity | Relation | Action | Passion | Motion
deriving DecidableEq, Inhabited

class CategoricalTests (α : Type) where
  has_contrary   : α → Prop
  admits_degrees : α → Prop 
  is_simple_term : α → Prop
  is_complex_term: α → Prop
  
  simple_iff_not_complex : ∀ x : α, is_simple_term x ↔ ¬ is_complex_term x

/-! 
  ## 4. THE DIALECTICAL MANUAL (Topics & Categories)
-/

class DialecticalManual extends 
  Predication Being, CategoricalTests Being, Signification, Morphology 
where
  falls_under : Being → Category → Prop

  -- Constraint Rules
  sub_no_contrary : ∀ b, falls_under b Category.Substance → ¬ has_contrary b
  sub_no_degrees  : ∀ b, falls_under b Category.Substance → ¬ admits_degrees b

  -- ONTOLOGICAL AXIOMS FOR THE DIALECTICIAN (Menn p. 321)
  -- 1. Only simple terms fall under a category ("things said without combination").
  category_requires_simple : ∀ (b : Being) (c : Category), 
    falls_under b c → is_simple_term b
    
  -- 2. Having a genus requires falling under a category.
  genus_requires_category : ∀ (g s : Being),
    genus_of g s → ∃ c, falls_under s c

  -- 3. Paronyms signify complex terms ("the grammatical man" is Substance + Quality).
  paronyms_are_complex : ∀ (b1 b2 : Being) (w1 w2 : Lexis),
    is_paronymous b1 b2 w1 w2 → is_complex_term b1

  -- WIDENED TOPOI (Fix 3): The dialectician traps the opponent based on what 
  -- they *propose* is said-of the subject, which might be a universal accident!
  topos_proposed_contrary : ∀ (p s : Being), said_of p s → has_contrary p → has_contrary s
  topos_proposed_degrees  : ∀ (p s : Being), said_of p s → admits_degrees p → admits_degrees s
  
  -- Mutual Exclusivity
  simple_term_mutually_exclusive : ∀ (b : Being) (c1 c2 : Category),
    is_simple_term b → falls_under b c1 → falls_under b c2 → c1 = c2


/-! 
  ## 5. VERIFIED REFUTATIONS
-/

section Refutations
open DialecticalManual Predication CategoricalTests
/-- 
  FORMAL PROOF OF MENN'S CLAIM (p. 321): 
  Paronyms have no genus, and thus fall under no single category.
-/
theorem paronym_has_no_genus [DialecticalManual] 
  (b1 b2 : Being) (w1 w2 : Lexis) (h_par : is_paronymous b1 b2 w1 w2) :
  ¬ ∃ (g : Being), Predication.genus_of g b1 := by
  -- Assume for contradiction that the paronym has a genus `g`
  intro ⟨g, h_genus⟩
  -- 1. If it has a genus, it must fall under a category
  have ⟨c, h_falls_under⟩ := DialecticalManual.genus_requires_category g b1 h_genus
  -- 2. If it falls under a category, it must be a simple term
  have h_simple := DialecticalManual.category_requires_simple b1 c h_falls_under
  -- 3. But paronyms signify complex terms
  have h_complex := DialecticalManual.paronyms_are_complex b1 b2 w1 w2 h_par
  -- 4. Simple terms are strictly not complex
  have h_not_complex := (CategoricalTests.simple_iff_not_complex b1).mp h_simple
  -- 5. Contradiction
  exact h_not_complex h_complex


/-- 
  Eudemus Refutation (Menn p. 329):
  Proving that Harmony is not said of Soul (widened from genus_of).
-/
theorem soul_not_harmony_contrary [DialecticalManual]
  (Soul Harmony : Being)
  (h_soul_sub : falls_under Soul Category.Substance)
  (h_harm_con : has_contrary Harmony) :
  ¬ (said_of Harmony Soul) := by
  intro h_said_of
  have h_soul_no_con := sub_no_contrary Soul h_soul_sub
  have h_soul_con := topos_proposed_contrary Harmony Soul h_said_of h_harm_con
  exact h_soul_no_con h_soul_con

end Refutations

/-! 
  ## 6. FIRST PHILOSOPHY (Metaphysics Z)
  Completely decoupled from DialecticalManual, averting the Neo-Platonic collapse.
-/

class Causality (α : Type) where
  material_cause : α → α → Prop  
  formal_cause   : α → α → Prop  

class FirstPhilosophy extends Causality Being where
  is_primary_ousia : Being → Prop 
  is_separate      : Being → Prop 
  
  matter_not_separate : ∀ (m c : Being), material_cause m c → ¬ is_separate m
  form_is_primary_ousia : ∀ (f c : Being), formal_cause f c → is_primary_ousia f

end PhiloLib.Aristotle.V5