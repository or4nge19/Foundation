import Mathlib.Logic.Basic
import Mathlib.Tactic

open scoped Classical

namespace PhiloLib.Aristotle.V3

/-! 
  ## 1. THE SEMIOTIC TRIANGLE (Word, Definition, Thing)
  Fixing the Overcorrection: Synonymy and Homonymy are properties of THINGS 
  (Beings) that share a name, not properties of the words themselves (Categories 1).
-/

structure Being where
  id : String
deriving DecidableEq, Inhabited

structure Logos where
  definition : String
deriving DecidableEq, Inhabited

structure Lexis where
  label : String
deriving DecidableEq, Inhabited

-- Signification is a relation. One Lexis can signify multiple Beings.
class Signification where
  signifies : Lexis → Being → Prop
  logos_of  : Lexis → Being → Logos

export Signification (signifies logos_of)

/-- 
  Synonymy: Two THINGS are synonymous if they are signified by the same WORD 
  and share the same LOGOS (definition) relative to that word.
-/
def is_synonymous [Signification] (b1 b2 : Being) (w : Lexis) : Prop :=
  signifies w b1 ∧ signifies w b2 ∧ logos_of w b1 = logos_of w b2

/-- 
  Homonymy: Two THINGS are homonymous if they are signified by the same WORD 
  but have a different LOGOS (definition) relative to that word.
-/
def is_homonymous [Signification] (b1 b2 : Being) (w : Lexis) : Prop :=
  signifies w b1 ∧ signifies w b2 ∧ logos_of w b1 ≠ logos_of w b2

/-! 
  ## 2. PREDICATION (The Square of Opposition)
  Added `species_of` to complete the `said_of` relation.
-/

class Predication (α : Type) where
  genus_of      : α → α → Prop  
  species_of    : α → α → Prop  -- Added to fix Critique 2
  diff_of       : α → α → Prop  
  in_subject    : α → α → Prop  
  is_individual : α → Prop      
  
  -- "Said of" includes Genus, Species, and Differentia.
  said_of (p s : α) : Prop := genus_of p s ∨ species_of p s ∨ diff_of p s
  
  indiv_not_said_of : ∀ (x y : α), is_individual x → ¬ said_of x y

export Predication (genus_of species_of diff_of in_subject is_individual said_of)

/-! 
  ## 3. CATEGORICAL TESTS (The Idia)
  Unbundled into a clean typeclass.
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
  ## 4. THE DIALECTICAL MANUAL (Topics & Categories)
  Fixing Critique 5: `falls_under` is now a Relation, not a Function. 
  "Things said with combination" do not fall under a single category.
-/

class DialecticalManual extends Predication Being, CategoricalTests Being where
  falls_under : Being → Category → Prop

  -- CONSTRAINT RULES: Negative heuristic filters (Menn p. 323)
  sub_no_contrary : ∀ b, falls_under b Category.Substance → ¬ has_contrary b
  sub_no_degrees  : ∀ b, falls_under b Category.Substance → ¬ admits_degrees b
  sub_not_in      : ∀ b s, falls_under b Category.Substance → ¬ in_subject b s

  -- TOPOI FOR GENUS TESTING (Topics IV)
  topos_genus_contrary : ∀ (g s : Being), genus_of g s → has_contrary g → has_contrary s
  topos_genus_degrees  : ∀ (g s : Being), genus_of g s → admits_degrees g → admits_degrees s
  
  -- MENN'S CONJECTURE (p. 332, fn 34): 
  -- In the dialectical manual, immanent forms are treated as a kind of Quality (shape),
  -- NOT as substances.
  immanent_form_is_quality : ∀ (form composite : Being), 
    falls_under form Category.Quality


/-! 
  ## 5. VERIFIED REFUTATIONS
  Idiomatic Lean 4 passing of typeclasses (`[DialecticalManual]`).
-/

section Refutations

/-- 
  Eudemus Refutation (Menn p. 329):
  Soul is a substance (therefore no contrary). Harmony has a contrary.
  Therefore Harmony is not the genus of Soul.
-/
theorem soul_not_harmony_contrary [DialecticalManual]
  (Soul Harmony : Being)
  (h_soul_sub : DialecticalManual.falls_under Soul Category.Substance)
  (h_harm_con : has_contrary Harmony) :
  ¬ (genus_of Harmony Soul) := by
  intro h_is_genus
  have h_soul_no_con : ¬ has_contrary Soul := DialecticalManual.sub_no_contrary Soul h_soul_sub
  have h_soul_con : has_contrary Soul := DialecticalManual.topos_genus_contrary Harmony Soul h_is_genus h_harm_con
  exact h_soul_no_con h_soul_con

/-- 
  Phaedo Refutation (Menn p. 330):
  Soul is a substance (no degrees). Harmony has degrees.
  Therefore Harmony is not the genus of Soul.
-/
theorem soul_not_harmony_degrees [DialecticalManual]
  (Soul Harmony : Being)
  (h_soul_sub : DialecticalManual.falls_under Soul Category.Substance)
  (h_harm_deg : admits_degrees Harmony) :
  ¬ (genus_of Harmony Soul) := by
  intro h_is_genus
  have h_soul_no_deg : ¬ admits_degrees Soul := DialecticalManual.sub_no_degrees Soul h_soul_sub
  have h_soul_deg : admits_degrees Soul := DialecticalManual.topos_genus_degrees Harmony Soul h_is_genus h_harm_deg
  exact h_soul_no_deg h_soul_deg

end Refutations

/-! 
  ## 6. METAPHYSICS Z: FIRST PHILOSOPHY
  Fixing the Fatal Flaw (Critique 4): FirstPhilosophy completely DECOUPLED 
  from DialecticalManual. Metaphysics Z searches for causes of Being.
-/

class Causality (α : Type) where
  material_cause : α → α → Prop  -- The subject/matter of X
  formal_cause   : α → α → Prop  -- The essence/form of X

class FirstPhilosophy extends Causality Being where
  -- Metaphysical substance (Ousia), entirely distinct from the Dialectical Category of Substance.
  is_primary_ousia : Being → Prop 
  is_separate      : Being → Prop 
  
  -- Metaphysics Z.3 (1029a28): Matter cannot be the ultimate separate substance.
  matter_not_separate : ∀ (m c : Being), 
    material_cause m c → ¬ is_separate m
    
  -- MENN'S CLIMAX (p. 337): In First Philosophy, the formal cause (Essence) IS 
  -- the primary substance. (This logically contradicts the Categories 
  -- treating form as a Quality, exactly as Menn thesis dictates).
  form_is_primary_ousia : ∀ (f c : Being),
    formal_cause f c → is_primary_ousia f

end PhiloLib.Aristotle.V3