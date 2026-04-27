import Mathlib.Logic.Basic

namespace PhiloLib.Aristotle.Refactored

/-! 
  ## 1. THE SEMIOTIC TRIANGLE, OPAQUE BEING & HOMONYMY/SYNONYMY
  Identity is mediated by Language (Lexis) and Definition (Logos).
-/
opaque Being : Type
structure Logos where definition : String deriving DecidableEq, Inhabited
structure Lexis where label : String deriving DecidableEq, Inhabited

class Signification where
  signifies_as : Lexis → Being → Logos → Prop

def signifies [Signification] (w : Lexis) (b : Being) : Prop :=
  ∃ l, Signification.signifies_as w b l

-- HOMONYMY & SYNONYMY (Cat. 1): Relations between *things* relative to a word
def are_synonymous [Signification] (b1 b2 : Being) (w : Lexis) (l : Logos) : Prop :=
  Signification.signifies_as w b1 l ∧ Signification.signifies_as w b2 l
  
def are_homonymous [Signification] (b1 b2 : Being) (w : Lexis) (l1 l2 : Logos) : Prop :=
  Signification.signifies_as w b1 l1 ∧ Signification.signifies_as w b2 l2 ∧ l1 ≠ l2

/-! 
  ## 2. PREDICATION & THE 4-FOLD DIVISION
  Essential predication (`said_of`) and accidental inherence (`in_subject`) 
  are now the foundational primitives, exactly as established in Categories 2.
-/
class Predication extends Signification where
  -- THE TRUE PRIMITIVES
  said_of    : Being → Being → Prop  
  in_subject : Being → Being → Prop  

  -- DOWNSTREAM ROLES (Specific constraints upon the primitives)
  genus_of       : Being → Being → Prop  
  species_of     : Being → Being → Prop  
  differentia_of : Being → Being → Prop  
  
  genus_is_said_of       : ∀ g s, genus_of g s → said_of g s
  species_is_said_of     : ∀ sp s, species_of sp s → said_of sp s
  differentia_is_said_of : ∀ d s, differentia_of d s → said_of d s

  -- SYNONYMY TEST (Cat. 1 & 3): Essential predication requires Synonymy.
  said_of_synonymy : ∀ (p s : Being), said_of p s → 
    ∀ (w_p : Lexis) (l : Logos), signifies_as w_p p l → signifies_as w_p s l

  -- ASYNONYMY TEST (Cat. 2): Accidental predication forbids Synonymy.
  -- "Of things in a subject... for the logos it is impossible to be predicated."
  in_subject_asynonymy : ∀ (a s : Being), in_subject a s → 
    ∀ (w_a : Lexis) (l_a : Logos), signifies_as w_a a l_a → ¬ (∃ w_s, signifies_as w_s s l_a)

-- THE 4-FOLD ONTOLOGICAL DIVISION (Cat. 2)
def is_universal_substance [Predication] (b : Being) : Prop :=
  (∃ s, Predication.said_of b s) ∧ ¬(∃ s, Predication.in_subject b s) ∧ 
  ¬(∃ g, Predication.differentia_of b g) -- Exclude the differentiae!

def is_particular_accident [Predication] (b : Being) : Prop :=
  ¬(∃ s, Predication.said_of b s) ∧ (∃ s, Predication.in_subject b s)

def is_universal_accident [Predication] (b : Being) : Prop :=
  (∃ s, Predication.said_of b s) ∧ (∃ s, Predication.in_subject b s)

def is_particular_substance[Predication] (b : Being) : Prop :=
  ¬(∃ s, Predication.said_of b s) ∧ ¬(∃ s, Predication.in_subject b s)

/-! 
  ## 3. CATEGORIES & POST-PREDICAMENTA
  Restored to the classical 10 categories. Motion is correctly isolated
  as a cross-categorical post-predicamental phenomenon.
-/
inductive Category
  | Substance | Quantity | Quality | Relation 
  | Where | When | Position | Having | Action | Passion
deriving DecidableEq, Inhabited

class PostPredicamenta where
  is_motion       : Being → Prop
  is_prior        : Being → Being → Prop
  is_simultaneous : Being → Being → Prop

/-! 
  ## 4. DIALECTICAL STATE & HEURISTIC MANUAL
-/
class DialecticalConcession extends Signification where
  has_contrary      : Being → Prop
  admits_contraries : Being → Prop  -- The malista idion of Substance
  admits_degrees    : Being → Prop 
  is_complex_signification : Lexis → Being → Logos → Prop
  is_simple_signification  : Lexis → Being → Logos → Prop
  simple_iff_not_complex   : ∀ w b l, is_simple_signification w b l ↔ ¬ is_complex_signification w b l

class Morphology where
  derives_from : Lexis → Lexis → Prop

def is_paronymous [Signification] [Morphology] [Predication] 
  (b_complex b_quality : Being) (w_paronym w_root : Lexis) (l_par l_root : Logos) : Prop :=
  Signification.signifies_as w_paronym b_complex l_par ∧ 
  Signification.signifies_as w_root b_quality l_root ∧ 
  Morphology.derives_from w_paronym w_root ∧ 
  Predication.in_subject b_quality b_complex

class DialecticalManual extends Predication, DialecticalConcession, Morphology where
  -- Categorical placement is tied to the specific Lexis/Logos proposal.
  classifies_under : Lexis → Being → Logos → Category → Prop

  -- THE TOPOI: Heuristics to trap the opponent in dialectic.
  topos_sub_no_contrary       : ∀ w b l, classifies_under w b l Category.Substance → ¬ has_contrary b
  topos_sub_admits_contraries : ∀ w b l, classifies_under w b l Category.Substance → admits_contraries b
  topos_sub_no_degrees        : ∀ w b l, classifies_under w b l Category.Substance → ¬ admits_degrees b

  topos_proposed_contrary : ∀ p s, said_of p s → has_contrary p → has_contrary s
  topos_proposed_degrees  : ∀ p s, said_of p s → admits_degrees p → admits_degrees s

  -- AXIOMS FOR DIALECTICIANS
  -- 1. Categorical placement requires the PROPOSED signification to be simple.
  category_requires_simple : ∀ w b l c, 
    classifies_under w b l c → is_simple_signification w b l
    
  -- 2. Having an essential genus implies that *some* simple signification classifies it.
  -- (This safely allows the man to have a genus without forcing the phrase "the grammatical" to be simple).
  genus_requires_category : ∀ g s, 
    genus_of g s → ∃ w_s l_s c, classifies_under w_s s l_s c

  -- 3. Paronymous terms are linguistically/conceptually complex.
  paronyms_are_complex : ∀ b1 b2 w1 w2 l1 l2,
    is_paronymous b1 b2 w1 w2 l1 l2 → is_complex_signification w1 b1 l1

-- AXIOM: Anything classified as a Substance cannot be 'in a subject'
  substance_never_in_subject : ∀ w b l s, 
    classifies_under w b l Category.Substance → ¬ in_subject b s

/-! 
  ## 5. FIRST PHILOSOPHY (Metaphysics Z & Λ Bridge)
-/

structure CategoricalSubstance [DialecticalManual] where
  entity : Being
  lexis  : Lexis
  logos  : Logos
  is_sub : DialecticalManual.classifies_under lexis entity logos Category.Substance

-- Complete four-fold causality
class Causality where
  material_cause  : Being → Being → Prop  
  formal_cause    : Being → Being → Prop  
  efficient_cause : Being → Being → Prop
  final_cause     : Being → Being → Prop

class FirstPhilosophy [DialecticalManual] extends Causality where
  is_primary_ousia : Being → Prop 
  is_separate      : Being → Prop 
  
  matter_not_separate : ∀ m c, material_cause m c → ¬ is_separate m
  form_is_primary_ousia : ∀ f c, formal_cause f c → is_primary_ousia f

-- METAPHYSICS Z: The search for the formal causes of agreed-upon categorical substances.
def investigates_separate_form[DialecticalManual] [FirstPhilosophy] (cs : CategoricalSubstance) : Prop :=
  ∃ (form : Being), 
    Causality.formal_cause form cs.entity ∧ 
    FirstPhilosophy.is_primary_ousia form ∧ 
    FirstPhilosophy.is_separate form

-- METAPHYSICS Λ: The search for the ultimate efficient and final causes (Unmoved Mover).
def investigates_unmoved_mover [DialecticalManual] [FirstPhilosophy] (cosmos : Being) : Prop :=
  ∃ (nous : Being), 
    Causality.final_cause nous cosmos ∧ 
    FirstPhilosophy.is_separate nous ∧ 
    (∀ b, ¬ Causality.efficient_cause b nous) -- Unmoved

/-! 
  ## 6. VERIFIED REFUTATIONS
-/

section Refutations

/-- 
  FORMAL PROOF: Paronymous significations cannot serve as the categorical classification. 
-/
theorem paronymous_term_not_categorized 
  [DialecticalManual]
  (b_complex b_quality : Being) (w_par w_root : Lexis) (l_par l_root : Logos)
  (h_par : is_paronymous b_complex b_quality w_par w_root l_par l_root) : 
  ¬ ∃ (c : Category), DialecticalManual.classifies_under w_par b_complex l_par c := by
  intro h_exists
  obtain ⟨c, hc⟩ := h_exists
  have h_simple := DialecticalManual.category_requires_simple w_par b_complex l_par c hc
  have h_complex := DialecticalManual.paronyms_are_complex b_complex b_quality w_par w_root l_par l_root h_par
  have h_not_complex := (DialecticalConcession.simple_iff_not_complex w_par b_complex l_par).mp h_simple
  exact h_not_complex h_complex

/-- 
  Eudemus Refutation: Proving that Harmony is not said of Soul using the rules of dialectic.
-/
theorem soul_not_harmony_contrary [DialecticalManual]
  (Soul Harmony : Being) (w_soul : Lexis) (l_soul : Logos)
  (h_soul_sub : DialecticalManual.classifies_under w_soul Soul l_soul Category.Substance)
  (h_harm_con : DialecticalConcession.has_contrary Harmony) :
  ¬ (Predication.said_of Harmony Soul) := by
  intro h_said_of
  have h_soul_no_con := DialecticalManual.topos_sub_no_contrary w_soul Soul l_soul h_soul_sub
  have h_soul_con := DialecticalManual.topos_proposed_contrary Harmony Soul h_said_of h_harm_con
  exact h_soul_no_con h_soul_con

end Refutations

end PhiloLib.Aristotle.Refactored