import Mathlib.Logic.Basic

namespace PhiloLib.Aristotle.Refactored

/-! 
  ## 1. THE SEMIOTIC TRIANGLE & POLYMORPHISM
  Identity is mediated by Language (Lexis) and Definition (Logos).
  We pass Lexis (W), Being (B), and Logos (L) as polymorphic types.
-/

class Signification (W B L : Type) where
  signifies_as : W → B → L → Prop

def signifies {W B L : Type} [Signification W B L] (w : W) (b : B) : Prop :=
  ∃ l, Signification.signifies_as w b l

-- HOMONYMY & SYNONYMY (Cat. 1)
def are_synonymous {W B L : Type}[Signification W B L] (b1 b2 : B) (w : W) (l : L) : Prop :=
  Signification.signifies_as w b1 l ∧ Signification.signifies_as w b2 l
  
def are_homonymous {W B L : Type}[Signification W B L] (b1 b2 : B) (w : W) (l1 l2 : L) : Prop :=
  Signification.signifies_as w b1 l1 ∧ Signification.signifies_as w b2 l2 ∧ l1 ≠ l2

/-! 
  ## 2. PREDICATION & THE 4-FOLD DIVISION
  Essential predication (`said_of`) and accidental inherence (`in_subject`).
-/
class Predication (W B L : Type) extends Signification W B L where
  said_of    : B → B → Prop  
  in_subject : B → B → Prop  

  genus_of       : B → B → Prop  
  species_of     : B → B → Prop  
  differentia_of : B → B → Prop  
  
  genus_is_said_of       : ∀ g s, genus_of g s → said_of g s
  species_is_said_of     : ∀ sp s, species_of sp s → said_of sp s
  differentia_is_said_of : ∀ d s, differentia_of d s → said_of d s

  -- SYNONYMY TEST (Cat. 1 & 3): Essential predication requires Synonymy.
  said_of_synonymy : ∀ (p s : B), said_of p s → 
    ∀ (w_p : W) (l : L), signifies_as w_p p l → signifies_as w_p s l

  -- ASYNONYMY TEST (Cat. 2): Accidental predication forbids Synonymy.
  in_subject_asynonymy : ∀ (a s : B), in_subject a s → 
    ∀ (w_a : W) (l_a : L), signifies_as w_a a l_a → ¬ (∃ w_s, signifies_as w_s s l_a)

-- THE 4-FOLD ONTOLOGICAL DIVISION (Cat. 2)
-- Note: Differentiae correctly fall under universal substances here structurally 
-- (said of, not in subject) as per Cat. 5 (3a21).
def is_universal_substance {W B L : Type} [Predication W B L] (b : B) : Prop :=
  (∃ s, Predication.said_of b s) ∧ ¬(∃ s, Predication.in_subject b s)

def is_particular_accident {W B L : Type} [Predication W B L] (b : B) : Prop :=
  ¬(∃ s, Predication.said_of b s) ∧ (∃ s, Predication.in_subject b s)

def is_universal_accident {W B L : Type} [Predication W B L] (b : B) : Prop :=
  (∃ s, Predication.said_of b s) ∧ (∃ s, Predication.in_subject b s)

def is_particular_substance {W B L : Type} [Predication W B L] (b : B) : Prop :=
  ¬(∃ s, Predication.said_of b s) ∧ ¬(∃ s, Predication.in_subject b s)

/-! 
  ## 3. CATEGORIES & POST-PREDICAMENTA
-/
inductive Category
  | Substance | Quantity | Quality | Relation 
  | Where | When | Position | Having | Action | Passion
deriving DecidableEq, Inhabited

class PostPredicamenta (B : Type) where
  is_motion       : B → Prop
  is_prior        : B → B → Prop
  is_simultaneous : B → B → Prop

/-! 
  ## 4. DIALECTICAL STATE & HEURISTIC MANUAL
-/
class DialecticalConcession (W B L : Type) extends Signification W B L where
  has_contrary      : B → Prop
  admits_contraries : B → Prop  
  admits_degrees    : B → Prop 
  is_complex_signification : W → B → L → Prop
  is_simple_signification  : W → B → L → Prop
  simple_iff_not_complex   : ∀ w b l, is_simple_signification w b l ↔ ¬ is_complex_signification w b l

class Morphology (W : Type) where
  derives_from : W → W → Prop

-- Paronymy strictly as a linguistic derivation mapping to an ontological relation.
-- (Removed strict in_subject constraint to handle cases like "The Grammatical")
def is_paronymous {W B L : Type} [Signification W B L] [Morphology W] 
  (b_complex b_quality : B) (w_paronym w_root : W) (l_par l_root : L) : Prop :=
  Signification.signifies_as w_paronym b_complex l_par ∧ 
  Signification.signifies_as w_root b_quality l_root ∧ 
  Morphology.derives_from w_paronym w_root

class DialecticalManual (W B L : Type) extends Predication W B L, DialecticalConcession W B L, Morphology W where
  classifies_under : W → B → L → Category → Prop

  -- AXIOMS FOR DIALECTICIANS
  category_requires_simple : ∀ w b l c, 
    classifies_under w b l c → is_simple_signification w b l
    
  genus_requires_category : ∀ g s, 
    genus_of g s → ∃ w_s l_s c, classifies_under w_s s l_s c

  paronyms_are_complex : ∀ b1 b2 w1 w2 l1 l2,
    is_paronymous b1 b2 w1 w2 l1 l2 → is_complex_signification w1 b1 l1

  substance_never_in_subject : ∀ w b l s, 
    classifies_under w b l Category.Substance → ¬ in_subject b s

  -- ONTOLOGICAL PRIMITIVES FOR DERIVING TOPOI
  -- Axiom: Contraries require a shared subject to alternate within.
  contraries_inhere_in_subject : ∀ b, has_contrary b → ∃ s, in_subject b s
  
  -- Axiom: If P is said of S, S inherits the categorical limitations/features of P.
  said_of_preserves_contrary : ∀ p s, said_of p s → has_contrary p → has_contrary s

/-! 
  ## 5. DERIVING THE TOPOI (Theorems, not Axioms)
-/
section Topoi
variable {W B L : Type} [DialecticalManual W B L]

/-- Topos: A categorical substance cannot have a contrary. -/
theorem topos_sub_no_contrary (w : W) (b : B) (l : L) 
  (h_sub : DialecticalManual.classifies_under w b l Category.Substance) : 
  ¬ DialecticalConcession.has_contrary b := by
  intro h_contrary
  -- From the axiom that contraries must alternate within a subject:
  have ⟨s, h_in_subj⟩ := DialecticalManual.contraries_inhere_in_subject b h_contrary
  -- From the axiom that substances are never in a subject:
  have h_not_in_subj := DialecticalManual.substance_never_in_subject w b l s h_sub
  -- Contradiction:
  exact h_not_in_subj h_in_subj

/-- Topos: If a proposed genus has a contrary, the species must have a contrary. -/
theorem topos_proposed_contrary (p s : B) (h_said : Predication.said_of p s) 
  (h_p_con : DialecticalConcession.has_contrary p) : 
  DialecticalConcession.has_contrary s := 
  DialecticalManual.said_of_preserves_contrary p s h_said h_p_con

end Topoi

/-! 
  ## 6. FIRST PHILOSOPHY (Metaphysics Z & Λ Bridge)
-/

structure CategoricalSubstance {W B L : Type}[DialecticalManual W B L] where
  entity : B
  lexis  : W
  logos  : L
  is_sub : DialecticalManual.classifies_under lexis entity logos Category.Substance

class Causality (B : Type) where
  material_cause  : B → B → Prop  
  formal_cause    : B → B → Prop  
  efficient_cause : B → B → Prop
  final_cause     : B → B → Prop

class FirstPhilosophy (W B L : Type)[DialecticalManual W B L] extends Causality B where
  is_primary_ousia : B → Prop 
  
  -- Separability cleanly divided to avoid accidental Platonism
  is_separate_in_formula   : B → Prop 
  is_separate_in_existence : B → Prop 
  
  matter_not_separate_formula : ∀ m c, material_cause m c → ¬ is_separate_in_formula m
  matter_not_separate_existence : ∀ m c, material_cause m c → ¬ is_separate_in_existence m
  form_is_primary_ousia : ∀ f c, formal_cause f c → is_primary_ousia f

-- METAPHYSICS Z: The search for the formal causes of sensible categorical substances.
-- The form is primary and separate in formula, but critically NOT separate in existence!
def investigates_separate_form {W B L : Type} [DialecticalManual W B L][FirstPhilosophy W B L] (cs : CategoricalSubstance) : Prop :=
  ∃ (form : B), 
    Causality.formal_cause form cs.entity ∧ 
    FirstPhilosophy.is_primary_ousia form ∧ 
    FirstPhilosophy.is_separate_in_formula form ∧
    ¬ FirstPhilosophy.is_separate_in_existence form

-- METAPHYSICS Λ: The search for the ultimate efficient and final causes.
-- The Unmoved Mover is truly separate in existence.
def investigates_unmoved_mover {W B L : Type} [DialecticalManual W B L][FirstPhilosophy W B L] (cosmos : B) : Prop :=
  ∃ (nous : B), 
    Causality.final_cause nous cosmos ∧ 
    FirstPhilosophy.is_separate_in_existence nous ∧ 
    (∀ b, ¬ Causality.efficient_cause b nous)

/-! 
  ## 7. VERIFIED REFUTATIONS
-/

section Refutations
variable {W B L : Type}[DialecticalManual W B L]

/-- FORMAL PROOF: Paronymous significations cannot serve as the categorical classification. -/
theorem paronymous_term_not_categorized 
  (b_complex b_quality : B) (w_par w_root : W) (l_par l_root : L)
  (h_par : is_paronymous b_complex b_quality w_par w_root l_par l_root) : 
  ¬ ∃ (c : Category), DialecticalManual.classifies_under w_par b_complex l_par c := by
  intro h_exists
  obtain ⟨c, hc⟩ := h_exists
  have h_simple := DialecticalManual.category_requires_simple w_par b_complex l_par c hc
  have h_complex := DialecticalManual.paronyms_are_complex b_complex b_quality w_par w_root l_par l_root h_par
  have h_not_complex := (DialecticalConcession.simple_iff_not_complex w_par b_complex l_par).mp h_simple
  exact h_not_complex h_complex

/-- Eudemus Refutation: Modus Tollens proving Harmony is not the genus of Soul using derived Topoi. -/
theorem soul_not_harmony_contrary
  (Soul Harmony : B) (w_soul : W) (l_soul : L)
  (h_soul_sub : DialecticalManual.classifies_under w_soul Soul l_soul Category.Substance)
  (h_harm_con : DialecticalConcession.has_contrary Harmony) :
  ¬ (Predication.said_of Harmony Soul) := by
  intro h_said_of
  have h_soul_no_con := topos_sub_no_contrary w_soul Soul l_soul h_soul_sub
  have h_soul_con := topos_proposed_contrary Harmony Soul h_said_of h_harm_con
  exact h_soul_no_con h_soul_con

end Refutations

end PhiloLib.Aristotle.Refactored