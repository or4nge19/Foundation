import Mathlib.Logic.Basic

namespace PhiloLib.Aristotle.Refactored

/-! 
  ## 1. THE SEMIOTIC TRIANGLE & POLYMORPHISM
  Identity is mediated by Language (Lexis) and Definition (Logos).
  We pass Lexis (W), Being (B), and Logos (L) as polymorphic type variables 
  to ensure the logic does not depend on a single, hardcoded ontological universe.
-/

class Signification (W B L : Type) where
  signifies_as : W → B → L → Prop

def signifies {W B L : Type} [Signification W B L] (w : W) (b : B) : Prop :=
  ∃ l : L, Signification.signifies_as w b l

-- HOMONYMY & SYNONYMY (Cat. 1)
def are_synonymous {W B L : Type} [Signification W B L] (b1 b2 : B) (w : W) (l : L) : Prop :=
  Signification.signifies_as w b1 l ∧ Signification.signifies_as w b2 l
  
def are_homonymous {W B L : Type}[Signification W B L] (b1 b2 : B) (w : W) (l1 l2 : L) : Prop :=
  Signification.signifies_as w b1 l1 ∧ Signification.signifies_as w b2 l2 ∧ l1 ≠ l2

/-! 
  ## 2. PREDICATION & THE 4-FOLD DIVISION
  We separate `Ontology` from `Signification` so that purely existential/ontological
  facts (like `said_of`) do not require linguistic resolution to evaluate.
-/
class Ontology (B : Type) where
  said_of    : B → B → Prop  
  in_subject : B → B → Prop  

  genus_of       : B → B → Prop  
  species_of     : B → B → Prop  
  differentia_of : B → B → Prop  
  
  genus_is_said_of       : ∀ (g s : B), genus_of g s → said_of g s
  species_is_said_of     : ∀ (sp s : B), species_of sp s → said_of sp s
  differentia_is_said_of : ∀ (d s : B), differentia_of d s → said_of d s

class Predication (W B L : Type) extends Ontology B, Signification W B L where
  -- SYNONYMY TEST (Cat. 1 & 3): Essential predication requires Synonymy.
  said_of_synonymy : ∀ (p s : B), Ontology.said_of p s → 
    ∀ (w_p : W) (l : L), Signification.signifies_as w_p p l → Signification.signifies_as w_p s l

  -- ASYNONYMY TEST (Cat. 2): Accidental predication forbids Synonymy.
  in_subject_asynonymy : ∀ (a s : B), Ontology.in_subject a s → 
    ∀ (w_a : W) (l_a : L), Signification.signifies_as w_a a l_a → ¬ (∃ w_s : W, Signification.signifies_as w_s s l_a)

-- THE 4-FOLD ONTOLOGICAL DIVISION (Cat. 2)
-- Note: Differentiae correctly fall under universal substances here structurally 
-- (said of, not in subject) as per Cat. 5 (3a21).
def is_universal_substance {B : Type}[Ontology B] (b : B) : Prop :=
  (∃ s, Ontology.said_of b s) ∧ ¬(∃ s, Ontology.in_subject b s)

def is_particular_accident {B : Type} [Ontology B] (b : B) : Prop :=
  ¬(∃ s, Ontology.said_of b s) ∧ (∃ s, Ontology.in_subject b s)

def is_universal_accident {B : Type} [Ontology B] (b : B) : Prop :=
  (∃ s, Ontology.said_of b s) ∧ (∃ s, Ontology.in_subject b s)

def is_particular_substance {B : Type} [Ontology B] (b : B) : Prop :=
  ¬(∃ s, Ontology.said_of b s) ∧ ¬(∃ s, Ontology.in_subject b s)

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
class DialecticalOntology (B : Type) where
  has_contrary      : B → Prop
  admits_contraries : B → Prop  
  admits_degrees    : B → Prop 

class DialecticalConcession (W B L : Type) extends Signification W B L, DialecticalOntology B where
  is_complex_signification : W → B → L → Prop
  is_simple_signification  : W → B → L → Prop
  simple_iff_not_complex   : ∀ (w : W) (b : B) (l : L), is_simple_signification w b l ↔ ¬ is_complex_signification w b l

class Morphology (W : Type) where
  derives_from : W → W → Prop

-- Paronymy strictly as a linguistic derivation mapping to an ontological relation.
-- (Removed strict in_subject constraint to handle cases like "The Grammatical")
def is_paronymous {W B L : Type} [Signification W B L] [Morphology W] 
  (b_complex b_quality : B) (w_paronym w_root : W) (l_par l_root : L) : Prop :=
  Signification.signifies_as w_paronym b_complex l_par ∧ 
  Signification.signifies_as w_root b_quality l_root ∧ 
  Morphology.derives_from w_paronym w_root

namespace PhiloLib.Epistemology

/-!
  THE EPISTEMIC BARRIER
  We define two mutually exclusive wrappers for propositions.
-/

/-- Dialectical knowledge (hoti / 'that it is').
    Achieved through the Topoi and endoxa. It is logically valid 
    in debate but lacks causal explanatory power. -/
inductive Dialectical (P : Prop) : Prop where
  | conceded : P → Dialectical P
  | derived  : P → Dialectical P

/-- Causality is required for Science. -/
class Causality (B : Type) where
  material_cause  : B → B → Prop  
  formal_cause    : B → B → Prop  
  efficient_cause : B → B → Prop
  final_cause     : B → B → Prop
  -- A generic relation stating that 'c' is the cause of fact 'P'
  explains        : B → Prop → Prop 

/-- Scientific knowledge (epistêmê / dioti / 'why it is').
    To hold a proposition scientifically, you must not only know THAT it is true,
    but you must possess the precise CAUSE that makes it true. -/
structure Episteme {B : Type} [Causality B] (P : Prop) : Prop where
  fact     : P
  cause    : B
  explains : Causality.explains cause P

end PhiloLib.Epistemology

class DialecticalManual' (W B L : Type) extends Predication W B L, DialecticalConcession W B L, Morphology W where
  classifies_under : W → B → L → Category → Prop

  -- AXIOMS FOR DIALECTICIANS
  category_requires_simple : ∀ (w : W) (b : B) (l : L) (c : Category), 
    classifies_under w b l c → DialecticalConcession.is_simple_signification w b l
    
  genus_requires_category : ∀ (g s : B), 
    Ontology.genus_of g s → ∃ (w_s : W) (l_s : L) (c : Category), classifies_under w_s s l_s c

  paronyms_are_complex : ∀ (b1 b2 : B) (w1 w2 : W) (l1 l2 : L),
    is_paronymous b1 b2 w1 w2 l1 l2 → DialecticalConcession.is_complex_signification w1 b1 l1

  substance_never_in_subject : ∀ (w : W) (b : B) (l : L) (s : B), 
    classifies_under w b l Category.Substance → ¬ Ontology.in_subject b s

  -- ONTOLOGICAL PRIMITIVES FOR DERIVING TOPOI
  -- Axiom: Contraries require a shared subject to alternate within.
  contraries_inhere_in_subject : ∀ (b : B), DialecticalOntology.has_contrary b → ∃ (s : B), Ontology.in_subject b s
  
  -- Axiom: If P is said of S, S inherits the categorical limitations/features of P.
  said_of_preserves_contrary : ∀ (p s : B), Ontology.said_of p s → DialecticalOntology.has_contrary p → DialecticalOntology.has_contrary s

open PhiloLib.Epistemology

class DialecticalManual (W B L : Type) extends Predication W B L, DialecticalConcession W B L where
  classifies_under : W → B → L → Category → Prop

  -- The Topoi now strictly return `Dialectical P`. 
  -- They are rules of debate, not scientific demonstrations.
  /-- Topos: Substances have no contraries. 
      Used implicitly in the Eudemus to prove the soul is not a harmony. -/
  topos_substance_no_contrary : ∀ (w : W) (b : B) (l : L), 
    classifies_under w b l Category.Substance → Dialectical (¬ DialecticalOntology.has_contrary b)
  /-- Topos: If a proposed genus has a contrary, the species must have a contrary. -/

  topos_genus_species_contrary : ∀ (g s : B), 
    Ontology.genus_of g s → DialecticalOntology.has_contrary g → Dialectical (DialecticalOntology.has_contrary s)

  -- 1. STRUCTURAL HEURISTICS
  -- Basic rules the dialectician must verify before debate can proceed.
  category_requires_simple : ∀ (w : W) (b : B) (l : L) (c : Category), 
    classifies_under w b l c → DialecticalConcession.is_simple_signification w b l
    
  genus_requires_category : ∀ (g s : B), 
    Ontology.genus_of g s → ∃ (w_s : W) (l_s : L) (c : Category), classifies_under w_s s l_s c

  substance_never_in_subject : ∀ (w : W) (b : B) (l : L) (s : B), 
    classifies_under w b l Category.Substance → ¬ Ontology.in_subject b s

  -- 2. THE TOPOI AS AXIOMATIC RULES OF THE GAME
  -- These are not derived from deeper causal truths; they are the accepted 
  -- tests (idia) used to force a respondent into a contradiction.

  /-- Topos: Substances do not receive more and less. -/
  topos_substance_no_degrees : ∀ (w : W) (b : B) (l : L),
    classifies_under w b l Category.Substance → ¬ DialecticalOntology.admits_degrees b

  /-- Topos: A single substance is capable of contrary attributes (malista idion). -/
  topos_substance_admits_contraries : ∀ (w : W) (b : B) (l : L),
    classifies_under w b l Category.Substance → DialecticalOntology.admits_contraries b


/-! 
  ## 5. DERIVING THE TOPOI (Theorems, not Axioms)
  Topoi are no longer unproven postulates; they are derived from the structure of 
  Aristotle's categorical constraints and ontological inheritance.
-/
section Topoi
variable {W B L : Type} [DialecticalManual W B L]

/-- Topos: A categorical substance cannot have a contrary. -/
theorem topos_sub_no_contrary (w : W) (b : B) (l : L) 
  (h_sub : DialecticalManual.classifies_under w b l Category.Substance) : 
  ¬ DialecticalOntology.has_contrary b := by
  intro h_contrary
  have ⟨s, h_in_subj⟩ := @DialecticalManual.contraries_inhere_in_subject W B L _ b h_contrary
  have h_not_in_subj := DialecticalManual.substance_never_in_subject w b l s h_sub
  exact h_not_in_subj h_in_subj

/-- Topos: If a proposed genus has a contrary, the species must have a contrary. -/
theorem topos_proposed_contrary (p s : B) (h_said : Ontology.said_of p s) 
  (h_p_con : DialecticalOntology.has_contrary p) : 
  DialecticalOntology.has_contrary s := 
  @DialecticalManual.said_of_preserves_contrary W B L _ p s h_said h_p_con

end Topoi

/-! 
  ## 6. FIRST PHILOSOPHY (Metaphysics Z & Λ Bridge)
-/

structure CategoricalSubstance (W B L : Type)[DialecticalManual W B L] where
  entity : B
  lexis  : W
  logos  : L
  is_sub : DialecticalManual.classifies_under lexis entity logos Category.Substance

class Causality (B : Type) where
  material_cause  : B → B → Prop  
  formal_cause    : B → B → Prop  
  efficient_cause : B → B → Prop
  final_cause     : B → B → Prop

class FirstPhilosophy (B : Type) extends Causality B where
  is_primary_ousia : B → Prop 
  
  -- Separability cleanly divided to avoid accidental Platonism (Menn's critique of Z)
  is_separate_in_formula   : B → Prop 
  is_separate_in_existence : B → Prop 
  
  matter_not_separate_formula : ∀ (m c : B), Causality.material_cause m c → ¬ is_separate_in_formula m
  matter_not_separate_existence : ∀ (m c : B), Causality.material_cause m c → ¬ is_separate_in_existence m
  form_is_primary_ousia : ∀ (f c : B), Causality.formal_cause f c → is_primary_ousia f

-- METAPHYSICS Z: The search for the formal causes of sensible categorical substances.
-- The form is primary and separate in formula, but critically NOT separate in existence!
def investigates_separate_form {W B L : Type} [DialecticalManual W B L] [FirstPhilosophy B] (cs : CategoricalSubstance W B L) : Prop :=
  ∃ (form : B), 
    Causality.formal_cause form cs.entity ∧ 
    FirstPhilosophy.is_primary_ousia form ∧ 
    FirstPhilosophy.is_separate_in_formula form ∧
    ¬ FirstPhilosophy.is_separate_in_existence form

-- METAPHYSICS Λ: The search for the ultimate efficient and final causes.
-- The Unmoved Mover is truly separate in existence.
def investigates_unmoved_mover {B : Type} [FirstPhilosophy B] (cosmos : B) : Prop :=
  ∃ (nous : B), 
    Causality.final_cause nous cosmos ∧ 
    FirstPhilosophy.is_separate_in_existence nous ∧ 
    (∀ (b : B), ¬ Causality.efficient_cause b nous)

/-! 
  ## 7. VERIFIED REFUTATIONS
-/

section Refutations
variable {W B L : Type} [DialecticalManual W B L]

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
theorem soul_not_harmony_contrary'
  (Soul Harmony : B) (w_soul : W) (l_soul : L)
  (h_soul_sub : DialecticalManual.classifies_under w_soul Soul l_soul Category.Substance)
  (h_harm_con : DialecticalOntology.has_contrary Harmony) :
  ¬ (Ontology.said_of Harmony Soul) := by
  intro h_said_of
  have h_soul_no_con := topos_sub_no_contrary w_soul Soul l_soul h_soul_sub
  have h_soul_con := @topos_proposed_contrary W B L _ Harmony Soul h_said_of h_harm_con
  exact h_soul_no_con h_soul_con

end Refutations
/-! 
  ## APPLICATION IN DIALECTIC
  We can now construct a valid dialectical refutation purely from the manual's rules,
  without needing to prove *why* the rules hold ontologically.
-/

section Refutations
variable {W B L : Type} [DialecticalManual W B L]

/-- Eudemus Refutation: Proving Harmony is not the genus of Soul. 
    Notice this is now a straightforward application of the manual's axiomatic tests, 
    mirroring how a dialectician would deploy it in a live debate. -/
theorem soul_not_harmony_contrary
  (Soul Harmony : B) (w_soul : W) (l_soul : L)
  (h_soul_sub : DialecticalManual.classifies_under w_soul Soul l_soul Category.Substance)
  (h_harm_con : DialecticalOntology.has_contrary Harmony) :
  ¬ (Ontology.genus_of Harmony Soul) := by
  intro h_genus
  -- The dialectician cites the manual: Substances have no contraries.
  have h_soul_no_con := DialecticalManual.topos_substance_no_contrary w_soul Soul l_soul h_soul_sub
  -- The dialectician cites the manual: Genera pass contraries to their species.
  have h_soul_con := DialecticalManual.topos_genus_species_contrary Harmony Soul h_genus h_harm_con
  -- Contradiction forces the respondent to yield.
  exact h_soul_no_con h_soul_con

end Refutations
end PhiloLib.Aristotle.Refactored