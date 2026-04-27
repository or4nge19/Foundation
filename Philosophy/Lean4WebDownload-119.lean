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

class Morphology (W : Type) where
  derives_from : W → W → Prop

-- Paronymy strictly as a linguistic derivation mapping to an ontological relation.
-- Now relies on the failure of logos transmission to distinguish from synonymy.
def is_paronymous {W B L : Type} [Signification W B L] [Morphology W] 
  (b_complex b_quality : B) (w_paronym w_root : W) (l_par l_root : L) : Prop :=
  Signification.signifies_as w_paronym b_complex l_par ∧ 
  Signification.signifies_as w_root b_quality l_root ∧ 
  Morphology.derives_from w_paronym w_root ∧
  l_par ≠ l_root

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
  ## 4. THE EPISTEMIC BARRIER
  Separates Dialectic (non-causal rules of debate) from Episteme (causal science).
-/

namespace Epistemology

/-- Dialectical knowledge (hoti). 
    Logically valid in debate but lacks causal explanatory power. -/
inductive Dialectical (P : Prop) : Prop where
  | conceded : P → Dialectical P
  | derived  : P → Dialectical P

/-- A helper to allow logical deduction within the Dialectical wrapper. -/
axiom dialectical_mt {P Q : Prop} : Dialectical (P → Q) → Dialectical ¬Q → Dialectical ¬P

class Causality (B : Type) where
  material_cause  : B → B → Prop  
  formal_cause    : B → B → Prop  
  efficient_cause : B → B → Prop
  final_cause     : B → B → Prop
  explains        : B → Prop → Prop 
  -- Axiom: Scientific explanation guarantees the truth of the fact.
  cause_guarantees_fact : ∀ {c : B} {P : Prop}, explains c P → P

/-- Scientific knowledge (epistêmê / dioti).
    Must possess the precise CAUSE that makes the proposition true. 
    Notice this now returns `Type`, reflecting a cognitive state containing data. -/
structure Episteme (B : Type) [Causality B] (P : Prop) : Type where
  fact     : P
  cause    : B
  explains : Causality.explains cause P

end Epistemology

open Epistemology

/-! 
  ## 5. DIALECTICAL STATE & HEURISTIC MANUAL (The Categories)
-/

class DialecticalOntology (B : Type) where
  has_contrary      : B → Prop
  admits_contraries : B → Prop  
  admits_degrees    : B → Prop 

class DialecticalConcession (W B L : Type) extends Signification W B L, DialecticalOntology B where
  is_complex_signification : W → B → L → Prop
  is_simple_signification  : W → B → L → Prop
  simple_iff_not_complex   : ∀ (w : W) (b : B) (l : L), is_simple_signification w b l ↔ ¬ is_complex_signification w b l

class DialecticalManual (W B L : Type) extends Predication W B L, DialecticalConcession W B L, Morphology W where
  classifies_under : W → B → L → Category → Prop

  -- STRUCTURAL HEURISTICS
  category_requires_simple : ∀ (w : W) (b : B) (l : L) (c : Category), 
    classifies_under w b l c → is_simple_signification w b l
    
  genus_requires_category : ∀ (g s : B), 
    Ontology.genus_of g s → ∃ (w_s : W) (l_s : L) (c : Category), classifies_under w_s s l_s c

  paronyms_are_complex : ∀ (b1 b2 : B) (w1 w2 : W) (l1 l2 : L),
    is_paronymous b1 b2 w1 w2 l1 l2 → is_complex_signification w1 b1 l1

  substance_never_in_subject : ∀ (w : W) (b : B) (l : L) (s : B), 
    classifies_under w b l Category.Substance → ¬ Ontology.in_subject b s

  -- THE TOPOI AS AXIOMATIC RULES OF THE GAME
  -- These yield `Dialectical P`, enforcing the epistemic barrier.
  topos_substance_no_contrary : ∀ (w : W) (b : B) (l : L), 
    classifies_under w b l Category.Substance → Dialectical (¬ DialecticalOntology.has_contrary b)

  topos_substance_no_degrees : ∀ (w : W) (b : B) (l : L),
    classifies_under w b l Category.Substance → Dialectical (¬ DialecticalOntology.admits_degrees b)

  topos_substance_admits_contraries : ∀ (w : W) (b : B) (l : L),
    classifies_under w b l Category.Substance → Dialectical (DialecticalOntology.admits_contraries b)

  topos_genus_species_contrary : ∀ (g s : B), 
    Ontology.genus_of g s → DialecticalOntology.has_contrary g → Dialectical (DialecticalOntology.has_contrary s)

  -- Dialectical axiom: If G is genus of S, and G has property X, S has property X.
  -- Represented here specifically for the Modus Tollens setup.
  genus_passes_contrary_rule : ∀ (g s : B),
    Ontology.genus_of g s → (¬ DialecticalOntology.has_contrary s → ¬ DialecticalOntology.has_contrary g)

/-! 
  ## 6. VERIFIED REFUTATIONS
-/

section Refutations
variable {W B L : Type} [DialecticalManual W B L]

/-- Eudemus Refutation: Proving Harmony is not the genus of Soul. 
    Returns `Dialectical P`, representing a debate victory without causal science. -/
theorem soul_not_harmony_dialectical
  (Soul Harmony : B) (w_soul : W) (l_soul : L)
  (h_soul_sub : DialecticalManual.classifies_under w_soul Soul l_soul Category.Substance)
  (h_harm_con : DialecticalOntology.has_contrary Harmony) :
  Dialectical (¬ Ontology.genus_of Harmony Soul) := by
  -- 1. Cite the manual: Substances have no contraries.
  have h_soul_no_con : Dialectical (¬ DialecticalOntology.has_contrary Soul) := 
    DialecticalManual.topos_substance_no_contrary w_soul Soul l_soul h_soul_sub
  
  -- 2. State the logical implication of passing contraries from genus to species.
  -- We use Classical contradiction to derive the positive implication from the manual's contrapositive rule.
  have h_implication : Dialectical (Ontology.genus_of Harmony Soul → DialecticalOntology.has_contrary Soul) :=
    Dialectical.conceded (fun h_gen => 
      Classical.byContradiction (fun h_not_soul_con => 
        have h_not_harm_con := DialecticalManual.genus_passes_contrary_rule Harmony Soul h_gen h_not_soul_con
        h_not_harm_con h_harm_con
      )
    )
      
  -- 3. Apply Dialectical Modus Tollens to force the conclusion.
  exact dialectical_mt h_implication h_soul_no_con

end Refutations


/-! 
  ## 7. THEORETICAL SCIENCES: PHYSICS VS. FIRST PHILOSOPHY
  We strictly divide the causal sciences based on their objects' relationship to matter.
-/

/-- Physics studies natural things whose forms are inseparable from matter and motion. -/
class Physics (B : Type) extends Causality B where
  has_internal_principle_of_motion : B → Prop
  is_inseparable_from_matter       : B → Prop
  
  -- The formal cause of a natural object cannot exist separately from its matter.
  physical_form_inseparable : ∀ (f c : B), 
    has_internal_principle_of_motion c → Causality.formal_cause f c → is_inseparable_from_matter f

/-- First Philosophy studies the highest causes, specifically seeking substances 
    that exist eternally apart from matter. -/
class FirstPhilosophy (B : Type) extends Causality B where
  is_primary_ousia : B → Prop 
  
  is_separate_in_formula   : B → Prop 
  is_separate_in_existence : B → Prop 
  
  matter_not_separate_formula : ∀ (m c : B), Causality.material_cause m c → ¬ is_separate_in_formula m
  matter_not_separate_existence : ∀ (m c : B), Causality.material_cause m c → ¬ is_separate_in_existence m
  form_is_primary_ousia : ∀ (f c : B), Causality.formal_cause f c → is_primary_ousia f

/-! 
  ## 8. CAUSAL DEMONSTRATIONS (Epistêmê)
-/
structure CategoricalSubstance (W B L : Type)[DialecticalManual W B L] where
  entity : B
  lexis  : W
  logos  : L
  is_sub : DialecticalManual.classifies_under lexis entity logos Category.Substance

-- METAPHYSICS Z: The search for the formal causes of sensible categorical substances.
-- This bridges Physics and First Philosophy by asking *whether* the cause is separate.
def investigates_substance_causes {W B L : Type} [DialecticalManual W B L] [FirstPhilosophy B] (cs : CategoricalSubstance W B L) : Prop :=
  ∃ (form : B), 
    Causality.formal_cause form cs.entity ∧ 
    FirstPhilosophy.is_primary_ousia form ∧ 
    FirstPhilosophy.is_separate_in_formula form

-- METAPHYSICS Λ: The search for the ultimate efficient and final causes (Theology).
def investigates_unmoved_mover {B : Type} [FirstPhilosophy B] (cosmos : B) : Prop :=
  ∃ (nous : B), 
    Causality.final_cause nous cosmos ∧ 
    FirstPhilosophy.is_separate_in_existence nous ∧ 
    (∀ (b : B), ¬ Causality.efficient_cause b nous)

/-- DE ANIMA / PHYSICS: A scientist attempting to demonstrate a truth about the Soul 
    MUST provide the formal cause. Because the soul is inseparable from matter, 
    this demonstration properly requires the `Physics` class. -/
def demonstrate_soul_nature {B : Type} [Physics B] (Soul : B) (P : Prop) (formal_cause : B) 
  (h_explains : Causality.explains formal_cause P) : Episteme B P := 
  { fact := Causality.cause_guarantees_fact h_explains, -- The cause scientifically guarantees the fact.
    cause := formal_cause, 
    explains := h_explains }


end PhiloLib.Aristotle.Refactored