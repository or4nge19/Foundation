import Mathlib.Logic.Basic
import Mathlib.Tactic

open scoped Classical

namespace PhiloLib.Aristotle.Final

/-! 
  ## 1. THE SEMIOTIC TRIANGLE (Word, Definition, Thing)
  A 3-place relation `signifies_as` is used to represent partiality natively, 
  avoiding computationally hostile dependent types while perfectly capturing 
  Aristotle's linguistic-ontological mapping.
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
-/

class Morphology where
  derives_from : Lexis → Lexis → Prop

/-! 
  ## 2. THE FULL SQUARE OF OPPOSITION
  Orthogonal mapping of Essential Predication (`said_of`) and Accidental Inherence (`in_subject`).
-/

class Predication (α : Type) where
  genus_of              : α → α → Prop  
  species_of            : α → α → Prop  
  differentia_of        : α → α → Prop  
  in_subject            : α → α → Prop  
  is_individual         : α → Prop      
  
  -- Essential Universal Predication (Strict hierarchy)
  said_of (p s : α) : Prop := 
    genus_of p s ∨ species_of p s ∨ differentia_of p s
  
  indiv_not_said_of : ∀ (x y : α), is_individual x → ¬ said_of x y

/-- A Universal Accident is something that is BOTH said of a lower universal 
    AND in a subject (Categories 1a20). -/
def is_universal_accident [Predication Being] (u : Being) : Prop :=
  (∃ s, Predication.said_of u s) ∧ (∃ sub, Predication.in_subject u sub)
  
/-- 
  Paronymy bridges language and ontology natively.
  Example: "Grammatical" (w1) and "Grammar" (w2) signify the Man (b_complex) and the Science (b_quality).
-/
def is_paronymous [Signification] [Morphology][Predication Being] 
  (b_complex b_quality : Being) (w_paronym w_root : Lexis) : Prop :=
  signifies w_paronym b_complex ∧ 
  signifies w_root b_quality ∧ 
  Morphology.derives_from w_paronym w_root ∧ 
  -- The quality is an accident (it is in SOME subject, though not necessarily the complex itself)
  ∃ (b_substance : Being), Predication.in_subject b_quality b_substance

/-! 
  ## 3. CATEGORICAL TESTS & COMPLEXITY
  Distinguishes simple Beings (which have categories) from complex Beings (which do not).
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
  Menn's Thesis: The Categories is a heuristic handbook to help the dialectician 
  rule out proposed genera or definitions by establishing negative constraints.
-/

class DialecticalManual extends 
  Predication Being, CategoricalTests Being, Signification, Morphology 
where
  falls_under : Being → Category → Prop

  -- Constraint Rules
  sub_no_contrary : ∀ b, falls_under b Category.Substance → ¬ has_contrary b
  sub_no_degrees  : ∀ b, falls_under b Category.Substance → ¬ admits_degrees b

  -- Differentiae of substances are NOT in a subject (Categories 3a21)
  diff_of_sub_not_in : ∀ (d s : Being), 
    falls_under s Category.Substance → differentia_of d s → 
    ∀ (x : Being), ¬ in_subject d x

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

  -- WIDENED TOPOI: The dialectician traps the opponent based on what 
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
  ¬ ∃ (g : Being), genus_of g b1 := by
  -- Assume for contradiction that the paronym has a genus `g`
  intro ⟨g, h_genus⟩
  -- 1. If it has a genus, it must fall under a category
  have ⟨c, h_falls_under⟩ := genus_requires_category g b1 h_genus
  -- 2. If it falls under a category, it must be a simple term
  have h_simple := category_requires_simple b1 c h_falls_under
  -- 3. But paronyms signify complex terms
  have h_complex := paronyms_are_complex b1 b2 w1 w2 h_par
  -- 4. Simple terms are strictly not complex
  have h_not_complex := (simple_iff_not_complex b1).mp h_simple
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

/-- 
  Phaedo Refutation (Menn p. 330):
  Soul is a substance (no degrees). Harmony has degrees.
  Therefore Harmony is not said of Soul.
-/
theorem soul_not_harmony_degrees [DialecticalManual]
  (Soul Harmony : Being)
  (h_soul_sub : falls_under Soul Category.Substance)
  (h_harm_deg : admits_degrees Harmony) :
  ¬ (said_of Harmony Soul) := by
  intro h_said_of
  have h_soul_no_deg := sub_no_degrees Soul h_soul_sub
  have h_soul_deg := topos_proposed_degrees Harmony Soul h_said_of h_harm_deg
  exact h_soul_no_deg h_soul_deg

end Refutations

/-! 
  ## 6. FIRST PHILOSOPHY (Metaphysics Z)
  Completely decoupled from DialecticalManual, averting the Neo-Platonic collapse 
  by establishing causal archai rather than dialectical constraints.
-/

class Causality (α : Type) where
  material_cause : α → α → Prop  
  formal_cause   : α → α → Prop  

class FirstPhilosophy extends Causality Being where
  is_primary_ousia : Being → Prop 
  is_separate      : Being → Prop 
  
  matter_not_separate : ∀ (m c : Being), material_cause m c → ¬ is_separate m
  form_is_primary_ousia : ∀ (f c : Being), formal_cause f c → is_primary_ousia f

end PhiloLib.Aristotle.Final
/-
This "devil’s advocate" review focuses on the friction between Lean’s formal requirements and the nuances of Stephen Menn’s historical-philosophical reconstruction. While the code is elegant, several architectural choices may "leak" unintended metaphysical commitments or oversimplify Menn’s specific claims about the relationship between the *Topics* and the *Categories*.

---

### 1. The "Ontological Lean": `Being` as a Structure
**The Code:** `structure Being where id : String`
**The Critique:** By defining `Being` as a concrete structure with an identity string, you have already made an ontological commitment that Menn (and Aristotle) might find "un-dialectical."
*   **The Issue:** For the dialectician, a "Being" is often just "that which is signified by a term in a proposition." By making `Being` a distinct type from `Lexis`, you assume we can pick out Beings independently of the language used to frame them.
*   **Menn’s Perspective:** Menn emphasizes that the *Categories* is a "survey of the kinds of being that a term might signify" (p. 321). 
*   **The Fix:** Consider making `Being` an opaque type or a property of `Lexis` within the `Signification` class. If `Being` is too "solid," the formalization becomes an Ontology, whereas Menn argues the *Categories* is an *Encheiridion* (handbook) for linguistic moves.

### 2. Signification vs. Predication (The Paronymy Trap)
**The Code:** 
```lean
def is_paronymous [...] : Prop :=
  signifies w_paronym b_complex ∧ signifies w_root b_quality ∧ ...
```
**The Critique:** This definition conflates **signification** (what the word points to) with **predication** (what the word is said of).
*   **The Issue:** In Menn’s analysis of paronymy (p. 321-322), "grammatical" (*grammatikos*) is paronymous because it derives from "grammar" (*grammatikê*). However, does "grammatical" signify the "Complex Being" (the man)? Aristotle says the word "grammatical" is *predicated* of the man, but it *signifies* the quality (grammar) *as* qualifying a subject. 
*   **The Danger:** Your `paronym_has_no_genus` theorem relies on `b1` (the complex being) being the thing signified. If the paronym actually signifies a quality in a certain "mode" of predication, the proof collapses. You are proving that a *Man-with-Grammar* has no genus, which is trivial. Menn’s point is that the **term** "grammatical" cannot be placed in a genus because it refers to a "this-in-a-that."

### 3. The "Decoupling" of Metaphysics and Dialectic
**The Code:** `class FirstPhilosophy extends Causality Being` (completely separate from `DialecticalManual`).
**The Critique:** While Menn argues they are different *disciplines*, he insists they are looking at the **same objects** through different lenses. 
*   **The Issue:** By decoupling them into separate classes, you miss the "Contradiction" Menn seeks to resolve. Menn's paper starts by acknowledging that it *looks* like Aristotle contradicts himself on what a "Primary Substance" is (Socrates in *Cat.* vs. Soul in *Met.*).
*   **The Fix:** You should allow the `FirstPhilosophy` class to see the `DialecticalManual` constraints. The power of Menn’s thesis is that the same `b : Being` (e.g., Socrates' Soul) can be a `Quality` to a Dialectician (because it passes the "in a subject" test) but a `Substance` to a Metaphysician (because it is a formal cause). Your code doesn't yet allow for this "productive tension."

### 4. Categorical Tests as `Prop` vs. `Heuristic`
**The Code:** `sub_no_contrary : ∀ b, falls_under b Category.Substance → ¬ has_contrary b`
**The Critique:** You treat these as absolute axioms. Menn treats them as **tests** for the disputant.
*   **The Issue:** Menn notes that the *Categories* is "authoritarian" and "lays down rules... supported by examples rather than serious argument" (p. 315). 
*   **The Heuristic Problem:** If an opponent proposes that "Virtue is a Substance," the dialectician uses the *test* of contraries to refute them. If your Lean code makes `¬ has_contrary` a hard-coded requirement of the *type* Substance, you can't model a "failed dialectical move" where someone wrongly attributes a category.
*   **Suggestion:** Model these as `Topoi`—rules that allow one to derive a contradiction from a proposed definition, rather than global axioms of being.

### 5. Missing: The "Said of / In" Distinction as a Function of `Logos`
**The Critique:** In Section 1.b, you define `said_of` and `in_subject` as simple relations between `Being` and `Being`. 
*   **The Issue:** Menn argues that the difference between "synonymous" and "homonymous" depends on the **Logos** (definition). 
*   **Menn’s Point:** "Substances are said synonymously... of all the things they are said of" (p. 322). This means if $A$ is said of $B$, then the `Logos` of $A$ must be true of $B$. 
*   **The Fix:** `said_of` should probably be defined in terms of your `Signification` triangle. $A$ is `said_of` $B$ if and only if for every word $w$ and definition $l$ that signifies $A$, $w$ signifies $B$ according to that same $l$. Without the `Logos` being central to predication, you are doing 17th-century ontology, not Aristotelian logic.

### 6. The "Decidability" of Categories
**The Code:** `simple_term_mutually_exclusive`
**The Critique:** Does Menn agree that categories are mutually exclusive for the *dialectician*?
*   **The Issue:** Menn mentions that "seeing" (*horan*) looks like an Action (`poiein`) but is actually a Passion (`paschein`). A dialectician might exploit this ambiguity. 
*   **The Point:** By enforcing `c1 = c2` as a Lean axiom, you make it impossible to model **sophisms** (which Menn spends significant time on, p. 320). To model the *Sophistical Refutations* (the "final book of the Topics"), the manual needs to allow for "Figure of Speech" errors where a term *appears* to fall under two categories.

---

### Final "Devil's Advocate" Verdict:
The formalization is a **Great Ontology** but a **Thin Manual**. 

To truly capture Menn’s "reconstruction," the code needs to shift from:
1.  **"What is Being?"** (Fixed axioms) 
2.  **"How do we classify this term?"** (Heuristic tests). 

**Immediate Recommendation:** Move the categorical properties (contraries, degrees) from the `Being` itself into the `Signification` relation. A being has no contrary *under a certain description*. This would align perfectly with Menn’s "Semiotic Triangle" on page 321.-/