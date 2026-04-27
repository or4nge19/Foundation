import Mathlib.Logic.Basic
import Mathlib.Tactic

-- We use Classical logic because dialectic assumes every 
-- categorical test (e.g. "Has it a contrary?") can be answered yes/no.
open scoped Classical

namespace PhiloLib.Aristotle

/-!
  ## 1. LEXICAL FOUNDATIONS: Names and Accounts
  Menn Ch. 1: Dialectic operates on expressions (*lexeis*) and their accounts (*logoi*).
-/

structure Lexis where
  label : String
deriving DecidableEq, Inhabited

structure Logos where
  definition : String
deriving DecidableEq

structure DialecticalContext where
  signifies : Lexis → Logos → Prop

/-!
  ## 2. THE GRID (Predication as Moves)
  Menn p. 13: The Fourfold Division classifies how terms are "said of" or "in" a subject.
-/

structure DialecticalEnvironment extends DialecticalContext where
  said_of : Lexis → Lexis → Prop
  in_subject : Lexis → Lexis → Prop

/-!
  ## 3. LINGUISTIC IDIA (The Tests)
  Linguistic tests (Contraries, Degrees) are the tools for the "Hunt."
-/

class CategoryTests (env : DialecticalEnvironment) where
  has_contrary : Lexis → Prop
  admits_degrees : Lexis → Prop

  /-- 
    TOPICS IV GENUS RULE (Inheritance Topos).
    Menn p. 10: The species must inherit the contrary status of its genus.
  -/
  topos_genus_inheritance : ∀ {G S : Lexis},
    env.said_of G S → has_contrary G → has_contrary S

/-!
  ## 4. THE EUDEMUS REFUTATION (The Trapping)
  Menn p. 329: Refutation by contradiction between Topos and Concession.
-/

theorem eudemus_refutation
  (env : DialecticalEnvironment)
  [tests : CategoryTests env]
  (soul harmony : Lexis)
  (thesis : env.said_of harmony soul)
  (h_harm_con : CategoryTests.has_contrary env harmony)
  (h_soul_no_con : ¬ CategoryTests.has_contrary env soul) :
  False := by
  -- Use the Topos of Inheritance: if Soul were a species of Harmony, it would have a contrary.
  have h_trap := CategoryTests.topos_genus_inheritance thesis h_harm_con
  -- Conflict reached: The Proponent's thesis is refuted by the Respondent's concession.
  exact h_soul_no_con h_trap

/-! 
  ## 5. THE PERSIAN HUNT (Procedural Discovery)
  Classification via the procedure of exclusion.
-/

inductive Category
  | Substance
  | Quality
deriving DecidableEq

/-- 
  The Persian Hunt (Menn p. 9).
  Classification is the result of applying linguistic tests (idia).
-/
noncomputable def persian_hunt (env : DialecticalEnvironment) [tests : CategoryTests env] (L : Lexis) : Category :=
  if ¬ CategoryTests.has_contrary env L ∧ ¬ CategoryTests.admits_degrees env L then
    Category.Substance
  else
    Category.Quality

theorem persian_hunt_discovery
  (env : DialecticalEnvironment) [tests : CategoryTests env] (L : Lexis)
  (h_fail_tests : ¬ CategoryTests.has_contrary env L ∧ ¬ CategoryTests.admits_degrees env L) :
  persian_hunt env L = Category.Substance := by
  unfold persian_hunt
  -- split correctly handles the if-then-else based on the provided hypothesis
  split
  · rfl
  · rename_i h_not_sub
    -- This branch is unreachable given h_fail_tests
    contradiction

end PhiloLib.Aristotle