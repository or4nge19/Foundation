import Philosophy.Aristotle.PriorAnalytics.Syntax

namespace Aristotle.PriorAnalytics

/-!
# Syllogistic Proof Theory

This file contains the asserted moods and derivability machinery for the
assertoric fragment currently modeled.
-/

inductive Figure
  | first
  | second
  | third
  deriving DecidableEq, Repr

inductive Mood
  | barbara
  | celarent
  | cesare
  | camestres
  deriving DecidableEq, Repr

def Mood.figure : Mood → Figure
  | .barbara => .first
  | .celarent => .first
  | .cesare => .second
  | .camestres => .second

/-- First-figure syllogisms are the perfected forms currently modeled. -/
def Figure.IsPerfect : Figure → Prop
  | .first => True
  | .second => False
  | .third => False

def Mood.IsPerfect (m : Mood) : Prop :=
  m.figure.IsPerfect

/--
The simple conversions licensed in the current assertoric fragment.

This is intentionally narrower than mere term-swapping.
-/
inductive SimplyConverts : Categorical → Categorical → Prop
  | e (S P : Term) : SimplyConverts (.E S P) (.E P S)
  | i (S P : Term) : SimplyConverts (.I S P) (.I P S)

theorem SimplyConverts.swapTerms_eq {premise conclusion : Categorical}
    (h : SimplyConverts premise conclusion) :
    conclusion = premise.swapTerms := by
  cases h <;> rfl

theorem SimplyConverts.symm {premise conclusion : Categorical}
    (h : SimplyConverts premise conclusion) :
    SimplyConverts conclusion premise := by
  cases h with
  | e S P => exact .e P S
  | i S P => exact .i P S

theorem SimplyConverts.source_isSimplyConvertible {premise conclusion : Categorical}
    (h : SimplyConverts premise conclusion) :
    premise.IsSimplyConvertible := by
  cases h <;> trivial

/--
Validity / deduction system (⊢).

The quantity and quality of a premise are carried by the categorical form
itself, not by a second layer of metadata on terms.
-/
inductive Deduce : List Categorical → Categorical → Prop
  | Assumption (c : Categorical) : Deduce [c] c
  | ConvertE : ∀ (S P : Term),
      Deduce [Categorical.E S P] (Categorical.E P S)
  | ConvertI : ∀ (S P : Term),
      Deduce [Categorical.I S P] (Categorical.I P S)
  | Barbara : ∀ (S M P : Term),
      Deduce [Categorical.A M P, Categorical.A S M] (Categorical.A S P)
  | Celarent : ∀ (S M P : Term),
      Deduce [Categorical.E M P, Categorical.A S M] (Categorical.E S P)
  | Cesare : ∀ (S M P : Term),
      Deduce [Categorical.E P M, Categorical.A S M] (Categorical.E S P)
  | Camestres : ∀ (S M P : Term),
      Deduce [Categorical.A P M, Categorical.E S M] (Categorical.E S P)

theorem Deduce.ofSimplyConverts {premise conclusion : Categorical}
    (h : SimplyConverts premise conclusion) :
    Deduce [premise] conclusion := by
  cases h with
  | e S P => exact Deduce.ConvertE S P
  | i S P => exact Deduce.ConvertI S P

theorem e_simply_converts (S P : Term) :
    SimplyConverts (Categorical.E S P) (Categorical.E P S) :=
  .e S P

theorem i_simply_converts (S P : Term) :
    SimplyConverts (Categorical.I S P) (Categorical.I P S) :=
  .i S P

theorem e_converts (S P : Term) :
    Deduce [Categorical.E S P] (Categorical.E P S) :=
  Deduce.ofSimplyConverts (e_simply_converts S P)

theorem i_converts (S P : Term) :
    Deduce [Categorical.I S P] (Categorical.I P S) :=
  Deduce.ofSimplyConverts (i_simply_converts S P)

/--
Closure of Aristotelian deduction under proof-construction from a stock of
premises. `Deduce` records a single valid inferential step; `Derives` records
what can be obtained from available premises by repeatedly using such steps.
-/
inductive Derives : List Categorical → Categorical → Prop
  | premise {premises : List Categorical} {c : Categorical} :
      c ∈ premises → Derives premises c
  | unary {premises : List Categorical} {major conclusion : Categorical} :
      Derives premises major →
      Deduce [major] conclusion →
      Derives premises conclusion
  | binary {premises : List Categorical} {major minor conclusion : Categorical} :
      Derives premises major →
      Derives premises minor →
      Deduce [major, minor] conclusion →
      Derives premises conclusion

theorem Derives.monotone {premises premises' : List Categorical} {conclusion : Categorical}
    (hsub : ∀ {premise : Categorical}, premise ∈ premises → premise ∈ premises') :
    Derives premises conclusion → Derives premises' conclusion := by
  intro h
  induction h with
  | premise hmem =>
      exact Derives.premise (hsub hmem)
  | unary hmajor hstep ih =>
      exact Derives.unary ih hstep
  | binary hmajor hminor hstep ihMajor ihMinor =>
      exact Derives.binary ihMajor ihMinor hstep

theorem Derives.ofDeduce {premises context : List Categorical} {conclusion : Categorical}
    (hctx : ∀ {premise : Categorical}, premise ∈ premises → Derives context premise)
    (h : Deduce premises conclusion) :
    Derives context conclusion := by
  cases h with
  | Assumption c =>
      exact hctx (by simp)
  | ConvertE S P =>
      exact Derives.unary (hctx (by simp)) (Deduce.ConvertE S P)
  | ConvertI S P =>
      exact Derives.unary (hctx (by simp)) (Deduce.ConvertI S P)
  | Barbara S M P =>
      exact Derives.binary (hctx (by simp)) (hctx (by simp)) (Deduce.Barbara S M P)
  | Celarent S M P =>
      exact Derives.binary (hctx (by simp)) (hctx (by simp)) (Deduce.Celarent S M P)
  | Cesare S M P =>
      exact Derives.binary (hctx (by simp)) (hctx (by simp)) (Deduce.Cesare S M P)
  | Camestres S M P =>
      exact Derives.binary (hctx (by simp)) (hctx (by simp)) (Deduce.Camestres S M P)

theorem Derives.fromDeduce {premises : List Categorical} {conclusion : Categorical}
    (h : Deduce premises conclusion) :
    Derives premises conclusion :=
  Derives.ofDeduce (context := premises) (fun hmem => Derives.premise hmem) h

/-- A valid syllogism. -/
structure Syllogism where
  Minor : Term
  Middle : Term
  Major : Term
  major_premise : Categorical
  minor_premise : Categorical
  conclusion : Categorical
  is_valid : Deduce [major_premise, minor_premise] conclusion

/--
Aristotle's figures are organized by the position of the middle term relative
to the extremes. We expose a small API for the assertoric moods currently
modeled.
-/
structure FiguredSyllogism where
  minor : Term
  middle : Term
  major : Term
  mood : Mood

def FiguredSyllogism.majorPremise : FiguredSyllogism → Categorical
  | ⟨_, M, P, .barbara⟩ => .A M P
  | ⟨_, M, P, .celarent⟩ => .E M P
  | ⟨_, M, P, .cesare⟩ => .E P M
  | ⟨_, M, P, .camestres⟩ => .A P M

def FiguredSyllogism.minorPremise : FiguredSyllogism → Categorical
  | ⟨S, M, _, .barbara⟩ => .A S M
  | ⟨S, M, _, .celarent⟩ => .A S M
  | ⟨S, M, _, .cesare⟩ => .A S M
  | ⟨S, M, _, .camestres⟩ => .E S M

def FiguredSyllogism.conclusion : FiguredSyllogism → Categorical
  | ⟨S, _, P, .barbara⟩ => .A S P
  | ⟨S, _, P, .celarent⟩ => .E S P
  | ⟨S, _, P, .cesare⟩ => .E S P
  | ⟨S, _, P, .camestres⟩ => .E S P

def FiguredSyllogism.figure (f : FiguredSyllogism) : Figure :=
  f.mood.figure

def FiguredSyllogism.isPerfect (f : FiguredSyllogism) : Prop :=
  f.figure.IsPerfect

def FiguredSyllogism.toSyllogism (f : FiguredSyllogism) : Syllogism where
  Minor := f.minor
  Middle := f.middle
  Major := f.major
  major_premise := f.majorPremise
  minor_premise := f.minorPremise
  conclusion := f.conclusion
  is_valid := by
    cases f with
    | mk S M P mood =>
        cases mood
        · exact Deduce.Barbara S M P
        · exact Deduce.Celarent S M P
        · exact Deduce.Cesare S M P
        · exact Deduce.Camestres S M P

/--
The first-figure companion through which a modeled syllogism is perfected.
For first-figure moods this is the syllogism itself; for the second figure we
record the first-figure shape reached by conversion.
-/
def FiguredSyllogism.firstFigureCompanion : FiguredSyllogism → FiguredSyllogism
  | ⟨S, M, P, .barbara⟩ => ⟨S, M, P, .barbara⟩
  | ⟨S, M, P, .celarent⟩ => ⟨S, M, P, .celarent⟩
  | ⟨S, M, P, .cesare⟩ => ⟨S, M, P, .celarent⟩
  | ⟨S, M, P, .camestres⟩ => ⟨P, M, S, .celarent⟩

/-- API: core theorem showing the currently modeled figured deduction forms. -/
theorem barbara_is_valid (S M P : Term) :
    Deduce [Categorical.A M P, Categorical.A S M] (Categorical.A S P) :=
  Deduce.Barbara S M P

theorem celarent_is_valid (S M P : Term) :
    Deduce [Categorical.E M P, Categorical.A S M] (Categorical.E S P) :=
  Deduce.Celarent S M P

theorem cesare_is_valid (S M P : Term) :
    Deduce [Categorical.E P M, Categorical.A S M] (Categorical.E S P) :=
  Deduce.Cesare S M P

theorem camestres_is_valid (S M P : Term) :
    Deduce [Categorical.A P M, Categorical.E S M] (Categorical.E S P) :=
  Deduce.Camestres S M P

theorem figuredSyllogism_valid (f : FiguredSyllogism) :
    Deduce [f.majorPremise, f.minorPremise] f.conclusion :=
  f.toSyllogism.is_valid

theorem syllogism_derives (s : Syllogism) :
    Derives [s.major_premise, s.minor_premise] s.conclusion :=
  Derives.fromDeduce s.is_valid

theorem figuredSyllogism_derives (f : FiguredSyllogism) :
    Derives [f.majorPremise, f.minorPremise] f.conclusion :=
  Derives.fromDeduce f.toSyllogism.is_valid

theorem figure_isPerfect_iff_first (g : Figure) : g.IsPerfect ↔ g = .first := by
  cases g <;> simp [Figure.IsPerfect]

theorem mood_isPerfect_iff_first (m : Mood) : m.IsPerfect ↔ m.figure = .first := by
  simpa [Mood.IsPerfect] using figure_isPerfect_iff_first m.figure

theorem firstFigureCompanion_has_first_figure (f : FiguredSyllogism) :
    f.firstFigureCompanion.figure = .first := by
  cases f with
  | mk S M P mood =>
      cases mood <;> rfl

theorem firstFigureCompanion_isPerfect (f : FiguredSyllogism) :
    f.firstFigureCompanion.isPerfect := by
  have hfirst : f.firstFigureCompanion.figure = .first :=
    firstFigureCompanion_has_first_figure f
  exact (figure_isPerfect_iff_first f.firstFigureCompanion.figure).2 hfirst

theorem firstFigureCompanion_eq_self_of_isPerfect (f : FiguredSyllogism)
    (h : f.isPerfect) : f.firstFigureCompanion = f := by
  cases f with
  | mk S M P mood =>
      cases mood
      · rfl
      · rfl
      · cases h
      · cases h

theorem firstFigureCompanion_conclusion_eq_or_swapTerms (f : FiguredSyllogism) :
    f.firstFigureCompanion.conclusion = f.conclusion ∨
      f.firstFigureCompanion.conclusion = f.conclusion.swapTerms := by
  cases f with
  | mk S M P mood =>
      cases mood
      · left; rfl
      · left; rfl
      · left; rfl
      · right; rfl

theorem cesare_firstFigureCompanion_majorPremise_swapTerms (S M P : Term) :
    (FiguredSyllogism.firstFigureCompanion ⟨S, M, P, .cesare⟩).majorPremise =
      (FiguredSyllogism.majorPremise ⟨S, M, P, .cesare⟩).swapTerms := by
  rfl

theorem cesare_firstFigureCompanion_minorPremise (S M P : Term) :
    (FiguredSyllogism.firstFigureCompanion ⟨S, M, P, .cesare⟩).minorPremise =
      (FiguredSyllogism.minorPremise ⟨S, M, P, .cesare⟩) := by
  rfl

theorem cesare_firstFigureCompanion_conclusion (S M P : Term) :
    (FiguredSyllogism.firstFigureCompanion ⟨S, M, P, .cesare⟩).conclusion =
      (FiguredSyllogism.conclusion ⟨S, M, P, .cesare⟩) := by
  rfl

theorem camestres_firstFigureCompanion_majorPremise_swapTerms (S M P : Term) :
    (FiguredSyllogism.firstFigureCompanion ⟨S, M, P, .camestres⟩).majorPremise =
      (FiguredSyllogism.minorPremise ⟨S, M, P, .camestres⟩).swapTerms := by
  rfl

theorem camestres_firstFigureCompanion_minorPremise (S M P : Term) :
    (FiguredSyllogism.firstFigureCompanion ⟨S, M, P, .camestres⟩).minorPremise =
      (FiguredSyllogism.majorPremise ⟨S, M, P, .camestres⟩) := by
  rfl

theorem camestres_firstFigureCompanion_conclusion_swapTerms (S M P : Term) :
    (FiguredSyllogism.firstFigureCompanion ⟨S, M, P, .camestres⟩).conclusion =
      (FiguredSyllogism.conclusion ⟨S, M, P, .camestres⟩).swapTerms := by
  rfl

end Aristotle.PriorAnalytics
