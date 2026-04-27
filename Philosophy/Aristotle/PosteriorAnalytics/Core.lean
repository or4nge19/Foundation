import Philosophy.Aristotle.PosteriorAnalytics.Semantics

namespace Aristotle.PosteriorAnalytics

open Aristotle.PriorAnalytics

abbrev ScientificDefinition := Philosophy.Aristotle.Core.ScientificDefinition
abbrev InquiryAim := Philosophy.Aristotle.Core.InquiryAim

/-!
# Science-Relative Demonstration

Immediacy, first principles, and demonstration are all indexed by a
`Science`. This prevents derivability in some unrelated domain from counting
against the immediacy of a proposition inside the science under study.

`Philosophy/Aristotle/Aristotle.md` gives the governing distinction here:
dialectic can reach preliminary definitions and puzzles, but scientific
knowledge requires causes, better-known premises, and a non-demonstrative grasp
of first principles. The Robin Smith reconstructions in this repo then sharpen
that general guide into science-relative truth, immediacy, and explanatory
demonstration.

The current explanatory-answer and anti-reciprocity layers now track the
currently modeled universal figured moods instead of treating every valid
syllogism as already explanatory.
-/

/--
Fallback immediacy notion for proposition-shapes that do not yet have a more
explicit middle-sensitive treatment.
-/
def UnderivableIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m) (prop : Categorical) : Prop :=
  science.TrueIn prop ∧
    ∀ {premises : List Categorical},
      PremisesTrueIn science premises →
        Derives premises prop →
          prop ∈ premises

/--
A universal affirmative is immediate when every Barbara-style derivation from
science-true premises collapses to a trivial middle identical with one of the
extremes.
-/
def NoNontrivialBarbaraMiddle {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m)
    (lower upper : Term) : Prop :=
  ∀ {premises : List Categorical} {middle : Term},
    PremisesTrueIn science premises →
      Derives premises (Categorical.A middle upper) →
        Derives premises (Categorical.A lower middle) →
          middle = lower ∨ middle = upper

/--
The current explicit form of Aristotelian immediacy for universal
affirmatives.
-/
structure ImmediateAIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m) (lower upper : Term) : Prop where
  true_in : science.TrueIn (Categorical.A lower upper)
  no_nontrivial_middle : NoNontrivialBarbaraMiddle science lower upper

theorem ImmediateAIn.trueIn {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {lower upper : Term}
    (h : ImmediateAIn science lower upper) :
    science.TrueIn (Categorical.A lower upper) :=
  h.true_in

theorem ImmediateAIn.noDistinctMiddle {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {lower upper : Term}
    (h : ImmediateAIn science lower upper) :
    NoNontrivialBarbaraMiddle science lower upper :=
  h.no_nontrivial_middle

theorem immediateAIn_blocks_derivation {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {premises : List Categorical} {lower upper : Term}
    (himm : ImmediateAIn science lower upper)
    (hPremises : PremisesTrueIn science premises)
    (hDerives : Derives premises (Categorical.A lower upper)) :
    Categorical.A lower upper ∈ premises := by
  have hmem :
      ∀ {conclusion : Categorical},
        Derives premises conclusion →
          conclusion = Categorical.A lower upper →
            conclusion ∈ premises := by
    intro conclusion h
    induction h with
    | premise hpremise =>
        intro heq
        simpa [heq] using hpremise
    | unary hmajor hstep ih =>
        intro heq
        cases hstep with
        | Assumption c =>
            exact ih (by simpa using heq)
        | ConvertE => cases heq
        | ConvertI => cases heq
    | binary hmajor hminor hstep ihMajor ihMinor =>
        intro heq
        cases hstep with
        | Barbara S M P =>
            injection heq with hsubject hpredicate
            have hmajor' : Derives premises (Categorical.A M upper) := by
              simpa [hpredicate] using hmajor
            have hminor' : Derives premises (Categorical.A lower M) := by
              simpa [hsubject] using hminor
            have hmiddle : M = lower ∨ M = upper :=
              himm.noDistinctMiddle hPremises hmajor' hminor'
            rcases hmiddle with hMlower | hMupper
            · have hEqMajor : Categorical.A M P = Categorical.A lower upper := by
                simp [hMlower, hpredicate]
              simpa [hsubject, hMlower] using (ihMajor hEqMajor)
            · have hEqMinor : Categorical.A S M = Categorical.A lower upper := by
                simp [hsubject, hMupper]
              simpa [hpredicate, hMupper] using (ihMinor hEqMinor)
        | Celarent => cases heq
        | Cesare => cases heq
        | Camestres => cases heq
  exact hmem hDerives rfl

/--
A universal negative is immediate when none of the currently modeled negative
figures can introduce a genuinely distinct middle between the extremes.
-/
def NoNontrivialCelarentMiddle {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m)
    (lower upper : Term) : Prop :=
  ∀ {premises : List Categorical} {middle : Term},
    PremisesTrueIn science premises →
      Derives premises (Categorical.E middle upper) →
        Derives premises (Categorical.A lower middle) →
          middle = lower ∨ middle = upper

def NoNontrivialCesareMiddle {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m)
    (lower upper : Term) : Prop :=
  ∀ {premises : List Categorical} {middle : Term},
    PremisesTrueIn science premises →
      Derives premises (Categorical.E upper middle) →
        Derives premises (Categorical.A lower middle) →
          middle = lower ∨ middle = upper

def NoNontrivialCamestresMiddle {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m)
    (lower upper : Term) : Prop :=
  ∀ {premises : List Categorical} {middle : Term},
    PremisesTrueIn science premises →
      Derives premises (Categorical.A upper middle) →
        Derives premises (Categorical.E lower middle) →
          middle = lower ∨ middle = upper

/--
The current explicit form of Aristotelian immediacy for universal negatives.
-/
structure ImmediateEIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m) (lower upper : Term) : Prop where
  true_in : science.TrueIn (Categorical.E lower upper)
  no_nontrivial_celarent_middle : NoNontrivialCelarentMiddle science lower upper
  no_nontrivial_cesare_middle : NoNontrivialCesareMiddle science lower upper
  no_nontrivial_camestres_middle : NoNontrivialCamestresMiddle science lower upper

theorem ImmediateEIn.trueIn {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {lower upper : Term}
    (h : ImmediateEIn science lower upper) :
    science.TrueIn (Categorical.E lower upper) :=
  h.true_in

def ImmediateIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m) (prop : Categorical) : Prop :=
  match prop with
  | .A lower upper => ImmediateAIn science lower upper
  | .E lower upper => ImmediateEIn science lower upper
  | .I _ _ => UnderivableIn science prop
  | .O _ _ => UnderivableIn science prop

theorem ImmediateIn.trueIn {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {prop : Categorical}
    (h : ImmediateIn science prop) :
    science.TrueIn prop := by
  cases prop with
  | A lower upper =>
      exact ImmediateAIn.trueIn h
  | E S P =>
      exact ImmediateEIn.trueIn h
  | I S P =>
      exact h.left
  | O S P =>
      exact h.left

theorem immediateAIn_of_noNontrivialBarbaraMiddle
    {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {lower upper : Term}
    (htrue : science.TrueIn (Categorical.A lower upper))
    (hno : NoNontrivialBarbaraMiddle science lower upper) :
    ImmediateAIn science lower upper :=
  ⟨htrue, hno⟩

theorem immediateIn_of_noNontrivialBarbaraMiddle
    {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {lower upper : Term}
    (htrue : science.TrueIn (Categorical.A lower upper))
    (hno : NoNontrivialBarbaraMiddle science lower upper) :
    ImmediateIn science (Categorical.A lower upper) := by
  simpa [ImmediateIn] using
    immediateAIn_of_noNontrivialBarbaraMiddle
      (science := science)
      (lower := lower)
      (upper := upper)
      htrue
      hno

theorem immediateEIn_of_noNontrivialNegativeMiddle
    {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {lower upper : Term}
    (htrue : science.TrueIn (Categorical.E lower upper))
    (hcelarent : NoNontrivialCelarentMiddle science lower upper)
    (hcesare : NoNontrivialCesareMiddle science lower upper)
    (hcamestres : NoNontrivialCamestresMiddle science lower upper) :
    ImmediateEIn science lower upper :=
  ⟨htrue, hcelarent, hcesare, hcamestres⟩

theorem immediateIn_of_noNontrivialNegativeMiddle
    {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {lower upper : Term}
    (htrue : science.TrueIn (Categorical.E lower upper))
    (hcelarent : NoNontrivialCelarentMiddle science lower upper)
    (hcesare : NoNontrivialCesareMiddle science lower upper)
    (hcamestres : NoNontrivialCamestresMiddle science lower upper) :
    ImmediateIn science (Categorical.E lower upper) := by
  simpa [ImmediateIn] using
    immediateEIn_of_noNontrivialNegativeMiddle
      (science := science)
      (lower := lower)
      (upper := upper)
      htrue
      hcelarent
      hcesare
      hcamestres

/--
`MiddleExplainsIn` is the Barbara-specific non-vacuous explanatory witness. It
ties a first-figure affirmative middle to the science's subject matter,
requires both premises to be true in the science, and excludes trivial
identification of the middle with either extreme.
-/
structure MiddleExplainsIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m)
    (minor middle major : Term) : Prop where
  middle_in_subject_matter : middle ∈ science.subjectMatter
  minor_to_middle_true : science.TrueIn (Categorical.A minor middle)
  middle_to_major_true : science.TrueIn (Categorical.A middle major)
  middle_distinct_from_minor : middle ≠ minor
  middle_distinct_from_major : middle ≠ major

theorem MiddleExplainsIn.middle_in_science {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {minor middle major : Term}
    (h : MiddleExplainsIn science minor middle major) :
    middle ∈ science.subjectMatter :=
  h.middle_in_subject_matter

theorem MiddleExplainsIn.minorPremise_true {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {minor middle major : Term}
    (h : MiddleExplainsIn science minor middle major) :
    science.TrueIn (Categorical.A minor middle) :=
  h.minor_to_middle_true

theorem MiddleExplainsIn.majorPremise_true {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {minor middle major : Term}
    (h : MiddleExplainsIn science minor middle major) :
    science.TrueIn (Categorical.A middle major) :=
  h.middle_to_major_true

theorem MiddleExplainsIn.not_vacuous {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {minor middle major : Term}
    (h : MiddleExplainsIn science minor middle major) :
    middle ≠ minor ∧ middle ≠ major :=
  ⟨h.middle_distinct_from_minor, h.middle_distinct_from_major⟩

/--
`UniqueMiddleIn` packages the Smith-style selectivity claim that, for a fixed
pair of extremes in a science, only one middle genuinely explains the
conclusion.
-/
def UniqueMiddleIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m)
    (minor middle major : Term) : Prop :=
  ∀ {candidate : Term}, MiddleExplainsIn science minor candidate major → candidate = middle

namespace UniqueMiddleIn

theorem unique {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {minor middle major candidate : Term}
    (h : UniqueMiddleIn science minor middle major)
    (hexplains : MiddleExplainsIn science minor candidate major) :
    candidate = middle :=
  h hexplains

theorem not_middleExplains_of_ne {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {minor middle major candidate : Term}
    (h : UniqueMiddleIn science minor middle major)
    (hneq : candidate ≠ middle) :
    ¬ MiddleExplainsIn science minor candidate major := by
  intro hexplains
  exact hneq (h hexplains)

/-- Any two `MiddleExplainsIn` for the same extremes under a `UniqueMiddleIn` constraint
share the same middle: the selectivity pin is the *formal* content of "the" cause in
the Smith layer (compare `UniqueExplanatoryMiddleIn` for figured syllogisms). -/
theorem middle_eq_of_middleExplains {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {minor u major m1 m2 : Term}
    (h : UniqueMiddleIn science minor u major)
    (e1 : MiddleExplainsIn science minor m1 major) (e2 : MiddleExplainsIn science minor m2 major) :
    m1 = m2 :=
  (h e1).trans (h e2).symm

end UniqueMiddleIn

/--
`ExplanatorySyllogismIn` generalizes the explanatory witness from Barbara alone
to any figured syllogism currently modeled by the proof theory. The syllogism's
own mood determines whether the explanation is affirmative or negative.
-/
structure ExplanatorySyllogismIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m)
    (figured : FiguredSyllogism) : Prop where
  middle_in_subject_matter : figured.middle ∈ science.subjectMatter
  major_premise_true : science.TrueIn figured.majorPremise
  minor_premise_true : science.TrueIn figured.minorPremise
  middle_distinct_from_minor : figured.middle ≠ figured.minor
  middle_distinct_from_major : figured.middle ≠ figured.major

namespace MiddleExplainsIn

def toExplanatorySyllogismIn {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {minor middle major : Term}
    (h : MiddleExplainsIn science minor middle major) :
    ExplanatorySyllogismIn science
      { minor := minor
        middle := middle
        major := major
        mood := .barbara } where
  middle_in_subject_matter := h.middle_in_subject_matter
  major_premise_true := h.middle_to_major_true
  minor_premise_true := h.minor_to_middle_true
  middle_distinct_from_minor := h.middle_distinct_from_minor
  middle_distinct_from_major := h.middle_distinct_from_major

end MiddleExplainsIn

namespace ExplanatorySyllogismIn

def toMiddleExplains_of_barbara {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {minor middle major : Term}
    (h : ExplanatorySyllogismIn science
      { minor := minor
        middle := middle
        major := major
        mood := .barbara }) :
    MiddleExplainsIn science minor middle major where
  middle_in_subject_matter := h.middle_in_subject_matter
  minor_to_middle_true := h.minor_premise_true
  middle_to_major_true := h.major_premise_true
  middle_distinct_from_minor := h.middle_distinct_from_minor
  middle_distinct_from_major := h.middle_distinct_from_major

end ExplanatorySyllogismIn

/--
`UniqueExplanatoryMiddleIn` lifts middle-selectivity to the figured explanatory
layer: among explanations with the same mood and conclusion, the middle is
fixed.
-/
def UniqueExplanatoryMiddleIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m)
    (figured : FiguredSyllogism) : Prop :=
  ∀ {candidate : FiguredSyllogism},
    candidate.mood = figured.mood →
      candidate.conclusion = figured.conclusion →
        ExplanatorySyllogismIn science candidate →
          candidate.middle = figured.middle

namespace UniqueExplanatoryMiddleIn

theorem unique {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {figured candidate : FiguredSyllogism}
    (h : UniqueExplanatoryMiddleIn science figured)
    (hmood : candidate.mood = figured.mood)
    (hconclusion : candidate.conclusion = figured.conclusion)
    (hexplains : ExplanatorySyllogismIn science candidate) :
    candidate.middle = figured.middle :=
  h hmood hconclusion hexplains

/-- Two **explanatory** figured syllogisms with the same mood and conclusion as a
`UniqueExplanatoryMiddleIn` pattern share a middle: they both collapse to the
same distinguished middle against `figured` (the Smith layer's “**the** middle
term” for that explanatory shape, prior to the causal lift). -/
theorem figured_middle_eq_of_explanatory {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {figured c1 c2 : FiguredSyllogism}
    (h : UniqueExplanatoryMiddleIn science figured)
    (hm1 : c1.mood = figured.mood) (hc1 : c1.conclusion = figured.conclusion)
    (hex1 : ExplanatorySyllogismIn science c1)
    (hm2 : c2.mood = figured.mood) (hc2 : c2.conclusion = figured.conclusion)
    (hex2 : ExplanatorySyllogismIn science c2) :
    c1.middle = c2.middle :=
  (h hm1 hc1 hex1).trans (h hm2 hc2 hex2).symm

theorem of_barbara_uniqueMiddle {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {minor middle major : Term}
    (h : UniqueMiddleIn science minor middle major) :
    UniqueExplanatoryMiddleIn science
      { minor := minor, middle := middle, major := major, mood := .barbara } := by
  intro candidate hmood hconclusion hexplains
  cases candidate with
  | mk cminor cmiddle cmajor cmood =>
      cases cmood <;> cases hmood
      change Categorical.A cminor cmajor = Categorical.A minor major at hconclusion
      injection hconclusion with hminor hmajor
      have hmiddle : MiddleExplainsIn science minor cmiddle major := by
        simpa [hminor, hmajor] using
          (ExplanatorySyllogismIn.toMiddleExplains_of_barbara hexplains)
      exact h hmiddle

end UniqueExplanatoryMiddleIn

/--
`WhyQuestion` packages the demonstrative target "why does this predicate belong to
this subject?" Unlike the dialectical `Problem`, it is answered only when a
middle-bearing syllogism is exhibited. The current layer handles universal
affirmative and universal negative conclusions.
-/
structure WhyQuestion where
  subject : Term
  predicate : Term
  quality : Quality := .affirmative
  deriving DecidableEq, Repr

namespace WhyQuestion

def aim (_question : WhyQuestion) : InquiryAim :=
  .dioti

def conclusion (question : WhyQuestion) : Categorical :=
  match question.quality with
  | .affirmative => .A question.subject question.predicate
  | .negative => .E question.subject question.predicate

def ofConclusion (conclusion : Categorical) : WhyQuestion :=
  { subject := conclusion.subject
    predicate := conclusion.predicate
    quality := conclusion.quality }

theorem dioti_only (question : WhyQuestion) : question.aim = .dioti := by
  rfl

@[simp] theorem ofConclusion_conclusion_A (subject predicate : Term) :
    (ofConclusion (Categorical.A subject predicate)).conclusion =
      Categorical.A subject predicate := by
  rfl

@[simp] theorem ofConclusion_conclusion_E (subject predicate : Term) :
    (ofConclusion (Categorical.E subject predicate)).conclusion =
      Categorical.E subject predicate := by
  rfl

end WhyQuestion

def AnswersWhyIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m) (question : WhyQuestion) : Prop :=
  ∃ figured : FiguredSyllogism,
    figured.conclusion = question.conclusion ∧
      ExplanatorySyllogismIn science figured

structure Nous {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m) (prop : Categorical) : Prop where
  immediate : ImmediateIn science prop

theorem Nous.trueIn {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {prop : Categorical}
    (h : Nous science prop) :
    science.TrueIn prop :=
  h.immediate.trueIn

theorem Nous.immediateIn {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {prop : Categorical}
    (h : Nous science prop) :
    ImmediateIn science prop :=
  h.immediate

def FirstPrinciples {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m) (premises : List Categorical) : Prop :=
  ∀ ⦃premise : Categorical⦄, premise ∈ premises → Nous science premise

theorem FirstPrinciples.of_mem {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {premises : List Categorical} {premise : Categorical}
    (h : FirstPrinciples science premises) (hmem : premise ∈ premises) :
    Nous science premise :=
  h hmem

/--
The categorical commitments carried by a scientific definition when applied to a
subject term inside a science.
-/
def ScientificDefinitionStatements
    (subject : Term) (definition : ScientificDefinition) : List Categorical :=
  Categorical.A subject definition.genus ::
    definition.differentiae.map (fun differentia => Categorical.A subject differentia)

/--
A scientific definition is stronger than a dialectical candidate account. In the
current development, it belongs to a science only when its defining
genus/differentia claims function there as first principles.
-/
structure ScientificDefinitionIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m) (subject : Term) where
  definition : ScientificDefinition
  nonempty : definition.IsNonempty
  first_principles :
    FirstPrinciples science (ScientificDefinitionStatements subject definition)

namespace ScientificDefinitionIn

def statements {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {subject : Term}
    (h : ScientificDefinitionIn science subject) : List Categorical :=
  ScientificDefinitionStatements subject h.definition

theorem genus_statement_mem {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {subject : Term}
    (h : ScientificDefinitionIn science subject) :
    Categorical.A subject h.definition.genus ∈ h.statements := by
  simp [statements, ScientificDefinitionStatements]

theorem differentia_statement_mem {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {subject : Term}
    (h : ScientificDefinitionIn science subject)
    {differentia : Term}
    (hmem : differentia ∈ h.definition.differentiae) :
    Categorical.A subject differentia ∈ h.statements := by
  simp [statements, ScientificDefinitionStatements, hmem]

theorem genus_nous {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {subject : Term}
    (h : ScientificDefinitionIn science subject) :
    Nous science (Categorical.A subject h.definition.genus) :=
  h.first_principles h.genus_statement_mem

theorem differentia_nous {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {subject : Term}
    (h : ScientificDefinitionIn science subject)
    {differentia : Term}
    (hmem : differentia ∈ h.definition.differentiae) :
    Nous science (Categorical.A subject differentia) :=
  h.first_principles (h.differentia_statement_mem hmem)

theorem subject_in_subject_matter {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {subject : Term}
    (h : ScientificDefinitionIn science subject) :
    subject ∈ science.subjectMatter :=
  science.subject_mem_of_trueIn h.genus_nous.trueIn

theorem genus_in_subject_matter {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {subject : Term}
    (h : ScientificDefinitionIn science subject) :
    h.definition.genus ∈ science.subjectMatter :=
  science.predicate_mem_of_trueIn h.genus_nous.trueIn

theorem differentia_in_subject_matter {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {subject : Term}
    (h : ScientificDefinitionIn science subject)
    {differentia : Term}
    (hmem : differentia ∈ h.definition.differentiae) :
    differentia ∈ science.subjectMatter :=
  science.predicate_mem_of_trueIn (h.differentia_nous hmem).trueIn

end ScientificDefinitionIn

/--
`PerSePredicationIn` currently records the first Smith-style per-se case: the
predicate belongs to the subject because it occurs in the subject's scientific
definition. The second kind, where the subject enters the predicate's
definition, remains future work.
-/
inductive PerSePredicationIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m) (subject : Term) : Term → Prop
  | ofGenus (scientific_definition : ScientificDefinitionIn science subject) :
      PerSePredicationIn science subject scientific_definition.definition.genus
  | ofDifferentia (scientific_definition : ScientificDefinitionIn science subject)
      {differentia : Term}
      (hmem : differentia ∈ scientific_definition.definition.differentiae) :
      PerSePredicationIn science subject differentia

namespace PerSePredicationIn

theorem nous {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {subject predicate : Term}
    (h : PerSePredicationIn science subject predicate) :
    Nous science (Categorical.A subject predicate) := by
  cases h with
  | ofGenus scientific_definition =>
      simpa using scientific_definition.genus_nous
  | ofDifferentia scientific_definition hmem =>
      exact scientific_definition.differentia_nous hmem

theorem trueIn {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {subject predicate : Term}
    (h : PerSePredicationIn science subject predicate) :
    science.TrueIn (Categorical.A subject predicate) :=
  h.nous.trueIn

theorem predicate_in_subject_matter {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {subject predicate : Term}
    (h : PerSePredicationIn science subject predicate) :
    predicate ∈ science.subjectMatter := by
  exact science.predicate_mem_of_trueIn h.trueIn

end PerSePredicationIn

/--
`SecondPerSePredicationIn` records Smith's second per-se case: the subject
enters the scientific definition of the predicate. This does not by itself
yield a universal affirmative first principle, but it matters for tracking the
definitional background of demonstrative predicates.
-/
inductive SecondPerSePredicationIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m) (subject : Term) : Term → Prop
  | ofPredicateGenus {predicate : Term}
      (scientific_definition : ScientificDefinitionIn science predicate)
      (hgenus : scientific_definition.definition.genus = subject) :
      SecondPerSePredicationIn science subject predicate
  | ofPredicateDifferentia {predicate : Term}
      (scientific_definition : ScientificDefinitionIn science predicate)
      (hmem : subject ∈ scientific_definition.definition.differentiae) :
      SecondPerSePredicationIn science subject predicate

namespace SecondPerSePredicationIn

theorem predicate_in_subject_matter {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {subject predicate : Term}
    (h : SecondPerSePredicationIn science subject predicate) :
    predicate ∈ science.subjectMatter := by
  cases h with
  | ofPredicateGenus scientific_definition _ =>
      exact scientific_definition.subject_in_subject_matter
  | ofPredicateDifferentia scientific_definition _ =>
      exact scientific_definition.subject_in_subject_matter

theorem subject_in_subject_matter {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {subject predicate : Term}
    (h : SecondPerSePredicationIn science subject predicate) :
    subject ∈ science.subjectMatter := by
  cases h with
  | ofPredicateGenus scientific_definition hgenus =>
      simpa [hgenus] using scientific_definition.genus_in_subject_matter
  | ofPredicateDifferentia scientific_definition hmem =>
      exact scientific_definition.differentia_in_subject_matter hmem

end SecondPerSePredicationIn

/--
`IsCauseOf` is the currently modeled causal witness for a perfected
first-figure demonstration. It is intentionally stricter than a bare
explanatory middle:

- the syllogism must already be in a perfected first-figure form
- the subject must fall under the middle *per se* through scientific definition
- the major premise must itself be a first principle in the science

Second-kind per-se predication is tracked separately below the level of
first-principled universal premises; second-figure moods count as causal only
through their perfected first-figure companion.
-/
structure IsCauseOf {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m) (figured : FiguredSyllogism) : Prop where
  perfect : figured.isPerfect
  minor_per_se : PerSePredicationIn science figured.minor figured.middle
  major_principle : Nous science figured.majorPremise

namespace IsCauseOf

theorem minorPremise_nous {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {figured : FiguredSyllogism}
    (h : IsCauseOf science figured) :
    Nous science (Categorical.A figured.minor figured.middle) :=
  h.minor_per_se.nous

theorem minorPremise_trueIn {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {figured : FiguredSyllogism}
    (h : IsCauseOf science figured) :
    science.TrueIn (Categorical.A figured.minor figured.middle) :=
  h.minor_per_se.trueIn

theorem majorPremise_nous {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {figured : FiguredSyllogism}
    (h : IsCauseOf science figured) :
    Nous science figured.majorPremise :=
  h.major_principle

end IsCauseOf

/--
`CausalExplanatorySyllogismIn` strengthens the figured explanatory witness by
requiring the route to be causal in the stricter, definition-grounded sense
captured by `IsCauseOf`. For second-figure moods this causal route is carried by
the perfected first-figure companion.
-/
structure CausalExplanatorySyllogismIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m)
    (figured : FiguredSyllogism) : Prop where
  explanatory : ExplanatorySyllogismIn science figured
  companion_cause : IsCauseOf science figured.firstFigureCompanion

def AnswersWhyThroughCauseIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m) (question : WhyQuestion) : Prop :=
  ∃ figured : FiguredSyllogism,
    figured.conclusion = question.conclusion ∧
      CausalExplanatorySyllogismIn science figured

namespace CausalExplanatorySyllogismIn

theorem explanatoryWitness {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {figured : FiguredSyllogism}
    (h : CausalExplanatorySyllogismIn science figured) :
    ExplanatorySyllogismIn science figured :=
  h.explanatory

theorem companionCause {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {figured : FiguredSyllogism}
    (h : CausalExplanatorySyllogismIn science figured) :
    IsCauseOf science figured.firstFigureCompanion :=
  h.companion_cause

theorem answersWhyThroughCause {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {figured : FiguredSyllogism}
    (h : CausalExplanatorySyllogismIn science figured) :
    AnswersWhyThroughCauseIn science (WhyQuestion.ofConclusion figured.conclusion) := by
  refine ⟨figured, ?_, h⟩
  cases figured with
  | mk minor middle major mood =>
      cases mood <;> rfl

theorem answersWhy {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {figured : FiguredSyllogism}
    (h : CausalExplanatorySyllogismIn science figured) :
    AnswersWhyIn science (WhyQuestion.ofConclusion figured.conclusion) := by
  rcases h.answersWhyThroughCause with ⟨figured, hconclusion, hcausal⟩
  exact ⟨figured, hconclusion, hcausal.explanatoryWitness⟩

end CausalExplanatorySyllogismIn

/--
`UniqueCausalMiddleIn` is the causal analogue of `UniqueExplanatoryMiddleIn`:
once the explanatory route is strengthened into a causal one, the middle is
still fixed under the same mood and conclusion.
-/
def UniqueCausalMiddleIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m)
    (figured : FiguredSyllogism) : Prop :=
  ∀ {candidate : FiguredSyllogism},
    candidate.mood = figured.mood →
      candidate.conclusion = figured.conclusion →
        CausalExplanatorySyllogismIn science candidate →
          candidate.middle = figured.middle

namespace UniqueCausalMiddleIn

theorem unique {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {figured candidate : FiguredSyllogism}
    (h : UniqueCausalMiddleIn science figured)
    (hmood : candidate.mood = figured.mood)
    (hconclusion : candidate.conclusion = figured.conclusion)
    (hcausal : CausalExplanatorySyllogismIn science candidate) :
    candidate.middle = figured.middle :=
  h hmood hconclusion hcausal

theorem figured_middle_eq_of_causal {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {figured c1 c2 : FiguredSyllogism}
    (h : UniqueCausalMiddleIn science figured)
    (hm1 : c1.mood = figured.mood) (hc1 : c1.conclusion = figured.conclusion)
    (hca1 : CausalExplanatorySyllogismIn science c1)
    (hm2 : c2.mood = figured.mood) (hc2 : c2.conclusion = figured.conclusion)
    (hca2 : CausalExplanatorySyllogismIn science c2) :
    c1.middle = c2.middle :=
  (h hm1 hc1 hca1).trans (h hm2 hc2 hca2).symm

theorem of_uniqueExplanatory {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {figured : FiguredSyllogism}
    (h : UniqueExplanatoryMiddleIn science figured) :
    UniqueCausalMiddleIn science figured := by
  intro candidate hmood hconclusion hcausal
  exact h hmood hconclusion hcausal.explanatoryWitness

theorem of_barbara_uniqueMiddle {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {minor middle major : Term}
    (h : UniqueMiddleIn science minor middle major) :
    UniqueCausalMiddleIn science
      { minor := minor, middle := middle, major := major, mood := .barbara } :=
  of_uniqueExplanatory (UniqueExplanatoryMiddleIn.of_barbara_uniqueMiddle h)

end UniqueCausalMiddleIn

/--
`CompanionCausalRouteIn` records the explicitly second-per-se background through
which a non-perfect figured syllogism inherits causal force from its perfected
first-figure companion.
-/
structure CompanionCausalRouteIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m)
    (figured : FiguredSyllogism) : Prop where
  second_per_se :
    SecondPerSePredicationIn science figured.firstFigureCompanion.middle
      figured.firstFigureCompanion.minor
  companion_cause : IsCauseOf science figured.firstFigureCompanion

namespace CompanionCausalRouteIn

theorem middle_in_subject_matter {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {figured : FiguredSyllogism}
    (h : CompanionCausalRouteIn science figured) :
    figured.firstFigureCompanion.middle ∈ science.subjectMatter :=
  h.second_per_se.subject_in_subject_matter

theorem companionMinor_in_subject_matter {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {figured : FiguredSyllogism}
    (h : CompanionCausalRouteIn science figured) :
    figured.firstFigureCompanion.minor ∈ science.subjectMatter :=
  h.second_per_se.predicate_in_subject_matter

def ofCausalExplanatorySyllogismIn {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {figured : FiguredSyllogism}
    (hcausal : CausalExplanatorySyllogismIn science figured)
    (hsecond : SecondPerSePredicationIn science figured.firstFigureCompanion.middle
      figured.firstFigureCompanion.minor) :
    CompanionCausalRouteIn science figured where
  second_per_se := hsecond
  companion_cause := hcausal.companionCause

theorem cesare_of_causalExplanatorySyllogismIn
    {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {minor middle major : Term}
    (hcausal : CausalExplanatorySyllogismIn science
      { minor := minor, middle := middle, major := major, mood := .cesare })
    (hsecond : SecondPerSePredicationIn science middle minor) :
    CompanionCausalRouteIn science
      { minor := minor, middle := middle, major := major, mood := .cesare } := by
  simpa [FiguredSyllogism.firstFigureCompanion] using
    (ofCausalExplanatorySyllogismIn hcausal hsecond)

theorem camestres_of_causalExplanatorySyllogismIn
    {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {minor middle major : Term}
    (hcausal : CausalExplanatorySyllogismIn science
      { minor := minor, middle := middle, major := major, mood := .camestres })
    (hsecond : SecondPerSePredicationIn science middle major) :
    CompanionCausalRouteIn science
      { minor := minor, middle := middle, major := major, mood := .camestres } := by
  simpa [FiguredSyllogism.firstFigureCompanion] using
    (ofCausalExplanatorySyllogismIn hcausal hsecond)

def toCausalExplanatorySyllogismIn {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {figured : FiguredSyllogism}
    (h : CompanionCausalRouteIn science figured)
    (hexplains : ExplanatorySyllogismIn science figured) :
    CausalExplanatorySyllogismIn science figured where
  explanatory := hexplains
  companion_cause := h.companion_cause

theorem answersWhyThroughCause {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {figured : FiguredSyllogism}
    (h : CompanionCausalRouteIn science figured)
    (hexplains : ExplanatorySyllogismIn science figured) :
    AnswersWhyThroughCauseIn science (WhyQuestion.ofConclusion figured.conclusion) := by
  exact (h.toCausalExplanatorySyllogismIn hexplains).answersWhyThroughCause

theorem cesare_answersWhyThroughCompanionRoute
    {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {minor middle major : Term}
    (h : CompanionCausalRouteIn science
      { minor := minor, middle := middle, major := major, mood := .cesare })
    (hexplains : ExplanatorySyllogismIn science
      { minor := minor, middle := middle, major := major, mood := .cesare }) :
    AnswersWhyThroughCauseIn science
      (WhyQuestion.ofConclusion (Categorical.E minor major)) := by
  simpa using h.answersWhyThroughCause hexplains

theorem camestres_answersWhyThroughCompanionRoute
    {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {minor middle major : Term}
    (h : CompanionCausalRouteIn science
      { minor := minor, middle := middle, major := major, mood := .camestres })
    (hexplains : ExplanatorySyllogismIn science
      { minor := minor, middle := middle, major := major, mood := .camestres }) :
    AnswersWhyThroughCauseIn science
      (WhyQuestion.ofConclusion (Categorical.E minor major)) := by
  simpa using h.answersWhyThroughCause hexplains

end CompanionCausalRouteIn

def NonCircular {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m)
    (premises : List Categorical) (conclusion : Categorical) : Prop :=
  science.TrueIn conclusion ∧ conclusion ∉ premises

/--
`DemonstrativeExpansionIn` records the currently modeled one-step
demonstrative-expansion moves from either premise of an explanatory figured
syllogism to its conclusion. It now matches the same universal moods already
carried by `ExplanatorySyllogismIn`.
-/
inductive DemonstrativeExpansionIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m) : Categorical → Categorical → Prop
  | barbaraMajor {S M P : Term}
      (hexplains : ExplanatorySyllogismIn science
        { minor := S
          middle := M
          major := P
          mood := .barbara }) :
      DemonstrativeExpansionIn science (Categorical.A M P) (Categorical.A S P)
  | barbaraMinor {S M P : Term}
      (hexplains : ExplanatorySyllogismIn science
        { minor := S
          middle := M
          major := P
          mood := .barbara }) :
      DemonstrativeExpansionIn science (Categorical.A S M) (Categorical.A S P)
  | celarentMajor {S M P : Term}
      (hexplains : ExplanatorySyllogismIn science
        { minor := S
          middle := M
          major := P
          mood := .celarent }) :
      DemonstrativeExpansionIn science (Categorical.E M P) (Categorical.E S P)
  | celarentMinor {S M P : Term}
      (hexplains : ExplanatorySyllogismIn science
        { minor := S
          middle := M
          major := P
          mood := .celarent }) :
      DemonstrativeExpansionIn science (Categorical.A S M) (Categorical.E S P)
  | cesareMajor {S M P : Term}
      (hexplains : ExplanatorySyllogismIn science
        { minor := S
          middle := M
          major := P
          mood := .cesare }) :
      DemonstrativeExpansionIn science (Categorical.E P M) (Categorical.E S P)
  | cesareMinor {S M P : Term}
      (hexplains : ExplanatorySyllogismIn science
        { minor := S
          middle := M
          major := P
          mood := .cesare }) :
      DemonstrativeExpansionIn science (Categorical.A S M) (Categorical.E S P)
  | camestresMajor {S M P : Term}
      (hexplains : ExplanatorySyllogismIn science
        { minor := S
          middle := M
          major := P
          mood := .camestres }) :
      DemonstrativeExpansionIn science (Categorical.A P M) (Categorical.E S P)
  | camestresMinor {S M P : Term}
      (hexplains : ExplanatorySyllogismIn science
        { minor := S
          middle := M
          major := P
          mood := .camestres }) :
      DemonstrativeExpansionIn science (Categorical.E S M) (Categorical.E S P)

namespace DemonstrativeExpansionIn

theorem exists_premiseExpansion {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {premise conclusion : Categorical}
    (h : DemonstrativeExpansionIn science premise conclusion) :
    ∃ next, premise ∈ next ∧ PremiseExpansion [conclusion] next := by
  cases h with
  | @barbaraMajor S M P hexplains =>
      refine ⟨[Categorical.A M P, Categorical.A S M], by simp, ?_⟩
      simpa using premiseExpansion_barbara [] [] S M P
  | @barbaraMinor S M P hexplains =>
      refine ⟨[Categorical.A M P, Categorical.A S M], by simp, ?_⟩
      simpa using premiseExpansion_barbara [] [] S M P
  | @celarentMajor S M P hexplains =>
      refine ⟨[Categorical.E M P, Categorical.A S M], by simp, ?_⟩
      simpa using premiseExpansion_celarent [] [] S M P
  | @celarentMinor S M P hexplains =>
      refine ⟨[Categorical.E M P, Categorical.A S M], by simp, ?_⟩
      simpa using premiseExpansion_celarent [] [] S M P
  | @cesareMajor S M P hexplains =>
      refine ⟨[Categorical.E P M, Categorical.A S M], by simp, ?_⟩
      simpa using premiseExpansion_cesare [] [] S M P
  | @cesareMinor S M P hexplains =>
      refine ⟨[Categorical.E P M, Categorical.A S M], by simp, ?_⟩
      simpa using premiseExpansion_cesare [] [] S M P
  | @camestresMajor S M P hexplains =>
      refine ⟨[Categorical.A P M, Categorical.E S M], by simp, ?_⟩
      simpa using premiseExpansion_camestres [] [] S M P
  | @camestresMinor S M P hexplains =>
      refine ⟨[Categorical.A P M, Categorical.E S M], by simp, ?_⟩
      simpa using premiseExpansion_camestres [] [] S M P

theorem exists_premiseExpansionReachable {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {premise conclusion : Categorical}
    (h : DemonstrativeExpansionIn science premise conclusion) :
    ∃ next, premise ∈ next ∧ Relation.ReflTransGen PremiseExpansion [conclusion] next := by
  rcases h.exists_premiseExpansion with ⟨next, hmem, hstep⟩
  exact ⟨next, hmem, Relation.ReflTransGen.tail Relation.ReflTransGen.refl hstep⟩

end DemonstrativeExpansionIn

def ExpansionReachableIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m) :
    Categorical → Categorical → Prop :=
  Relation.ReflTransGen (DemonstrativeExpansionIn science)

theorem ExpansionReachableIn.trans {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {a b c : Categorical} (hab : ExpansionReachableIn science a b)
    (hbc : ExpansionReachableIn science b c) : ExpansionReachableIn science a c :=
  Relation.ReflTransGen.trans hab hbc

theorem ExpansionReachableIn.refl {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} (a : Categorical) : ExpansionReachableIn science a a :=
  Relation.ReflTransGen.refl

theorem DemonstrativeExpansionIn.reachable {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {premise conclusion : Categorical}
    (h : DemonstrativeExpansionIn science premise conclusion) :
    ExpansionReachableIn science premise conclusion :=
  Relation.ReflTransGen.tail Relation.ReflTransGen.refl h

theorem DemonstrativeExpansionIn.reachable_trans {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {premise mid conclusion : Categorical}
    (h : DemonstrativeExpansionIn science premise mid) (hrest : ExpansionReachableIn science mid conclusion) :
    ExpansionReachableIn science premise conclusion :=
  (DemonstrativeExpansionIn.reachable h).trans hrest

private theorem reflTransGen_eq_or_step
    {α : Type} {R : α → α → Prop} {start target : α}
    (h : Relation.ReflTransGen R start target) :
    start = target ∨ ∃ next, R start next ∧ Relation.ReflTransGen R next target := by
  induction h with
  | refl =>
      exact Or.inl rfl
  | @tail y z hxy hyz ih =>
      rcases ih with rfl | ⟨next, hstep, hrest⟩
      · exact Or.inr ⟨z, hyz, Relation.ReflTransGen.refl⟩
      · exact Or.inr ⟨next, hstep, Relation.ReflTransGen.tail hrest hyz⟩

theorem expansionReachableIn_eq_or_step {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {source target : Categorical}
    (h : ExpansionReachableIn science source target) :
    source = target ∨
      ∃ next,
        DemonstrativeExpansionIn science source next ∧
          ExpansionReachableIn science next target :=
  reflTransGen_eq_or_step h

def NonReciprocalIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m)
    (premises : List Categorical) (conclusion : Categorical) : Prop :=
  science.TrueIn conclusion ∧
    ∀ ⦃premise : Categorical⦄,
      premise ∈ premises →
        science.TrueIn premise →
          ¬ ExpansionReachableIn science conclusion premise

abbrev NonReciprocal {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m)
    (premises : List Categorical) (conclusion : Categorical) : Prop :=
  NonReciprocalIn science premises conclusion

theorem NonReciprocalIn.noncircular {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {premises : List Categorical} {conclusion : Categorical}
    (h : NonReciprocalIn science premises conclusion) :
    NonCircular science premises conclusion := by
  refine ⟨h.left, ?_⟩
  intro hmem
  exact h.right (premise := conclusion) hmem h.left Relation.ReflTransGen.refl

def SupportsConclusionIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m)
    (premises : List Categorical) (conclusion : Categorical) : Prop :=
  PremisesTrueIn science premises ∧ Derives premises conclusion

def PremiseIrredundantIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m)
    (premises : List Categorical) (conclusion : Categorical) : Prop :=
  ∀ ⦃premise : Categorical⦄,
    premise ∈ premises →
      ¬ SupportsConclusionIn science (premises.erase premise) conclusion

/--
`DemonstrativeBasisIn` isolates the Smith-style idea that a demonstrative
conclusion rests on first principles which genuinely support it inside a
science, even before we ask whether those principles are minimal.
-/
structure DemonstrativeBasisIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m)
    (premises : List Categorical) (conclusion : Categorical) : Prop where
  first_principles : FirstPrinciples science premises
  conclusion_admissible : science.admits conclusion
  derives : Derives premises conclusion

namespace DemonstrativeBasisIn

theorem premisesTrueIn {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {premises : List Categorical} {conclusion : Categorical}
    (h : DemonstrativeBasisIn science premises conclusion) :
    PremisesTrueIn science premises := by
  intro premise hmem
  exact (h.first_principles hmem).trueIn

theorem supports {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {premises : List Categorical} {conclusion : Categorical}
    (h : DemonstrativeBasisIn science premises conclusion) :
    SupportsConclusionIn science premises conclusion :=
  ⟨h.premisesTrueIn, h.derives⟩

theorem conclusionTrueIn {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {premises : List Categorical} {conclusion : Categorical}
    (h : DemonstrativeBasisIn science premises conclusion) :
    science.TrueIn conclusion := by
  refine ⟨h.conclusion_admissible, ?_⟩
  exact omnitemporal_of_derives
    (fun {_} hmem => (h.premisesTrueIn hmem).right)
    h.derives

end DemonstrativeBasisIn

structure MinimalDemonstrativeBasisIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m)
    (premises : List Categorical) (conclusion : Categorical) : Prop
    extends DemonstrativeBasisIn science premises conclusion where
  irredundant : PremiseIrredundantIn science premises conclusion

namespace DemonstrativeBasisIn

def minimal {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {premises : List Categorical} {conclusion : Categorical}
    (h : DemonstrativeBasisIn science premises conclusion)
    (hirr : PremiseIrredundantIn science premises conclusion) :
    MinimalDemonstrativeBasisIn science premises conclusion where
  first_principles := h.first_principles
  conclusion_admissible := h.conclusion_admissible
  derives := h.derives
  irredundant := hirr

end DemonstrativeBasisIn

/--
`Demonstration` is stricter than valid syllogism. It requires first-principle
premises, anti-reciprocity within a science, and a non-vacuous explanatory
figured syllogism. This keeps the Menn/Smith distinction between mere validity
and explanatory knowledge visible in the type itself even once the current
layer moves beyond Barbara alone.
-/
structure Demonstration (Model : Type) [Interpretation Model]
    {m : Model} (science : Science Model m) where
  figured : FiguredSyllogism
  conclusion_admissible : science.admits figured.conclusion
  major_principle : Nous science figured.majorPremise
  minor_principle : Nous science figured.minorPremise
  nonreciprocal :
    NonReciprocalIn science [figured.majorPremise, figured.minorPremise] figured.conclusion
  explains : ExplanatorySyllogismIn science figured

def Demonstration.premises {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    (d : Demonstration Model science) : List Categorical :=
  [d.figured.majorPremise, d.figured.minorPremise]

def Demonstration.conclusion {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    (d : Demonstration Model science) : Categorical :=
  d.figured.conclusion

def Demonstration.whyQuestion {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    (d : Demonstration Model science) : WhyQuestion :=
  { subject := d.figured.minor
    predicate := d.figured.major
    quality := d.figured.conclusion.quality }

def Demonstration.syllogism {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    (d : Demonstration Model science) : Syllogism :=
  d.figured.toSyllogism

def Demonstration.premisesTrueIn {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    (d : Demonstration Model science) : PremisesTrueIn science d.premises := by
  intro premise hmem
  have hpair : premise = d.figured.majorPremise ∨ premise = d.figured.minorPremise := by
    simpa [Demonstration.premises] using hmem
  rcases hpair with rfl | rfl
  · exact d.major_principle.trueIn
  · exact d.minor_principle.trueIn

def Demonstration.firstPrinciples {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    (d : Demonstration Model science) : FirstPrinciples science d.premises := by
  intro premise hmem
  have hpair : premise = d.figured.majorPremise ∨ premise = d.figured.minorPremise := by
    simpa [Demonstration.premises] using hmem
  rcases hpair with rfl | rfl
  · exact d.major_principle
  · exact d.minor_principle

theorem Demonstration.answersWhy {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    (d : Demonstration Model science) :
    AnswersWhyIn science d.whyQuestion := by
  cases d with
  | mk figured conclusion_admissible major_principle minor_principle nonreciprocal explains =>
      refine ⟨figured, ?_, explains⟩
      cases figured with
      | mk minor middle major mood =>
          cases mood <;> rfl

def Demonstration.basis {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    (d : Demonstration Model science) :
    DemonstrativeBasisIn science d.premises d.conclusion where
  first_principles := d.firstPrinciples
  conclusion_admissible := d.conclusion_admissible
  derives := by
    simpa [Demonstration.premises, Demonstration.conclusion, Demonstration.syllogism] using
      (Derives.fromDeduce d.syllogism.is_valid)

def Demonstration.minimalBasis {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    (d : Demonstration Model science)
    (hirr : PremiseIrredundantIn science d.premises d.conclusion) :
    MinimalDemonstrativeBasisIn science d.premises d.conclusion :=
  d.basis.minimal hirr

theorem Demonstration.premisesOmnitemporal {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    (d : Demonstration Model science) :
    ∀ ⦃premise : Categorical⦄, premise ∈ d.premises → IsOmnitemporal m premise := by
  intro premise hmem
  exact (d.premisesTrueIn hmem).right

theorem Demonstration.conclusion_omnitemporal {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    (d : Demonstration Model science) :
    IsOmnitemporal m d.conclusion := by
  exact omnitemporal_of_derives (d.premisesOmnitemporal)
    (Derives.fromDeduce d.syllogism.is_valid)

theorem Demonstration.conclusion_trueIn {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    (d : Demonstration Model science) :
    science.TrueIn d.conclusion :=
  ⟨d.conclusion_admissible, d.conclusion_omnitemporal⟩

theorem Demonstration.premisesNonReciprocal {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    (d : Demonstration Model science) :
    NonReciprocalIn science d.premises d.conclusion := by
  simpa [Demonstration.premises, Demonstration.conclusion] using d.nonreciprocal

theorem Demonstration.noncircular {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    (d : Demonstration Model science) :
    NonCircular science d.premises d.conclusion :=
  d.premisesNonReciprocal.noncircular

theorem Demonstration.conclusion_not_immediate {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    (d : Demonstration Model science) :
    ¬ ImmediateIn science d.conclusion := by
  cases d with
  | mk figured conclusion_admissible major_principle minor_principle nonreciprocal explains =>
      cases figured with
      | mk minor middle major mood =>
          cases mood
          · intro himm
            have hPremises :
                PremisesTrueIn science [Categorical.A middle major, Categorical.A minor middle] := by
              intro premise hmem
              have hpair :
                  premise = Categorical.A middle major ∨
                    premise = Categorical.A minor middle := by
                simpa [List.mem_cons] using hmem
              rcases hpair with rfl | rfl
              · exact major_principle.trueIn
              · exact minor_principle.trueIn
            have hmiddle : middle = minor ∨ middle = major :=
              himm.noDistinctMiddle hPremises
                (Derives.premise (by simp))
                (Derives.premise (by simp))
            rcases hmiddle with hmiddle | hmiddle
            · exact explains.middle_distinct_from_minor hmiddle
            · exact explains.middle_distinct_from_major hmiddle
          · intro himm
            have hPremises :
                PremisesTrueIn science [Categorical.E middle major, Categorical.A minor middle] := by
              intro premise hmem
              have hpair :
                  premise = Categorical.E middle major ∨
                    premise = Categorical.A minor middle := by
                simpa [List.mem_cons] using hmem
              rcases hpair with rfl | rfl
              · exact major_principle.trueIn
              · exact minor_principle.trueIn
            have hmiddle : middle = minor ∨ middle = major :=
              himm.no_nontrivial_celarent_middle hPremises
                (Derives.premise (by simp))
                (Derives.premise (by simp))
            rcases hmiddle with hmiddle | hmiddle
            · exact explains.middle_distinct_from_minor hmiddle
            · exact explains.middle_distinct_from_major hmiddle
          · intro himm
            have hPremises :
                PremisesTrueIn science [Categorical.E major middle, Categorical.A minor middle] := by
              intro premise hmem
              have hpair :
                  premise = Categorical.E major middle ∨
                    premise = Categorical.A minor middle := by
                simpa [List.mem_cons] using hmem
              rcases hpair with rfl | rfl
              · exact major_principle.trueIn
              · exact minor_principle.trueIn
            have hmiddle : middle = minor ∨ middle = major :=
              himm.no_nontrivial_cesare_middle hPremises
                (Derives.premise (by simp))
                (Derives.premise (by simp))
            rcases hmiddle with hmiddle | hmiddle
            · exact explains.middle_distinct_from_minor hmiddle
            · exact explains.middle_distinct_from_major hmiddle
          · intro himm
            have hPremises :
                PremisesTrueIn science [Categorical.A major middle, Categorical.E minor middle] := by
              intro premise hmem
              have hpair :
                  premise = Categorical.A major middle ∨
                    premise = Categorical.E minor middle := by
                simpa [List.mem_cons] using hmem
              rcases hpair with rfl | rfl
              · exact major_principle.trueIn
              · exact minor_principle.trueIn
            have hmiddle : middle = minor ∨ middle = major :=
              himm.no_nontrivial_camestres_middle hPremises
                (Derives.premise (by simp))
                (Derives.premise (by simp))
            rcases hmiddle with hmiddle | hmiddle
            · exact explains.middle_distinct_from_minor hmiddle
            · exact explains.middle_distinct_from_major hmiddle

theorem Demonstration.conclusion_not_nous {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    (d : Demonstration Model science) :
    ¬ Nous science d.conclusion := by
  intro hnous
  exact d.conclusion_not_immediate hnous.immediateIn

/--
`CausalDemonstration` is the stronger Smith-facing layer where the explanatory
middle is taken not merely as a formal intermediary but as the cause.
-/
structure CausalDemonstration (Model : Type) [Interpretation Model]
    {m : Model} (science : Science Model m)
    extends Demonstration Model science where
  companion_cause : IsCauseOf science toDemonstration.figured.firstFigureCompanion

namespace CausalDemonstration

def causalExplanatorySyllogism {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    (d : CausalDemonstration Model science) :
    CausalExplanatorySyllogismIn science d.toDemonstration.figured where
  explanatory := d.toDemonstration.explains
  companion_cause := d.companion_cause

def whyQuestion {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    (d : CausalDemonstration Model science) : WhyQuestion :=
  { subject := d.toDemonstration.figured.minor
    predicate := d.toDemonstration.figured.major
    quality := d.toDemonstration.figured.conclusion.quality }

theorem answersWhyThroughCause {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    (d : CausalDemonstration Model science) :
    AnswersWhyThroughCauseIn science d.whyQuestion := by
  cases d with
  | mk demo companion_cause =>
      cases demo with
      | mk figured conclusion_admissible major_principle minor_principle nonreciprocal explains =>
          refine ⟨figured, ?_, { explanatory := explains, companion_cause := companion_cause }⟩
          cases figured with
          | mk minor middle major mood =>
              cases mood <;> rfl

theorem answersWhy {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    (d : CausalDemonstration Model science) :
    AnswersWhyIn science d.whyQuestion := by
  rcases d.answersWhyThroughCause with ⟨figured, hconclusion, hcausal⟩
  exact ⟨figured, hconclusion, hcausal.explanatoryWitness⟩

end CausalDemonstration

end Aristotle.PosteriorAnalytics
