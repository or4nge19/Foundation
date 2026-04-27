import Philosophy.Aristotle.DialecticStaged
import Philosophy.Aristotle.PosteriorAnalytics.Core

namespace Aristotle.InquiryBoundary

open Aristotle.Categories
open Aristotle.Dialectic
open Aristotle.PriorAnalytics
open Aristotle.PosteriorAnalytics

theorem problemAim_ne_whyQuestionAim
    (problem : Problem) (question : WhyQuestion) :
    problem.aim ≠ question.aim := by
  simp [Problem.hoti_only, WhyQuestion.dioti_only]

theorem whyQuestionAim_ne_problemAim
    (problem : Problem) (question : WhyQuestion) :
    question.aim ≠ problem.aim := by
  simp [Problem.hoti_only, WhyQuestion.dioti_only]

/--
If a dialectical problem has a first categorical commitment, we can re-ask that
same commitment as a scientific `WhyQuestion` without changing the sentence
itself. What changes is the inquiry-role, not the conclusion-content.
-/
def problemWhyQuestion? (problem : Problem) : Option WhyQuestion :=
  problem.statement?.map WhyQuestion.ofConclusion

theorem problemStatement_eq_some_isUniversalAffirmative
    {problem : Problem} {statement : Categorical}
    (h : problem.statement? = some statement) :
    ∃ subject predicate, statement = Categorical.A subject predicate := by
  cases problem with
  | predication subject predicate =>
      refine ⟨subject, predicate, ?_⟩
      simpa [Problem.statement?, Problem.statements] using h.symm
  | genus subject genusTerm =>
      refine ⟨subject, genusTerm, ?_⟩
      simpa [Problem.statement?, Problem.statements] using h.symm
  | definition subject definition =>
      cases hdiff : definition.differentiae with
      | nil =>
          simp [Problem.statement?, Problem.statements, hdiff] at h
      | cons differentia rest =>
          refine ⟨subject, definition.genus, ?_⟩
          simpa [Problem.statement?, Problem.statements, hdiff] using h.symm
  | proprium subject property =>
      refine ⟨subject, property, ?_⟩
      simpa [Problem.statement?, Problem.statements] using h.symm

theorem problemOfConclusion_sameConclusion_of_statement
    {problem : Problem} {statement : Categorical}
    (h : problem.statement? = some statement) :
    (WhyQuestion.ofConclusion statement).conclusion = statement := by
  rcases problemStatement_eq_some_isUniversalAffirmative h with ⟨subject, predicate, rfl⟩
  simp

theorem problemWhyQuestion_eq_some_of_statement
    {problem : Problem} {statement : Categorical}
    (h : problem.statement? = some statement) :
    problemWhyQuestion? problem = some (WhyQuestion.ofConclusion statement) := by
  simp [problemWhyQuestion?, h]

theorem problemWhyQuestion_differentAim_of_statement
    {problem : Problem} {statement : Categorical}
    (_h : problem.statement? = some statement) :
    (WhyQuestion.ofConclusion statement).aim ≠ problem.aim := by
  exact whyQuestionAim_ne_problemAim problem (WhyQuestion.ofConclusion statement)

theorem not_demonstrativeBasis_of_not_firstPrinciples
    {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {premises : List Categorical} {conclusion : Categorical}
    (h : ¬ FirstPrinciples science premises) :
    ¬ DemonstrativeBasisIn science premises conclusion := by
  intro hbasis
  exact h hbasis.first_principles

theorem dialecticalSyllogism_without_demonstrativeBasis
    {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {art : DialecticalArt} {respondent : RespondentKind}
    {premises : List Categorical} {conclusion : Categorical}
    (hdial : DialecticalSyllogism art respondent premises conclusion)
    (hnot : ¬ FirstPrinciples science premises) :
    DialecticalSyllogism art respondent premises conclusion ∧
      ¬ DemonstrativeBasisIn science premises conclusion :=
  ⟨hdial, not_demonstrativeBasis_of_not_firstPrinciples hnot⟩

theorem not_answersWhyThroughCause_of_not_answersWhy
    {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {question : WhyQuestion}
    (h : ¬ AnswersWhyIn science question) :
    ¬ AnswersWhyThroughCauseIn science question := by
  intro hcausal
  apply h
  rcases hcausal with ⟨figured, hconclusion, hcausal⟩
  exact ⟨figured, hconclusion, hcausal.explanatoryWitness⟩

/--
`NaiveScientificPromotionIn` records the tempting but illicit move from a
dialectical definition-problem straight to a scientific definition built from
the same raw phrase, while retaining a successful dialectical dossier for that
very candidate.
-/
def NaiveScientificPromotionIn
    {Model : Type} [Interpretation Model]
    {m : Model} [Aristotle.Categories.PredicationalManual]
    (science : Science Model m) (problem : PositionedDefinitionProblem) : Prop :=
  ∃ _dossier : Aristotle.Categories.DialecticalDefinitionDossier problem.subject problem.phrase,
    ∃ hscientific : ScientificDefinitionIn science problem.subject.candidate.term,
      hscientific.definition = problem.phrase.toPhrase.asScientificDefinition

theorem not_naiveScientificPromotionIn_of_not_dossier
    {Model : Type} [Interpretation Model]
    {m : Model} [Aristotle.Categories.PredicationalManual]
    {science : Science Model m} {problem : PositionedDefinitionProblem}
    (h : ¬ Aristotle.Categories.DialecticalDefinitionDossier problem.subject problem.phrase) :
    ¬ NaiveScientificPromotionIn science problem := by
  intro hpromotion
  rcases hpromotion with ⟨dossier, _, _⟩
  exact h dossier

/--
Staged `diagnoseDefinition` has an admissible arm **iff** a
`DialecticalDefinitionDossier` exists (`Aristotle.Dialectic.diagnoseDefinition_eq_admissible_iff`).
So "the diagnosis never lands on admissible" is the same *mathematical* fact as
"no dossier"—here packaged for the Smith-style *Posterior* boundary: no
dossier, hence no `NaiveScientificPromotionIn`, *without* re-choosing among the
separate `DefinitionRefutationBy*` theorems. Menn-Topics: the *elenchus* has
refuted or blocked the material for a putative definition; that is the principled
common content behind the disjunction of defeat patterns.
-/
theorem not_naiveScientificPromotionIn_of_not_admissibleDefinitionDiagnosis
    {Model : Type} [Interpretation Model]
    {m : Model} [Aristotle.Categories.PredicationalManual]
    {science : Science Model m} {problem : PositionedDefinitionProblem}
    (h : ¬ ∃ dossier, diagnoseDefinition problem = .admissible dossier) :
    ¬ NaiveScientificPromotionIn science problem :=
  not_naiveScientificPromotionIn_of_not_dossier fun hdossier =>
    h (diagnoseDefinition_eq_admissible_iff (problem := problem).2 hdossier)

/--
Converse to the diagnosis bridge: if `NaiveScientificPromotionIn` holds, the
staged **definition** screen has an admissible outcome—since promotion
**presupposes** a `DialecticalDefinitionDossier` (`NaiveScientificPromotionIn`’s
first conjunct) and that is *equivalent* to
`∃ d, diagnoseDefinition = .admissible d` (`diagnoseDefinition_eq_admissible_iff`).

This does **not** endorse promotion as sound science; it only makes explicit that,
in this formalization, the “naive” move is **not** intelligible *without* passing
the same diagnosis gate, so refuting admissible diagnosis refutes the package (the
`not_*` theorems above). Menn-Topics: dialectical material is still a gate even when
it is *mis*used at the boundary to Posterior structure; Smith-Posterior: scientific
`ScientificDefinitionIn` is a further conjunct, not entailed by admissible diagnosis
alone.
-/
theorem exists_admissibleDefinitionDiagnosis_of_naiveScientificPromotionIn
    {Model : Type} [Interpretation Model]
    {m : Model} [Aristotle.Categories.PredicationalManual]
    {science : Science Model m} {problem : PositionedDefinitionProblem}
    (h : NaiveScientificPromotionIn science problem) :
    ∃ dossier, diagnoseDefinition problem = .admissible dossier := by
  rcases h with ⟨dossier, _, _⟩ 
  exact diagnoseDefinition_eq_admissible_iff (problem := problem).2 dossier

/-- The **first** conjunct of `NaiveScientificPromotionIn`: a dialectical dossier for
the very candidate is already assumed—before any `ScientificDefinitionIn` is cited.
(Topics/elenchus layer; Menn-interpretive: promotion presupposes screened material.) -/
theorem dialecticalDefinitionDossier_of_naiveScientificPromotionIn
    {Model : Type} [Interpretation Model]
    {m : Model} [Aristotle.Categories.PredicationalManual]
    {science : Science Model m} {problem : PositionedDefinitionProblem}
    (h : NaiveScientificPromotionIn science problem) :
    Aristotle.Categories.DialecticalDefinitionDossier problem.subject problem.phrase := by
  rcases h with ⟨dossier, _, _⟩; exact dossier

/-- Single interface clause: the Topics dossier and a matching admissible
`diagnoseDefinition` follow together from the same `NaiveScientificPromotionIn`
package (concatenation of
`dialecticalDefinitionDossier_of_naiveScientificPromotionIn` and
`exists_admissibleDefinitionDiagnosis_of_naiveScientificPromotionIn`, kept as one
`And` for downstream refactors and proof search). -/
theorem dialecticalDossier_and_admissibleDiagnosis_of_naiveScientificPromotionIn
    {Model : Type} [Interpretation Model]
    {m : Model} [Aristotle.Categories.PredicationalManual]
    {science : Science Model m} {problem : PositionedDefinitionProblem}
    (h : NaiveScientificPromotionIn science problem) :
    Aristotle.Categories.DialecticalDefinitionDossier problem.subject problem.phrase ∧
      ∃ dossier, diagnoseDefinition problem = .admissible dossier :=
  ⟨dialecticalDefinitionDossier_of_naiveScientificPromotionIn h,
    exists_admissibleDefinitionDiagnosis_of_naiveScientificPromotionIn h⟩

theorem not_naiveScientificPromotionIn_of_definitionFigureOfSpeechMismatch
    {Model : Type} [Interpretation Model]
    {m : Model} [Aristotle.Categories.PredicationalManual]
    {science : Science Model m} {problem : PositionedDefinitionProblem}
    (h : DefinitionRefutationByFigureOfSpeechMismatch problem) :
    ¬ NaiveScientificPromotionIn science problem := by
  exact not_naiveScientificPromotionIn_of_not_dossier
    (definitionFigureOfSpeechMismatch_not_dossier h)

theorem not_naiveScientificPromotionIn_of_definitionSurfaceTrapMismatch
    {Model : Type} [Interpretation Model]
    {m : Model} [Aristotle.Categories.PredicationalManual]
    {science : Science Model m} {problem : PositionedDefinitionProblem}
    (h : DefinitionRefutationBySurfaceTrapMismatch problem) :
    ¬ NaiveScientificPromotionIn science problem := by
  exact not_naiveScientificPromotionIn_of_not_dossier
    (definitionSurfaceTrapMismatch_not_dossier h)

theorem not_naiveScientificPromotionIn_of_definitionCategoryMismatch
    {Model : Type} [Interpretation Model]
    {m : Model} [Aristotle.Categories.PredicationalManual]
    {science : Science Model m} {problem : PositionedDefinitionProblem}
    (h : DefinitionRefutationByCategoryMismatch problem.subject problem.phrase) :
    ¬ NaiveScientificPromotionIn science problem := by
  exact not_naiveScientificPromotionIn_of_not_dossier (fun dossier =>
    Aristotle.Categories.DialecticalDefinitionDossier.notCategoryMismatch dossier h)

theorem not_naiveScientificPromotionIn_of_definitionContraryMismatch
    {Model : Type} [Interpretation Model]
    {m : Model} [Aristotle.Categories.PredicationalManual]
    {science : Science Model m} {problem : PositionedDefinitionProblem}
    (h : DefinitionRefutationByContraryMismatch problem.subject problem.phrase) :
    ¬ NaiveScientificPromotionIn science problem := by
  exact not_naiveScientificPromotionIn_of_not_dossier (fun dossier =>
    Aristotle.Categories.DialecticalDefinitionDossier.notContraryMismatch dossier h)

theorem not_naiveScientificPromotionIn_of_definitionDegreeMismatch
    {Model : Type} [Interpretation Model]
    {m : Model} [Aristotle.Categories.PredicationalManual]
    {science : Science Model m} {problem : PositionedDefinitionProblem}
    (h : DefinitionRefutationByDegreeMismatch problem.subject problem.phrase) :
    ¬ NaiveScientificPromotionIn science problem := by
  exact not_naiveScientificPromotionIn_of_not_dossier (fun dossier =>
    Aristotle.Categories.DialecticalDefinitionDossier.notDegreeMismatch dossier h)

theorem not_naiveScientificPromotionIn_of_definitionGenusNotSaidOf
    {Model : Type} [Interpretation Model]
    {m : Model} [Aristotle.Categories.PredicationalManual]
    {science : Science Model m} {problem : PositionedDefinitionProblem}
    (h : DefinitionRefutationByGenusNotSaidOf problem.subject problem.phrase) :
    ¬ NaiveScientificPromotionIn science problem := by
  exact not_naiveScientificPromotionIn_of_not_dossier (fun dossier =>
    Aristotle.Categories.DialecticalDefinitionDossier.notGenusNotSaidOf dossier h)

theorem not_naiveScientificPromotionIn_of_definitionDifferentiaNotSaidOf
    {Model : Type} [Interpretation Model]
    {m : Model} [Aristotle.Categories.PredicationalManual]
    {science : Science Model m} {problem : PositionedDefinitionProblem}
    (h : DefinitionRefutationByDifferentiaNotSaidOf problem.subject problem.phrase) :
    ¬ NaiveScientificPromotionIn science problem := by
  exact not_naiveScientificPromotionIn_of_not_dossier (fun dossier =>
    Aristotle.Categories.DialecticalDefinitionDossier.notDifferentiaNotSaidOf dossier h)

theorem not_naiveScientificPromotionIn_of_definitionInSubject
    {Model : Type} [Interpretation Model]
    {m : Model} [Aristotle.Categories.PredicationalManual]
    {science : Science Model m} {problem : PositionedDefinitionProblem}
    (h : DefinitionRefutationByInSubject problem.subject problem.phrase) :
    ¬ NaiveScientificPromotionIn science problem := by
  exact not_naiveScientificPromotionIn_of_not_dossier (fun dossier =>
    Aristotle.Categories.DialecticalDefinitionDossier.notInSubject_refutation dossier h)

end Aristotle.InquiryBoundary
