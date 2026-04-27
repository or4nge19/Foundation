import Philosophy.Aristotle.Categories
import Philosophy.Aristotle.PriorAnalytics

namespace Aristotle.Dialectic

open Aristotle.Categories
open Aristotle.PriorAnalytics

/-!
# Staged Dialectic

`Philosophy/Aristotle/Aristotle.md` presents dialectic as a teachable,
preliminary art: it tests theses from endoxa, especially candidate definitions,
without yet becoming science. `Philosophy/Aristotle/MDC_Menn.md` provides the
more detailed reconstruction governing this file.

Accordingly, the staged API here does not treat definitions as already
scientific accounts. It screens them, positions them, diagnoses their failure
or provisional admissibility, and exposes the full list of commitments that an
elenchus may target.

The newly added Smith `Topics` materials now give the nearest textual control
for this module:

- `Topics-I.10,11.md` for dialectical premiss, problem, and thesis
- `Topics-I.12,13.md` and `Topics-I.14.md` for induction, premiss collection,
  and the preparatory tools of dialectic
- `Topics-VIII.1.md` through `Topics-VIII.14.md` for arrangement,
  questioner/answerer aims, objections, criticism, and training

So this file should be read as an initial executable staging of that material,
not as a finished dialectical engine.
-/

abbrev DialecticalTerm := Aristotle.Categories.Term
abbrev DefinitionalPhrase := Aristotle.Categories.DefinitionalPhrase
abbrev DialecticalDefinition := Aristotle.Categories.DialecticalDefinition
abbrev InquiryAim := Philosophy.Aristotle.Core.InquiryAim

inductive RespondentKind
  | everyone
  | many
  | wise
  | mostFamousWise
  | certainSort
  deriving DecidableEq, Repr

namespace RespondentKind

def admits (source respondent : RespondentKind) : Prop :=
  source = .everyone ∨ source = respondent

theorem admits_refl (respondent : RespondentKind) : admits respondent respondent := by
  exact Or.inr rfl

theorem everyone_admits (respondent : RespondentKind) : admits .everyone respondent := by
  exact Or.inl rfl

end RespondentKind

/--
A minimal store of what each respondent-kind will concede. This is the current
executable shadow of the premiss-collections and tables discussed in Smith's
commentary on `Topics` I.10-I.14.
-/
structure DialecticalArt where
  acceptedPremises : RespondentKind → List Categorical

def acceptableTo (art : DialecticalArt)
    (respondent : RespondentKind) (premise : Categorical) : Prop :=
  premise ∈ art.acceptedPremises respondent

/--
An `Endoxon` packages a proposition together with the constituency relative to
which it is acceptable. This follows Smith's reading of `Topics` I.1 and I.10,
where endoxa are not bare truths but materials available for dialectical
questioning because they are accepted by some ranked public.
-/
structure Endoxon where
  proposition : Categorical
  source : RespondentKind
  deriving DecidableEq, Repr

def Endoxon.availableTo (endoxon : Endoxon)
    (respondent : RespondentKind) : Prop :=
  RespondentKind.admits endoxon.source respondent

def Endoxon.acceptableIn (endoxon : Endoxon) (art : DialecticalArt)
    (respondent : RespondentKind) : Prop :=
  endoxon.availableTo respondent ∧ acceptableTo art respondent endoxon.proposition

/--
The four thesis-types singled out by the Topics-style workflow:

- predication
- genus
- definition
- proprium

The definition case deliberately carries a `DialecticalDefinition` rather than a
flat term, because dialectic tests a candidate account through its genus and
differentiae before any scientific completion is available.

Smith's commentary on `Topics` I.4-6 and I.10-11 is especially important here:
`Problem` is not just a proposition in the abstract, but a proposition under a
definite argumentative role and under a definite predicable heading.
-/
inductive Problem
  | predication (subject predicate : DialecticalTerm)
  | genus (subject genusTerm : DialecticalTerm)
  | definition (subject : DialecticalTerm) (definition : DialecticalDefinition)
  | proprium (subject property : DialecticalTerm)
  deriving DecidableEq, Repr

def Problem.predicable : Problem → Predicable
  | .predication _ _ => .accident
  | .genus _ _ => .genus
  | .definition _ _ => .definition
  | .proprium _ _ => .proprium

/--
Menn's point is that dialectical problems ask whether some predication, genus,
definition, or proprium claim stands; they do not yet ask why it stands.
-/
def Problem.aim (_problem : Problem) : InquiryAim :=
  .hoti

theorem Problem.hoti_only (problem : Problem) : problem.aim = .hoti := by
  rfl

def Problem.leftTerm : Problem → DialecticalTerm
  | .predication subject _ => subject
  | .genus subject _ => subject
  | .definition subject _ => subject
  | .proprium subject _ => subject

def Problem.rightTerm : Problem → DialecticalTerm
  | .predication _ predicate => predicate
  | .genus _ genusTerm => genusTerm
  | .definition _ dialecticalDefinition => dialecticalDefinition.genus
  | .proprium _ property => property

/--
`Problem.statements` records the categorical commitments carried by a thesis.
Definitions keep the genus anchor and each differentia explicit, so the game
does not silently collapse a `logos` into its genus alone.

Malformed definition proposals with no differentiae contribute no categorical
commitment at all, rather than being downgraded to a bare genus claim.
-/
def Problem.statements : Problem → List Categorical
  | .predication subject predicate => [.A subject predicate]
  | .genus subject genusTerm => [.A subject genusTerm]
  | .definition subject dialecticalDefinition =>
      match dialecticalDefinition.differentiae with
      | [] => []
      | differentiae =>
          Categorical.A subject dialecticalDefinition.genus ::
            differentiae.map (fun differentia => Categorical.A subject differentia)
  | .proprium subject property => [.A subject property]

def Problem.statement? (problem : Problem) : Option Categorical :=
  problem.statements.head?

inductive ProblemSide
  | left
  | right
  deriving DecidableEq, Repr

structure ScreenedTermPair [AntepredicamentalManual] where
  left : CategorialCandidate
  right : CategorialCandidate

structure BlockedScreening [AntepredicamentalManual] where
  term : DialecticalTerm
  reason : BlockedSimpleTermScreening term

inductive DefinitionComponent
  | genus
  | differentia (term : DialecticalTerm)
  deriving DecidableEq, Repr

inductive DefinitionScreeningFailure [AntepredicamentalManual]
  | emptyDifferentiae (definition : DialecticalDefinition)
  | blocked (component : DefinitionComponent) (blocked : BlockedScreening)

inductive TermPairScreening [AntepredicamentalManual]
  | blocked (side : ProblemSide) (blocked : BlockedScreening)
  | screened (pair : ScreenedTermPair)

noncomputable def screenTermPair [AntepredicamentalManual]
    (leftTerm rightTerm : DialecticalTerm) : TermPairScreening := by
  classical
  cases screenSimpleTerm leftTerm with
  | blocked h =>
      exact .blocked .left ⟨leftTerm, h⟩
  | candidate left =>
      cases screenSimpleTerm rightTerm with
      | blocked h =>
          exact .blocked .right ⟨rightTerm, h⟩
      | candidate right =>
          exact .screened ⟨left, right⟩

noncomputable def screenDifferentiae [AntepredicamentalManual] :
    List DialecticalTerm → Except BlockedScreening (List CategorialCandidate)
  | [] => .ok []
  | term :: rest =>
      match screenSimpleTerm term with
      | .blocked blocked => .error ⟨term, blocked⟩
      | .candidate candidate =>
          match screenDifferentiae rest with
          | .error blocked => .error blocked
          | .ok candidates => .ok (candidate :: candidates)

theorem screenDifferentiae_ok_nil_iff [AntepredicamentalManual]
    {terms : List DialecticalTerm} :
    screenDifferentiae terms = .ok [] ↔ terms = [] := by
  constructor
  · intro h
    cases terms with
    | nil =>
        rfl
    | cons term rest =>
        cases hscreen : screenSimpleTerm term <;>
          cases hrest : screenDifferentiae rest <;>
            simp [screenDifferentiae, hscreen, hrest] at h
  · intro h
    subst h
    simp [screenDifferentiae]

noncomputable def screenDefinitionalPhrase [AntepredicamentalManual]
    (definition : DialecticalDefinition) :
    Except (DefinitionScreeningFailure) ScreenedDefinitionalPhrase := by
  classical
  by_cases hnil : definition.differentiae = []
  · exact .error (.emptyDifferentiae definition)
  · cases hgenus : screenSimpleTerm definition.genus with
    | blocked blocked =>
        exact .error (.blocked .genus ⟨definition.genus, blocked⟩)
    | candidate genus =>
        match hdiffs : screenDifferentiae definition.differentiae with
        | .error blocked =>
            exact .error (.blocked (.differentia blocked.term) blocked)
        | .ok differentiae =>
            have hne : differentiae ≠ [] := by
              intro hdiffNil
              have hscreenNil : screenDifferentiae definition.differentiae = .ok [] := by
                simp [hdiffs, hdiffNil]
              have hsourceNil : definition.differentiae = [] :=
                (screenDifferentiae_ok_nil_iff).1 hscreenNil
              exact hnil hsourceNil
            exact .ok
              { genus := genus
                differentiae := differentiae
                lexicalForm := definition.lexicalForm
                nonempty := hne }

inductive ScreenedProblem [AntepredicamentalManual]
  | predication (subject predicate : CategorialCandidate)
  | genus (subject genusTerm : CategorialCandidate)
  | definition (subject : CategorialCandidate) (phrase : ScreenedDefinitionalPhrase)
  | proprium (subject property : CategorialCandidate)

def ScreenedProblem.toProblem [AntepredicamentalManual] : ScreenedProblem → Problem
  | .predication subject predicate => .predication subject.term predicate.term
  | .genus subject genusTerm => .genus subject.term genusTerm.term
  | .definition subject phrase => .definition subject.term phrase.toDefinition
  | .proprium subject property => .proprium subject.term property.term

inductive ProblemScreening [AntepredicamentalManual]
  | blockedTerm (problem : Problem) (side : ProblemSide) (blocked : BlockedScreening)
  | blockedDefinition (problem : Problem) (failure : DefinitionScreeningFailure)
  | screened (problem : ScreenedProblem)

noncomputable def screenProblem [AntepredicamentalManual]
    (problem : Problem) : ProblemScreening := by
  classical
  cases problem with
  | predication subject predicate =>
      cases screenTermPair subject predicate with
      | blocked side blocked =>
          exact .blockedTerm (.predication subject predicate) side blocked
      | screened pair =>
          exact .screened (.predication pair.left pair.right)
  | genus subject genusTerm =>
      cases screenTermPair subject genusTerm with
      | blocked side blocked =>
          exact .blockedTerm (.genus subject genusTerm) side blocked
      | screened pair =>
          exact .screened (.genus pair.left pair.right)
  | definition subjectTerm dialecticalDefinition =>
      cases screenSimpleTerm subjectTerm with
      | blocked blocked =>
          exact .blockedTerm (.definition subjectTerm dialecticalDefinition) .left ⟨subjectTerm, blocked⟩
      | candidate subject =>
          match screenDefinitionalPhrase dialecticalDefinition with
          | .error failure => exact .blockedDefinition (.definition subjectTerm dialecticalDefinition) failure
          | .ok screenedPhrase => exact .screened (.definition subject screenedPhrase)
  | proprium subject property =>
      cases screenTermPair subject property with
      | blocked side blocked =>
          exact .blockedTerm (.proprium subject property) side blocked
      | screened pair =>
          exact .screened (.proprium pair.left pair.right)

inductive PositionedProblem [Manual]
  | predication (subject predicate : PositionedCandidate)
  | genus (subject genusTerm : PositionedCandidate)
  | definition (subject : PositionedCandidate) (phrase : PositionedDefinitionalPhrase)
  | proprium (subject property : PositionedCandidate)

structure PositionedGenusProblem [Manual] where
  subject : PositionedCandidate
  genusTerm : PositionedCandidate

structure PositionedDefinitionProblem [Manual] where
  subject : PositionedCandidate
  phrase : PositionedDefinitionalPhrase

structure PositionedPropriumProblem [Manual] where
  subject : PositionedCandidate
  property : PositionedCandidate

def PositionedGenusProblem.toProblem [Manual]
    (problem : PositionedGenusProblem) : Problem :=
  .genus problem.subject.candidate.term problem.genusTerm.candidate.term

def PositionedDefinitionProblem.toProblem [Manual]
    (problem : PositionedDefinitionProblem) : Problem :=
  .definition problem.subject.candidate.term problem.phrase.toDefinition

def PositionedPropriumProblem.toProblem [Manual]
    (problem : PositionedPropriumProblem) : Problem :=
  .proprium problem.subject.candidate.term problem.property.candidate.term

noncomputable def positionScreenedProblem? [Manual]
    (problem : ScreenedProblem) : Option PositionedProblem := by
  classical
  match problem with
  | .predication subject predicate =>
      match positionCandidate? subject, positionCandidate? predicate with
      | some subject, some predicate => exact some (.predication subject predicate)
      | _, _ => exact none
  | .genus subject genusTerm =>
      match positionCandidate? subject, positionCandidate? genusTerm with
      | some subject, some genusTerm => exact some (.genus subject genusTerm)
      | _, _ => exact none
  | .definition subject phrase =>
      match positionCandidate? subject, positionDefinitionalPhrase? phrase with
      | some subject, some phrase => exact some (.definition subject phrase)
      | _, _ => exact none
  | .proprium subject property =>
      match positionCandidate? subject, positionCandidate? property with
      | some subject, some property => exact some (.proprium subject property)
      | _, _ => exact none

def PositionedProblem.toGenus? [Manual] : PositionedProblem → Option PositionedGenusProblem
  | .genus subject genusTerm => some ⟨subject, genusTerm⟩
  | _ => none

def PositionedProblem.toDefinition? [Manual] : PositionedProblem → Option PositionedDefinitionProblem
  | .definition subject phrase => some ⟨subject, phrase⟩
  | _ => none

def PositionedProblem.toProprium? [Manual] : PositionedProblem → Option PositionedPropriumProblem
  | .proprium subject property => some ⟨subject, property⟩
  | _ => none

def PositionedProblem.toProblem [Manual] : PositionedProblem → Problem
  | .predication subject predicate =>
      .predication subject.candidate.term predicate.candidate.term
  | .genus subject genusTerm =>
      .genus subject.candidate.term genusTerm.candidate.term
  | .definition subject phrase =>
      .definition subject.candidate.term phrase.toDefinition
  | .proprium subject property =>
      .proprium subject.candidate.term property.candidate.term

abbrev GenusRefutationByContraryMismatch [Manual]
    (subject genusTerm : PositionedCandidate) : Prop :=
  ContraryMismatch subject genusTerm

abbrev GenusRefutationByDegreeMismatch [Manual]
    (subject genusTerm : PositionedCandidate) : Prop :=
  DegreeMismatch subject genusTerm

abbrev GenusRefutationByFigureOfSpeechMismatch [Manual]
    (problem : PositionedGenusProblem) : Prop :=
  ∃ hsubject : FigureOfSpeechMismatch problem.subject,
    problem.genusTerm.placement.category = hsubject.voice.suggestedCategory

abbrev DefinitionRefutationByFigureOfSpeechMismatch [Manual]
    (problem : PositionedDefinitionProblem) : Prop :=
  ∃ hsubject : FigureOfSpeechMismatch problem.subject,
    problem.phrase.genus.placement.category = hsubject.voice.suggestedCategory

abbrev GenusRefutationBySurfaceTrapMismatch [Manual]
    (problem : PositionedGenusProblem) : Prop :=
  ∃ hsubject : SurfaceTrapMismatch problem.subject,
    problem.genusTerm.placement.category = hsubject.trap.suggestedCategory

abbrev DefinitionRefutationBySurfaceTrapMismatch [Manual]
    (problem : PositionedDefinitionProblem) : Prop :=
  ∃ hsubject : SurfaceTrapMismatch problem.subject,
    problem.phrase.genus.placement.category = hsubject.trap.suggestedCategory

theorem genusFigureOfSpeechMismatch_surfaceTrapMismatch [Manual]
    {problem : PositionedGenusProblem}
    (h : GenusRefutationByFigureOfSpeechMismatch problem) :
    GenusRefutationBySurfaceTrapMismatch problem := by
  rcases h with ⟨hsubject, hgenus⟩
  refine ⟨hsubject.toSurfaceTrapMismatch, ?_⟩
  simpa [FigureOfSpeechMismatch.toSurfaceTrapMismatch, SurfaceTrap.ofVoice] using hgenus

theorem definitionFigureOfSpeechMismatch_surfaceTrapMismatch [Manual]
    {problem : PositionedDefinitionProblem}
    (h : DefinitionRefutationByFigureOfSpeechMismatch problem) :
    DefinitionRefutationBySurfaceTrapMismatch problem := by
  rcases h with ⟨hsubject, hgenus⟩
  refine ⟨hsubject.toSurfaceTrapMismatch, ?_⟩
  simpa [FigureOfSpeechMismatch.toSurfaceTrapMismatch, SurfaceTrap.ofVoice] using hgenus

inductive GenusDiagnosis [PredicationalManual] (problem : PositionedGenusProblem) where
  | admissible (dossier : GenusDossier problem.subject problem.genusTerm)
  | figureOfSpeechMismatch
      (h : GenusRefutationByFigureOfSpeechMismatch problem)
  | categoryMismatch (h : ¬ sameCategory problem.subject problem.genusTerm)
  | contraryMismatch (h : GenusRefutationByContraryMismatch problem.subject problem.genusTerm)
  | degreeMismatch (h : GenusRefutationByDegreeMismatch problem.subject problem.genusTerm)
  | notSaidOf (h : GenusRefutationByNotSaidOf problem.subject problem.genusTerm)

inductive DefinitionDiagnosis [PredicationalManual] (problem : PositionedDefinitionProblem) where
  | admissible
      (dossier : DialecticalDefinitionDossier problem.subject problem.phrase)
  | figureOfSpeechMismatch
      (h : DefinitionRefutationByFigureOfSpeechMismatch problem)
  | categoryMismatch
      (h : DefinitionRefutationByCategoryMismatch problem.subject problem.phrase)
  | contraryMismatch
      (h : DefinitionRefutationByContraryMismatch problem.subject problem.phrase)
  | degreeMismatch
      (h : DefinitionRefutationByDegreeMismatch problem.subject problem.phrase)
  | genusNotSaidOf
      (h : DefinitionRefutationByGenusNotSaidOf problem.subject problem.phrase)
  | differentiaNotSaidOf
      (h : DefinitionRefutationByDifferentiaNotSaidOf problem.subject problem.phrase)
  | inSubject
      (h : DefinitionRefutationByInSubject problem.subject problem.phrase)

inductive PropriumDiagnosis [PredicationalManual] (problem : PositionedPropriumProblem) where
  | admissible (dossier : PropriumDossier problem.subject problem.property)
  | notSaidOf (h : PropriumRefutationByNotSaidOf problem.subject problem.property)
  | inSubject (h : PropriumRefutationByInSubject problem.subject problem.property)

noncomputable def diagnoseGenus [PredicationalManual]
    (problem : PositionedGenusProblem) : GenusDiagnosis problem := by
  classical
  by_cases hfigure : GenusRefutationByFigureOfSpeechMismatch problem
  · exact .figureOfSpeechMismatch hfigure
  · by_cases h : sameCategory problem.subject problem.genusTerm
    · by_cases hcontra : GenusRefutationByContraryMismatch problem.subject problem.genusTerm
      · exact .contraryMismatch hcontra
      · by_cases hdegree : GenusRefutationByDegreeMismatch problem.subject problem.genusTerm
        · exact .degreeMismatch hdegree
        · by_cases hgenus : GenusRefutationByNotSaidOf problem.subject problem.genusTerm
          · exact .notSaidOf hgenus
          · exact .admissible
              { sameCategory := h
                contrary := contraryCompatibility_of_not_mismatch hcontra
                degree := degreeCompatibility_of_not_mismatch hdegree
                genusSaidOf := by
                  by_contra hnot
                  exact hgenus hnot }
    · exact .categoryMismatch h

theorem diagnoseGenus_of_categoryMismatch [PredicationalManual]
    {problem : PositionedGenusProblem}
    (hfigure : ¬ GenusRefutationByFigureOfSpeechMismatch problem)
    (h : ¬ sameCategory problem.subject problem.genusTerm) :
    diagnoseGenus problem = .categoryMismatch h := by
  unfold diagnoseGenus
  simp [hfigure, h]

theorem diagnoseGenus_of_figureOfSpeechMismatch [PredicationalManual]
    {problem : PositionedGenusProblem}
    (h : GenusRefutationByFigureOfSpeechMismatch problem) :
    diagnoseGenus problem = .figureOfSpeechMismatch h := by
  unfold diagnoseGenus
  simp [h]

theorem diagnoseGenus_of_notSaidOf [PredicationalManual]
    {problem : PositionedGenusProblem}
    (hfigure : ¬ GenusRefutationByFigureOfSpeechMismatch problem)
    (hsame : sameCategory problem.subject problem.genusTerm)
    (hcontra : ¬ GenusRefutationByContraryMismatch problem.subject problem.genusTerm)
    (hdegree : ¬ GenusRefutationByDegreeMismatch problem.subject problem.genusTerm)
    (hgenus : GenusRefutationByNotSaidOf problem.subject problem.genusTerm) :
    diagnoseGenus problem = .notSaidOf hgenus := by
  unfold diagnoseGenus
  simp [hfigure, hsame, hcontra, hdegree, hgenus]

noncomputable def provisionalGenus? [PredicationalManual]
    (problem : PositionedGenusProblem) : Option ProvisionalGenus := by
  classical
  cases diagnoseGenus problem with
  | admissible dossier =>
      exact some
        { subject := problem.subject
          genus := problem.genusTerm
          compatibility := ⟨dossier.sameCategory⟩
          genusSaidOf := dossier.genusSaidOf }
  | figureOfSpeechMismatch _ => exact none
  | categoryMismatch _ => exact none
  | contraryMismatch _ => exact none
  | degreeMismatch _ => exact none
  | notSaidOf _ => exact none

noncomputable def diagnoseDefinition [PredicationalManual]
    (problem : PositionedDefinitionProblem) : DefinitionDiagnosis problem := by
  classical
  by_cases hfigure : DefinitionRefutationByFigureOfSpeechMismatch problem
  · exact .figureOfSpeechMismatch hfigure
  · by_cases hsame : sameCategory problem.subject problem.phrase.genus
    · by_cases hcontra :
        DefinitionRefutationByContraryMismatch problem.subject problem.phrase
      · exact .contraryMismatch hcontra
      · by_cases hdegree :
          DefinitionRefutationByDegreeMismatch problem.subject problem.phrase
        · exact .degreeMismatch hdegree
        · by_cases hgenus :
            DefinitionRefutationByGenusNotSaidOf problem.subject problem.phrase
          · exact .genusNotSaidOf hgenus
          · by_cases hdifferentia :
              DefinitionRefutationByDifferentiaNotSaidOf problem.subject problem.phrase
            · exact .differentiaNotSaidOf hdifferentia
            · by_cases hin :
                DefinitionRefutationByInSubject problem.subject problem.phrase
              · exact .inSubject hin
              · exact .admissible
                  { sameCategory := hsame
                    contrary := contraryCompatibility_of_not_mismatch hcontra
                    degree := degreeCompatibility_of_not_mismatch hdegree
                    genusSaidOf := by
                      simpa [DefinitionRefutationByGenusNotSaidOf] using hgenus
                    differentiaeSaidOf := by
                      intro differentia hmem
                      by_contra hnot
                      exact hdifferentia ⟨differentia, hmem, hnot⟩
                    differentiaeNotInSubject := by
                      intro differentia hmem hinDifferentia
                      exact hin ⟨differentia, hmem, hinDifferentia⟩ }
    · exact .categoryMismatch hsame

theorem definitionFigureOfSpeechMismatch_categoryMismatch [Manual]
    {problem : PositionedDefinitionProblem}
    (h : DefinitionRefutationByFigureOfSpeechMismatch problem) :
    DefinitionRefutationByCategoryMismatch problem.subject problem.phrase := by
  rcases h with ⟨hsubject, hgenus⟩
  exact (hsubject.categoryMismatch hgenus).mismatch

theorem genusSurfaceTrapMismatch_categoryMismatch [Manual]
    {problem : PositionedGenusProblem}
    (h : GenusRefutationBySurfaceTrapMismatch problem) :
    CategoryMismatch problem.subject problem.genusTerm := by
  rcases h with ⟨hsubject, hgenus⟩
  exact hsubject.categoryMismatch hgenus

theorem definitionSurfaceTrapMismatch_categoryMismatch [Manual]
    {problem : PositionedDefinitionProblem}
    (h : DefinitionRefutationBySurfaceTrapMismatch problem) :
    DefinitionRefutationByCategoryMismatch problem.subject problem.phrase := by
  rcases h with ⟨hsubject, hgenus⟩
  exact (hsubject.categoryMismatch hgenus).mismatch

theorem definitionFigureOfSpeechMismatch_not_dossier [PredicationalManual]
    {problem : PositionedDefinitionProblem}
    (h : DefinitionRefutationByFigureOfSpeechMismatch problem) :
    ¬ DialecticalDefinitionDossier problem.subject problem.phrase := by
  intro hdossier
  exact (DialecticalDefinitionDossier.notCategoryMismatch hdossier)
    (definitionFigureOfSpeechMismatch_categoryMismatch h)

theorem genusSurfaceTrapMismatch_not_provisionalGenus [PredicationalManual]
    {problem : PositionedGenusProblem}
    (h : GenusRefutationBySurfaceTrapMismatch problem) :
    ¬ ∃ provisional : ProvisionalGenus,
      provisional.subject = problem.subject ∧ provisional.genus = problem.genusTerm := by
  rintro ⟨provisional, hsubject, hgenus⟩
  have hsame : sameCategory problem.subject problem.genusTerm := by
    simpa [hsubject, hgenus] using provisional.compatibility.sameCategory
  exact (genusSurfaceTrapMismatch_categoryMismatch h).mismatch
    hsame

theorem definitionSurfaceTrapMismatch_not_dossier [PredicationalManual]
    {problem : PositionedDefinitionProblem}
    (h : DefinitionRefutationBySurfaceTrapMismatch problem) :
    ¬ DialecticalDefinitionDossier problem.subject problem.phrase := by
  intro hdossier
  exact (DialecticalDefinitionDossier.notCategoryMismatch hdossier)
    (definitionSurfaceTrapMismatch_categoryMismatch h)

theorem DialecticalDefinitionDossier.notFigureOfSpeechMismatch [PredicationalManual]
    {problem : PositionedDefinitionProblem}
    (h : DialecticalDefinitionDossier problem.subject problem.phrase) :
    ¬ DefinitionRefutationByFigureOfSpeechMismatch problem := by
  intro hfigure
  exact definitionFigureOfSpeechMismatch_not_dossier hfigure h

theorem diagnoseDefinition_of_figureOfSpeechMismatch [PredicationalManual]
    {problem : PositionedDefinitionProblem}
    (h : DefinitionRefutationByFigureOfSpeechMismatch problem) :
    diagnoseDefinition problem = .figureOfSpeechMismatch h := by
  unfold diagnoseDefinition
  simp [h]

theorem diagnoseDefinition_eq_figureOfSpeechMismatch_iff [PredicationalManual]
    {problem : PositionedDefinitionProblem} :
    (∃ h, diagnoseDefinition problem = .figureOfSpeechMismatch h) ↔
      DefinitionRefutationByFigureOfSpeechMismatch problem := by
  constructor
  · rintro ⟨h, _⟩
    exact h
  · intro h
    exact ⟨h, diagnoseDefinition_of_figureOfSpeechMismatch h⟩

theorem diagnoseDefinition_eq_categoryMismatch_iff [PredicationalManual]
    {problem : PositionedDefinitionProblem} :
    (∃ h, diagnoseDefinition problem = .categoryMismatch h) ↔
      ¬ DefinitionRefutationByFigureOfSpeechMismatch problem ∧
        DefinitionRefutationByCategoryMismatch problem.subject problem.phrase := by
  constructor
  · rintro ⟨hcat, hdiag⟩
    refine ⟨?_, hcat⟩
    intro hfigure
    rw [diagnoseDefinition_of_figureOfSpeechMismatch hfigure] at hdiag
    cases hdiag
  · rintro ⟨hfigure, hcat⟩
    refine ⟨hcat, ?_⟩
    have hsame : ¬ sameCategory problem.subject problem.phrase.genus := hcat
    have hdiag : diagnoseDefinition problem = .categoryMismatch hsame := by
      unfold diagnoseDefinition
      simp [hfigure, hsame]
    simpa [DefinitionRefutationByCategoryMismatch] using hdiag

theorem diagnoseDefinition_eq_contraryMismatch_iff [PredicationalManual]
    {problem : PositionedDefinitionProblem} :
    (∃ h, diagnoseDefinition problem = .contraryMismatch h) ↔
      ¬ DefinitionRefutationByFigureOfSpeechMismatch problem ∧
        sameCategory problem.subject problem.phrase.genus ∧
          DefinitionRefutationByContraryMismatch problem.subject problem.phrase := by
  constructor
  · rintro ⟨hcontra, hdiag⟩
    have hfigure : ¬ DefinitionRefutationByFigureOfSpeechMismatch problem := by
      intro hfigure
      rw [diagnoseDefinition_of_figureOfSpeechMismatch hfigure] at hdiag
      cases hdiag
    have hsame : sameCategory problem.subject problem.phrase.genus := by
      by_contra hsame
      rcases (diagnoseDefinition_eq_categoryMismatch_iff (problem := problem)).2
        ⟨hfigure, hsame⟩ with ⟨hcat, hcatdiag⟩
      rw [hcatdiag] at hdiag
      cases hdiag
    exact ⟨hfigure, hsame, hcontra⟩
  · rintro ⟨hfigure, hsame, hcontra⟩
    refine ⟨hcontra, ?_⟩
    unfold diagnoseDefinition
    simp [hfigure, hsame, hcontra]

theorem diagnoseDefinition_eq_degreeMismatch_iff [PredicationalManual]
    {problem : PositionedDefinitionProblem} :
    (∃ h, diagnoseDefinition problem = .degreeMismatch h) ↔
      ¬ DefinitionRefutationByFigureOfSpeechMismatch problem ∧
        sameCategory problem.subject problem.phrase.genus ∧
          ¬ DefinitionRefutationByContraryMismatch problem.subject problem.phrase ∧
            DefinitionRefutationByDegreeMismatch problem.subject problem.phrase := by
  constructor
  · rintro ⟨hdegree, hdiag⟩
    have hfigure : ¬ DefinitionRefutationByFigureOfSpeechMismatch problem := by
      intro hfigure
      rw [diagnoseDefinition_of_figureOfSpeechMismatch hfigure] at hdiag
      cases hdiag
    have hsame : sameCategory problem.subject problem.phrase.genus := by
      by_contra hsame
      rcases (diagnoseDefinition_eq_categoryMismatch_iff (problem := problem)).2
        ⟨hfigure, hsame⟩ with ⟨hcat, hcatdiag⟩
      rw [hcatdiag] at hdiag
      cases hdiag
    have hcontra :
        ¬ DefinitionRefutationByContraryMismatch problem.subject problem.phrase := by
      intro hcontra
      rcases (diagnoseDefinition_eq_contraryMismatch_iff (problem := problem)).2
        ⟨hfigure, hsame, hcontra⟩ with ⟨hcontra', hcontradiag⟩
      rw [hcontradiag] at hdiag
      cases hdiag
    exact ⟨hfigure, hsame, hcontra, hdegree⟩
  · rintro ⟨hfigure, hsame, hcontra, hdegree⟩
    refine ⟨hdegree, ?_⟩
    unfold diagnoseDefinition
    simp [hfigure, hsame, hcontra, hdegree]

theorem diagnoseDefinition_eq_genusNotSaidOf_iff [PredicationalManual]
    {problem : PositionedDefinitionProblem} :
    (∃ h, diagnoseDefinition problem = .genusNotSaidOf h) ↔
      ¬ DefinitionRefutationByFigureOfSpeechMismatch problem ∧
        sameCategory problem.subject problem.phrase.genus ∧
          ¬ DefinitionRefutationByContraryMismatch problem.subject problem.phrase ∧
            ¬ DefinitionRefutationByDegreeMismatch problem.subject problem.phrase ∧
              DefinitionRefutationByGenusNotSaidOf problem.subject problem.phrase := by
  constructor
  · rintro ⟨hgenus, hdiag⟩
    have hfigure : ¬ DefinitionRefutationByFigureOfSpeechMismatch problem := by
      intro hfigure
      rw [diagnoseDefinition_of_figureOfSpeechMismatch hfigure] at hdiag
      cases hdiag
    have hsame : sameCategory problem.subject problem.phrase.genus := by
      by_contra hsame
      rcases (diagnoseDefinition_eq_categoryMismatch_iff (problem := problem)).2
        ⟨hfigure, hsame⟩ with ⟨hcat, hcatdiag⟩
      rw [hcatdiag] at hdiag
      cases hdiag
    have hcontra :
        ¬ DefinitionRefutationByContraryMismatch problem.subject problem.phrase := by
      intro hcontra
      rcases (diagnoseDefinition_eq_contraryMismatch_iff (problem := problem)).2
        ⟨hfigure, hsame, hcontra⟩ with ⟨hcontra', hcontradiag⟩
      rw [hcontradiag] at hdiag
      cases hdiag
    have hdegree :
        ¬ DefinitionRefutationByDegreeMismatch problem.subject problem.phrase := by
      intro hdegree
      rcases (diagnoseDefinition_eq_degreeMismatch_iff (problem := problem)).2
        ⟨hfigure, hsame, hcontra, hdegree⟩ with ⟨hdegree', hdegreediag⟩
      rw [hdegreediag] at hdiag
      cases hdiag
    exact ⟨hfigure, hsame, hcontra, hdegree, hgenus⟩
  · rintro ⟨hfigure, hsame, hcontra, hdegree, hgenus⟩
    refine ⟨hgenus, ?_⟩
    unfold diagnoseDefinition
    simp [hfigure, hsame, hcontra, hdegree, hgenus]

theorem diagnoseDefinition_eq_differentiaNotSaidOf_iff [PredicationalManual]
    {problem : PositionedDefinitionProblem} :
    (∃ h, diagnoseDefinition problem = .differentiaNotSaidOf h) ↔
      ¬ DefinitionRefutationByFigureOfSpeechMismatch problem ∧
        sameCategory problem.subject problem.phrase.genus ∧
          ¬ DefinitionRefutationByContraryMismatch problem.subject problem.phrase ∧
            ¬ DefinitionRefutationByDegreeMismatch problem.subject problem.phrase ∧
              ¬ DefinitionRefutationByGenusNotSaidOf problem.subject problem.phrase ∧
                DefinitionRefutationByDifferentiaNotSaidOf problem.subject problem.phrase := by
  constructor
  · rintro ⟨hdifferentia, hdiag⟩
    have hfigure : ¬ DefinitionRefutationByFigureOfSpeechMismatch problem := by
      intro hfigure
      rw [diagnoseDefinition_of_figureOfSpeechMismatch hfigure] at hdiag
      cases hdiag
    have hsame : sameCategory problem.subject problem.phrase.genus := by
      by_contra hsame
      rcases (diagnoseDefinition_eq_categoryMismatch_iff (problem := problem)).2
        ⟨hfigure, hsame⟩ with ⟨hcat, hcatdiag⟩
      rw [hcatdiag] at hdiag
      cases hdiag
    have hcontra :
        ¬ DefinitionRefutationByContraryMismatch problem.subject problem.phrase := by
      intro hcontra
      rcases (diagnoseDefinition_eq_contraryMismatch_iff (problem := problem)).2
        ⟨hfigure, hsame, hcontra⟩ with ⟨hcontra', hcontradiag⟩
      rw [hcontradiag] at hdiag
      cases hdiag
    have hdegree :
        ¬ DefinitionRefutationByDegreeMismatch problem.subject problem.phrase := by
      intro hdegree
      rcases (diagnoseDefinition_eq_degreeMismatch_iff (problem := problem)).2
        ⟨hfigure, hsame, hcontra, hdegree⟩ with ⟨hdegree', hdegreediag⟩
      rw [hdegreediag] at hdiag
      cases hdiag
    have hgenus :
        ¬ DefinitionRefutationByGenusNotSaidOf problem.subject problem.phrase := by
      intro hgenus
      rcases (diagnoseDefinition_eq_genusNotSaidOf_iff (problem := problem)).2
        ⟨hfigure, hsame, hcontra, hdegree, hgenus⟩ with ⟨hgenus', hgenusdiag⟩
      rw [hgenusdiag] at hdiag
      cases hdiag
    exact ⟨hfigure, hsame, hcontra, hdegree, hgenus, hdifferentia⟩
  · rintro ⟨hfigure, hsame, hcontra, hdegree, hgenus, hdifferentia⟩
    refine ⟨hdifferentia, ?_⟩
    unfold diagnoseDefinition
    simp [hfigure, hsame, hcontra, hdegree, hgenus, hdifferentia]

theorem diagnoseDefinition_eq_inSubject_iff [PredicationalManual]
    {problem : PositionedDefinitionProblem} :
    (∃ h, diagnoseDefinition problem = .inSubject h) ↔
      ¬ DefinitionRefutationByFigureOfSpeechMismatch problem ∧
        sameCategory problem.subject problem.phrase.genus ∧
          ¬ DefinitionRefutationByContraryMismatch problem.subject problem.phrase ∧
            ¬ DefinitionRefutationByDegreeMismatch problem.subject problem.phrase ∧
              ¬ DefinitionRefutationByGenusNotSaidOf problem.subject problem.phrase ∧
                ¬ DefinitionRefutationByDifferentiaNotSaidOf problem.subject problem.phrase ∧
                  DefinitionRefutationByInSubject problem.subject problem.phrase := by
  constructor
  · rintro ⟨hin, hdiag⟩
    have hfigure : ¬ DefinitionRefutationByFigureOfSpeechMismatch problem := by
      intro hfigure
      rw [diagnoseDefinition_of_figureOfSpeechMismatch hfigure] at hdiag
      cases hdiag
    have hsame : sameCategory problem.subject problem.phrase.genus := by
      by_contra hsame
      rcases (diagnoseDefinition_eq_categoryMismatch_iff (problem := problem)).2
        ⟨hfigure, hsame⟩ with ⟨hcat, hcatdiag⟩
      rw [hcatdiag] at hdiag
      cases hdiag
    have hcontra :
        ¬ DefinitionRefutationByContraryMismatch problem.subject problem.phrase := by
      intro hcontra
      rcases (diagnoseDefinition_eq_contraryMismatch_iff (problem := problem)).2
        ⟨hfigure, hsame, hcontra⟩ with ⟨hcontra', hcontradiag⟩
      rw [hcontradiag] at hdiag
      cases hdiag
    have hdegree :
        ¬ DefinitionRefutationByDegreeMismatch problem.subject problem.phrase := by
      intro hdegree
      rcases (diagnoseDefinition_eq_degreeMismatch_iff (problem := problem)).2
        ⟨hfigure, hsame, hcontra, hdegree⟩ with ⟨hdegree', hdegreediag⟩
      rw [hdegreediag] at hdiag
      cases hdiag
    have hgenus :
        ¬ DefinitionRefutationByGenusNotSaidOf problem.subject problem.phrase := by
      intro hgenus
      rcases (diagnoseDefinition_eq_genusNotSaidOf_iff (problem := problem)).2
        ⟨hfigure, hsame, hcontra, hdegree, hgenus⟩ with ⟨hgenus', hgenusdiag⟩
      rw [hgenusdiag] at hdiag
      cases hdiag
    have hdifferentia :
        ¬ DefinitionRefutationByDifferentiaNotSaidOf problem.subject problem.phrase := by
      intro hdifferentia
      rcases (diagnoseDefinition_eq_differentiaNotSaidOf_iff (problem := problem)).2
        ⟨hfigure, hsame, hcontra, hdegree, hgenus, hdifferentia⟩ with
          ⟨hdifferentia', hdifferentiadiag⟩
      rw [hdifferentiadiag] at hdiag
      cases hdiag
    exact ⟨hfigure, hsame, hcontra, hdegree, hgenus, hdifferentia, hin⟩
  · rintro ⟨hfigure, hsame, hcontra, hdegree, hgenus, hdifferentia, hin⟩
    refine ⟨hin, ?_⟩
    unfold diagnoseDefinition
    simp [hfigure, hsame, hcontra, hdegree, hgenus, hdifferentia, hin]

theorem diagnoseDefinition_eq_admissible_iff [PredicationalManual]
    {problem : PositionedDefinitionProblem} :
    (∃ dossier, diagnoseDefinition problem = .admissible dossier) ↔
      DialecticalDefinitionDossier problem.subject problem.phrase := by
  constructor
  · rintro ⟨dossier, _⟩
    exact dossier
  · intro dossier
    refine ⟨dossier, ?_⟩
    have hfigure : ¬ DefinitionRefutationByFigureOfSpeechMismatch problem :=
      DialecticalDefinitionDossier.notFigureOfSpeechMismatch dossier
    have hsame : sameCategory problem.subject problem.phrase.genus := dossier.sameCategory
    have hcontra :
        ¬ DefinitionRefutationByContraryMismatch problem.subject problem.phrase :=
      Aristotle.Categories.DialecticalDefinitionDossier.notContraryMismatch dossier
    have hdegree :
        ¬ DefinitionRefutationByDegreeMismatch problem.subject problem.phrase :=
      Aristotle.Categories.DialecticalDefinitionDossier.notDegreeMismatch dossier
    have hgenus :
        ¬ DefinitionRefutationByGenusNotSaidOf problem.subject problem.phrase :=
      Aristotle.Categories.DialecticalDefinitionDossier.notGenusNotSaidOf dossier
    have hdifferentia :
        ¬ DefinitionRefutationByDifferentiaNotSaidOf problem.subject problem.phrase :=
      Aristotle.Categories.DialecticalDefinitionDossier.notDifferentiaNotSaidOf dossier
    have hin :
        ¬ DefinitionRefutationByInSubject problem.subject problem.phrase :=
      Aristotle.Categories.DialecticalDefinitionDossier.notInSubject_refutation dossier
    unfold diagnoseDefinition
    simp [hfigure, hsame, hcontra, hdegree, hgenus, hdifferentia, hin]

theorem diagnoseDefinition_not_admissible_of_surfaceTrapMismatch [PredicationalManual]
    {problem : PositionedDefinitionProblem}
    (h : DefinitionRefutationBySurfaceTrapMismatch problem) :
    ¬ ∃ dossier, diagnoseDefinition problem = .admissible dossier := by
  intro hadmissible
  exact definitionSurfaceTrapMismatch_not_dossier h
    ((diagnoseDefinition_eq_admissible_iff (problem := problem)).1 hadmissible)

noncomputable def diagnoseProprium [PredicationalManual]
    (problem : PositionedPropriumProblem) : PropriumDiagnosis problem := by
  classical
  by_cases hprop : PropriumRefutationByNotSaidOf problem.subject problem.property
  · exact .notSaidOf hprop
  · by_cases hin : PropriumRefutationByInSubject problem.subject problem.property
    · exact .inSubject hin
    · exact .admissible
        { propertySaidOf := by
            by_contra hnot
            exact hprop hnot
          notInSubject := hin }

theorem contraryMismatch_of_recognizedSubstance [Manual]
    {subject genusTerm : PositionedCandidate}
    (hsubject : RecognizedSubstance subject)
    (hgenus : hasContrary genusTerm) :
    GenusRefutationByContraryMismatch subject genusTerm := by
  refine ⟨hgenus, ?_⟩
  intro hcontra
  rcases hsubject with hsubject | hsubject
  · exact hsubject.idia.lacksContrary hcontra
  · exact hsubject.idia.lacksContrary hcontra

theorem degreeMismatch_of_recognizedSubstance [Manual]
    {subject genusTerm : PositionedCandidate}
    (hsubject : RecognizedSubstance subject)
    (hgenus : admitsMoreAndLess genusTerm) :
    GenusRefutationByDegreeMismatch subject genusTerm := by
  refine ⟨hgenus, ?_⟩
  intro hdegrees
  rcases hsubject with hsubject | hsubject
  · exact hsubject.idia.lacksMoreAndLess hdegrees
  · exact hsubject.idia.lacksMoreAndLess hdegrees

inductive ThesisStage [PredicationalManual]
  | raw (problem : Problem)
  | screeningBlockedByTerm (problem : Problem)
      (side : ProblemSide) (blocked : BlockedScreening)
  | screeningBlockedDefinition (problem : Problem)
      (failure : DefinitionScreeningFailure)
  | screened (problem : ScreenedProblem)
  | positioned (problem : PositionedProblem)
  | provisionalGenus (problem : PositionedGenusProblem)
      (dossier : GenusDossier problem.subject problem.genusTerm)
  | refutedGenusByFigureOfSpeechMismatch (problem : PositionedGenusProblem)
      (h : GenusRefutationByFigureOfSpeechMismatch problem)
  | refutedGenusByCategoryMismatch (problem : PositionedGenusProblem)
      (h : ¬ sameCategory problem.subject problem.genusTerm)
  | refutedGenusByContraryMismatch (problem : PositionedGenusProblem)
      (h : GenusRefutationByContraryMismatch problem.subject problem.genusTerm)
  | refutedGenusByDegreeMismatch (problem : PositionedGenusProblem)
      (h : GenusRefutationByDegreeMismatch problem.subject problem.genusTerm)
  | refutedGenusByNotSaidOf (problem : PositionedGenusProblem)
      (h : GenusRefutationByNotSaidOf problem.subject problem.genusTerm)
  | provisionalDefinition (problem : PositionedDefinitionProblem)
      (dossier : DialecticalDefinitionDossier problem.subject problem.phrase)
  | refutedDefinitionByFigureOfSpeechMismatch (problem : PositionedDefinitionProblem)
      (h : DefinitionRefutationByFigureOfSpeechMismatch problem)
  | refutedDefinitionByCategoryMismatch (problem : PositionedDefinitionProblem)
      (h : DefinitionRefutationByCategoryMismatch problem.subject problem.phrase)
  | refutedDefinitionByContraryMismatch (problem : PositionedDefinitionProblem)
      (h : DefinitionRefutationByContraryMismatch problem.subject problem.phrase)
  | refutedDefinitionByDegreeMismatch (problem : PositionedDefinitionProblem)
      (h : DefinitionRefutationByDegreeMismatch problem.subject problem.phrase)
  | refutedDefinitionByGenusNotSaidOf (problem : PositionedDefinitionProblem)
      (h : DefinitionRefutationByGenusNotSaidOf problem.subject problem.phrase)
  | refutedDefinitionByDifferentiaNotSaidOf (problem : PositionedDefinitionProblem)
      (h : DefinitionRefutationByDifferentiaNotSaidOf problem.subject problem.phrase)
  | refutedDefinitionByInSubject (problem : PositionedDefinitionProblem)
      (h : DefinitionRefutationByInSubject problem.subject problem.phrase)
  | provisionalProprium (problem : PositionedPropriumProblem)
      (dossier : PropriumDossier problem.subject problem.property)
  | refutedPropriumByNotSaidOf (problem : PositionedPropriumProblem)
      (h : PropriumRefutationByNotSaidOf problem.subject problem.property)
  | refutedPropriumByInSubject (problem : PositionedPropriumProblem)
      (h : PropriumRefutationByInSubject problem.subject problem.property)

namespace ThesisStage

def problem [PredicationalManual] : ThesisStage → Problem
  | .raw problem => problem
  | .screeningBlockedByTerm problem _ _ => problem
  | .screeningBlockedDefinition problem _ => problem
  | .screened problem => problem.toProblem
  | .positioned problem => problem.toProblem
  | .provisionalGenus problem _ => problem.toProblem
  | .refutedGenusByFigureOfSpeechMismatch problem _ => problem.toProblem
  | .refutedGenusByCategoryMismatch problem _ => problem.toProblem
  | .refutedGenusByContraryMismatch problem _ => problem.toProblem
  | .refutedGenusByDegreeMismatch problem _ => problem.toProblem
  | .refutedGenusByNotSaidOf problem _ => problem.toProblem
  | .provisionalDefinition problem _ => problem.toProblem
  | .refutedDefinitionByFigureOfSpeechMismatch problem _ => problem.toProblem
  | .refutedDefinitionByCategoryMismatch problem _ => problem.toProblem
  | .refutedDefinitionByContraryMismatch problem _ => problem.toProblem
  | .refutedDefinitionByDegreeMismatch problem _ => problem.toProblem
  | .refutedDefinitionByGenusNotSaidOf problem _ => problem.toProblem
  | .refutedDefinitionByDifferentiaNotSaidOf problem _ => problem.toProblem
  | .refutedDefinitionByInSubject problem _ => problem.toProblem
  | .provisionalProprium problem _ => problem.toProblem
  | .refutedPropriumByNotSaidOf problem _ => problem.toProblem
  | .refutedPropriumByInSubject problem _ => problem.toProblem

def statements [PredicationalManual] (stage : ThesisStage) : List Categorical :=
  stage.problem.statements

def statement? [PredicationalManual] (stage : ThesisStage) : Option Categorical :=
  stage.statements.head?

end ThesisStage

noncomputable def stagePositionedProblem [PredicationalManual]
    (problem : PositionedProblem) : ThesisStage := by
  classical
  cases problem with
  | predication subject predicate =>
      exact .positioned (.predication subject predicate)
  | genus subject genusTerm =>
      let problem : PositionedGenusProblem := ⟨subject, genusTerm⟩
      cases diagnoseGenus problem with
      | admissible dossier => exact .provisionalGenus problem dossier
      | figureOfSpeechMismatch h => exact .refutedGenusByFigureOfSpeechMismatch problem h
      | categoryMismatch h => exact .refutedGenusByCategoryMismatch problem h
      | contraryMismatch h => exact .refutedGenusByContraryMismatch problem h
      | degreeMismatch h => exact .refutedGenusByDegreeMismatch problem h
      | notSaidOf h => exact .refutedGenusByNotSaidOf problem h
  | definition subject phrase =>
      let problem : PositionedDefinitionProblem := ⟨subject, phrase⟩
      cases diagnoseDefinition problem with
      | admissible dossier => exact .provisionalDefinition problem dossier
      | figureOfSpeechMismatch h =>
          exact .refutedDefinitionByFigureOfSpeechMismatch problem h
      | categoryMismatch h => exact .refutedDefinitionByCategoryMismatch problem h
      | contraryMismatch h => exact .refutedDefinitionByContraryMismatch problem h
      | degreeMismatch h => exact .refutedDefinitionByDegreeMismatch problem h
      | genusNotSaidOf h => exact .refutedDefinitionByGenusNotSaidOf problem h
      | differentiaNotSaidOf h =>
          exact .refutedDefinitionByDifferentiaNotSaidOf problem h
      | inSubject h => exact .refutedDefinitionByInSubject problem h
  | proprium subject property =>
      let problem : PositionedPropriumProblem := ⟨subject, property⟩
      cases diagnoseProprium problem with
      | admissible dossier => exact .provisionalProprium problem dossier
      | notSaidOf h => exact .refutedPropriumByNotSaidOf problem h
      | inSubject h => exact .refutedPropriumByInSubject problem h

/--
Advance a screened problem as far as the public staged API can currently take it.
If categorial positioning is unavailable, the workflow records that screening was
the furthest achieved stage.
-/
noncomputable def stageScreenedProblem [PredicationalManual]
    (problem : ScreenedProblem) : ThesisStage := by
  classical
  match positionScreenedProblem? problem with
  | some positioned => exact stagePositionedProblem positioned
  | none => exact .screened problem

/--
Advance a raw dialectical problem through screening, positioning, and diagnosis,
preserving explicit screening failure reasons rather than collapsing them into
`Option`-style loss.
-/
noncomputable def stageProblem [PredicationalManual]
    (problem : Problem) : ThesisStage := by
  classical
  match screenProblem problem with
  | .blockedTerm blockedProblem side blocked =>
      exact .screeningBlockedByTerm blockedProblem side blocked
  | .blockedDefinition blockedProblem failure =>
      exact .screeningBlockedDefinition blockedProblem failure
  | .screened screenedProblem =>
      exact stageScreenedProblem screenedProblem

theorem stageScreenedProblem_of_unpositioned [PredicationalManual]
    {problem : ScreenedProblem}
    (h : positionScreenedProblem? problem = none) :
    stageScreenedProblem problem = .screened problem := by
  unfold stageScreenedProblem
  simp [h]

theorem stageScreenedProblem_of_positioned [PredicationalManual]
    {screened : ScreenedProblem} {positioned : PositionedProblem}
    (h : positionScreenedProblem? screened = some positioned) :
    stageScreenedProblem screened = stagePositionedProblem positioned := by
  unfold stageScreenedProblem
  simp [h]

theorem stageProblem_of_blockedTerm [PredicationalManual]
    {problem : Problem} {side : ProblemSide} {blocked : BlockedScreening}
    (h : screenProblem problem = .blockedTerm problem side blocked) :
    stageProblem problem = .screeningBlockedByTerm problem side blocked := by
  unfold stageProblem
  simp [h]

theorem stageProblem_of_blockedDefinition [PredicationalManual]
    {problem : Problem} {failure : DefinitionScreeningFailure}
    (h : screenProblem problem = .blockedDefinition problem failure) :
    stageProblem problem = .screeningBlockedDefinition problem failure := by
  unfold stageProblem
  simp [h]

theorem stageProblem_of_screened [PredicationalManual]
    {problem : Problem} {screened : ScreenedProblem}
    (h : screenProblem problem = .screened screened) :
    stageProblem problem = stageScreenedProblem screened := by
  unfold stageProblem
  simp [h]

/--
Minimal state for a dialectical exchange. Relative to Smith's Book-VIII
commentary, this is intentionally partial: it keeps respondent, thesis,
concessions, and available endoxa, but it does not yet encode the fuller
questioner-side arrangement, concealment, or objection machinery.
-/
structure GameState where
  respondent : RespondentKind
  thesis : Option Problem := none
  concessions : List Categorical
  availableEndoxa : List Endoxon := []

namespace GameState

def withThesis (state : GameState) (problem : Problem) : GameState :=
  { state with thesis := some problem }

def clearThesis (state : GameState) : GameState :=
  { state with thesis := none }

/--
Install a raw thesis into the game state and return the staged interpretation
immediately, so callers do not need to separately update the state and then ask
for `stagedThesis?`.
-/
noncomputable def proposeThesis [PredicationalManual]
    (state : GameState) (problem : Problem) : GameState × ThesisStage :=
  let next := state.withThesis problem
  (next, stageProblem problem)

noncomputable def stagedThesis? [PredicationalManual]
    (state : GameState) : Option ThesisStage :=
  state.thesis.map stageProblem

def thesisStatements? (state : GameState) : Option (List Categorical) :=
  state.thesis.map Problem.statements

def thesisStatement? (state : GameState) : Option Categorical :=
  state.thesisStatements?.bind List.head?

@[simp] theorem thesis_withThesis (state : GameState) (problem : Problem) :
    (state.withThesis problem).thesis = some problem := by
  rfl

@[simp] theorem thesis_clearThesis (state : GameState) :
    state.clearThesis.thesis = none := by
  rfl

@[simp] theorem respondent_withThesis (state : GameState) (problem : Problem) :
    (state.withThesis problem).respondent = state.respondent := by
  rfl

@[simp] theorem concessions_withThesis (state : GameState) (problem : Problem) :
    (state.withThesis problem).concessions = state.concessions := by
  rfl

@[simp] theorem availableEndoxa_withThesis (state : GameState) (problem : Problem) :
    (state.withThesis problem).availableEndoxa = state.availableEndoxa := by
  rfl

@[simp] theorem respondent_clearThesis (state : GameState) :
    state.clearThesis.respondent = state.respondent := by
  rfl

@[simp] theorem concessions_clearThesis (state : GameState) :
    state.clearThesis.concessions = state.concessions := by
  rfl

@[simp] theorem availableEndoxa_clearThesis (state : GameState) :
    state.clearThesis.availableEndoxa = state.availableEndoxa := by
  rfl

@[simp] theorem thesisStatements?_withThesis (state : GameState) (problem : Problem) :
    (state.withThesis problem).thesisStatements? = some problem.statements := by
  rfl

@[simp] theorem thesisStatements?_clearThesis (state : GameState) :
    state.clearThesis.thesisStatements? = none := by
  rfl

@[simp] theorem thesisStatement?_withThesis (state : GameState) (problem : Problem) :
    (state.withThesis problem).thesisStatement? = problem.statement? := by
  simp [thesisStatement?, Problem.statement?]

@[simp] theorem thesisStatement?_clearThesis (state : GameState) :
    state.clearThesis.thesisStatement? = none := by
  simp [thesisStatement?]

@[simp] theorem stagedThesis?_withThesis [PredicationalManual]
    (state : GameState) (problem : Problem) :
    (state.withThesis problem).stagedThesis? = some (stageProblem problem) := by
  simp [stagedThesis?, withThesis]

@[simp] theorem stagedThesis?_clearThesis [PredicationalManual]
    (state : GameState) :
    state.clearThesis.stagedThesis? = none := by
  simp [stagedThesis?, clearThesis]

@[simp] theorem proposeThesis_fst [PredicationalManual]
    (state : GameState) (problem : Problem) :
    (state.proposeThesis problem).1 = state.withThesis problem := by
  rfl

@[simp] theorem proposeThesis_snd [PredicationalManual]
    (state : GameState) (problem : Problem) :
    (state.proposeThesis problem).2 = stageProblem problem := by
  rfl

end GameState

def Problem.refutationTargets (problem : Problem) : List Categorical :=
  problem.statements.map Categorical.contradictory

namespace GameState

def thesisRefutationTargets? (state : GameState) : Option (List Categorical) :=
  state.thesis.map Problem.refutationTargets

@[simp] theorem thesisRefutationTargets?_withThesis
    (state : GameState) (problem : Problem) :
    (state.withThesis problem).thesisRefutationTargets? = some problem.refutationTargets := by
  rfl

@[simp] theorem thesisRefutationTargets?_clearThesis (state : GameState) :
    state.clearThesis.thesisRefutationTargets? = none := by
  rfl

end GameState

/--
Answerer-side concession step. It only records a concession when the proposed
endoxon is both available in the current exchange and genuinely acceptable to
the respondent. This is a small executable fragment of the Book-VIII answerer
discipline, not yet the full theory of objections and blame.
-/
noncomputable def askConcession (art : DialecticalArt)
    (state : GameState) (premise : Endoxon) (agreed : Bool) : GameState := by
  classical
  exact
    if agreed then
      if havail : premise ∈ state.availableEndoxa then
        if hacc : premise.acceptableIn art state.respondent then
          { state with concessions := premise.proposition :: state.concessions }
        else
          state
      else
        state
    else
      state

theorem askConcession_adds_available (art : DialecticalArt)
    (state : GameState) (premise : Endoxon)
    (hmem : premise ∈ state.availableEndoxa)
    (hacc : premise.acceptableIn art state.respondent) :
    premise.proposition ∈ (askConcession art state premise true).concessions := by
  classical
  unfold askConcession
  simp [hmem, hacc]

theorem askConcession_ignores_unavailable (art : DialecticalArt)
    (state : GameState) (premise : Endoxon)
    (hmem : premise ∉ state.availableEndoxa) :
    askConcession art state premise true = state := by
  classical
  unfold askConcession
  simp [hmem]

theorem askConcession_ignores_unacceptable (art : DialecticalArt)
    (state : GameState) (premise : Endoxon)
    (hmem : premise ∈ state.availableEndoxa)
    (hacc : ¬ premise.acceptableIn art state.respondent) :
    askConcession art state premise true = state := by
  classical
  unfold askConcession
  simp [hmem, hacc]

@[simp] theorem thesis_askConcession (art : DialecticalArt)
    (state : GameState) (premise : Endoxon) (agreed : Bool) :
    (askConcession art state premise agreed).thesis = state.thesis := by
  classical
  unfold askConcession
  by_cases hagreed : agreed
  · by_cases hmem : premise ∈ state.availableEndoxa
    · by_cases hacc : premise.acceptableIn art state.respondent
      · simp [hagreed, hmem, hacc]
      · simp [hagreed, hmem, hacc]
    · simp [hagreed, hmem]
  · simp [hagreed]

namespace GameState

@[simp] theorem thesisStatements?_askConcession
    (art : DialecticalArt) (state : GameState) (premise : Endoxon) (agreed : Bool) :
    (askConcession art state premise agreed).thesisStatements? =
      state.thesisStatements? := by
  simp [thesisStatements?, thesis_askConcession]

@[simp] theorem thesisStatement?_askConcession
    (art : DialecticalArt) (state : GameState) (premise : Endoxon) (agreed : Bool) :
    (askConcession art state premise agreed).thesisStatement? =
      state.thesisStatement? := by
  simp [thesisStatement?, GameState.thesisStatements?_askConcession]

@[simp] theorem thesisRefutationTargets?_askConcession
    (art : DialecticalArt) (state : GameState) (premise : Endoxon) (agreed : Bool) :
    (askConcession art state premise agreed).thesisRefutationTargets? =
      state.thesisRefutationTargets? := by
  simp [thesisRefutationTargets?, thesis_askConcession]

end GameState

structure StagedSession [PredicationalManual] where
  state : GameState
  stagedThesis : Option ThesisStage
  coherent : stagedThesis = state.stagedThesis?

namespace StagedSession

noncomputable def ofState [PredicationalManual] (state : GameState) : StagedSession :=
  { state := state
    stagedThesis := state.stagedThesis?
    coherent := rfl }

noncomputable def withThesis [PredicationalManual]
    (session : StagedSession) (problem : Problem) : StagedSession :=
  ofState (session.state.withThesis problem)

noncomputable def clearThesis [PredicationalManual]
    (session : StagedSession) : StagedSession :=
  ofState session.state.clearThesis

noncomputable def proposeThesis [PredicationalManual]
    (session : StagedSession) (problem : Problem) : StagedSession :=
  withThesis session problem

noncomputable def askConcession [PredicationalManual]
    (art : DialecticalArt) (session : StagedSession)
    (premise : Endoxon) (agreed : Bool) : StagedSession :=
  ofState (Aristotle.Dialectic.askConcession art session.state premise agreed)

@[simp] theorem ofState_state [PredicationalManual] (state : GameState) :
    (ofState state).state = state := by
  rfl

@[simp] theorem ofState_stagedThesis [PredicationalManual] (state : GameState) :
    (ofState state).stagedThesis = state.stagedThesis? := by
  rfl

def thesisStatements? [PredicationalManual] (session : StagedSession) : Option (List Categorical) :=
  session.state.thesisStatements?

def thesisStatement? [PredicationalManual] (session : StagedSession) : Option Categorical :=
  session.state.thesisStatement?

def thesisRefutationTargets? [PredicationalManual] (session : StagedSession) : Option (List Categorical) :=
  session.state.thesisRefutationTargets?

@[simp] theorem ofState_thesisStatements? [PredicationalManual] (state : GameState) :
    StagedSession.thesisStatements? (ofState state) = state.thesisStatements? := by
  rfl

@[simp] theorem ofState_thesisStatement? [PredicationalManual] (state : GameState) :
    StagedSession.thesisStatement? (ofState state) = state.thesisStatement? := by
  rfl

@[simp] theorem ofState_thesisRefutationTargets? [PredicationalManual] (state : GameState) :
    StagedSession.thesisRefutationTargets? (ofState state) =
      state.thesisRefutationTargets? := by
  rfl

@[simp] theorem withThesis_state [PredicationalManual]
    (session : StagedSession) (problem : Problem) :
    (withThesis session problem).state = session.state.withThesis problem := by
  rfl

@[simp] theorem withThesis_stagedThesis [PredicationalManual]
    (session : StagedSession) (problem : Problem) :
    (withThesis session problem).stagedThesis = some (stageProblem problem) := by
  simp [withThesis, ofState]

@[simp] theorem clearThesis_state [PredicationalManual]
    (session : StagedSession) :
    (clearThesis session).state = session.state.clearThesis := by
  rfl

@[simp] theorem clearThesis_stagedThesis [PredicationalManual]
    (session : StagedSession) :
    (clearThesis session).stagedThesis = none := by
  simp [clearThesis, ofState]

@[simp] theorem proposeThesis_state [PredicationalManual]
    (session : StagedSession) (problem : Problem) :
    (proposeThesis session problem).state = session.state.withThesis problem := by
  simp [proposeThesis, withThesis]

@[simp] theorem proposeThesis_stagedThesis [PredicationalManual]
    (session : StagedSession) (problem : Problem) :
    (proposeThesis session problem).stagedThesis = some (stageProblem problem) := by
  simp [proposeThesis, withThesis]

@[simp] theorem askConcession_state [PredicationalManual]
    (art : DialecticalArt) (session : StagedSession)
    (premise : Endoxon) (agreed : Bool) :
    (askConcession art session premise agreed).state =
      Aristotle.Dialectic.askConcession art session.state premise agreed := by
  rfl

@[simp] theorem askConcession_stagedThesis [PredicationalManual]
    (art : DialecticalArt) (session : StagedSession)
    (premise : Endoxon) (agreed : Bool) :
    (askConcession art session premise agreed).stagedThesis = session.stagedThesis := by
  calc
    (askConcession art session premise agreed).stagedThesis =
        (Aristotle.Dialectic.askConcession art session.state premise agreed).stagedThesis? := by
          simp [askConcession, ofState]
    _ = session.state.stagedThesis? := by
          simp [GameState.stagedThesis?, thesis_askConcession]
    _ = session.stagedThesis := by
          simpa using session.coherent.symm

@[simp] theorem askConcession_thesisStatement? [PredicationalManual]
    (art : DialecticalArt) (session : StagedSession)
    (premise : Endoxon) (agreed : Bool) :
    StagedSession.thesisStatement? (askConcession art session premise agreed) =
      StagedSession.thesisStatement? session := by
  simp [StagedSession.thesisStatement?, StagedSession.askConcession,
    StagedSession.ofState]

@[simp] theorem askConcession_thesisRefutationTargets? [PredicationalManual]
    (art : DialecticalArt) (session : StagedSession)
    (premise : Endoxon) (agreed : Bool) :
    StagedSession.thesisRefutationTargets? (askConcession art session premise agreed) =
      StagedSession.thesisRefutationTargets? session := by
  simp [StagedSession.thesisRefutationTargets?, StagedSession.askConcession,
    StagedSession.ofState]

end StagedSession

namespace GameState

noncomputable def session [PredicationalManual] (state : GameState) : StagedSession :=
  StagedSession.ofState state

@[simp] theorem session_state [PredicationalManual] (state : GameState) :
    state.session.state = state := by
  rfl

@[simp] theorem session_stagedThesis [PredicationalManual] (state : GameState) :
    state.session.stagedThesis = state.stagedThesis? := by
  rfl

end GameState

/--
`Topics` VIII distinguishes theses according to whether they are acceptable,
unacceptable, or neither, and whether this standing is without qualification
or relative to the respondent / delegated position being defended.
-/
inductive ApparentAcceptability where
  | acceptable
  | unacceptable
  | neither
  deriving DecidableEq, Repr, Inhabited

/--
Book VIII allows a thesis to be assessed either without qualification, from the
respondent's own point of view, or relative to another position the respondent
has taken over for the exercise.
-/
inductive ThesisReference where
  | unqualified
  | respondent
  | delegated (source : RespondentKind)
  deriving DecidableEq, Repr, Inhabited

/--
An assigned thesis is not merely a problem-shape: it comes into the exercise
with a dialectical standing that governs what a good answerer should concede.
-/
structure AssignedThesis where
  problem : Problem
  standing : ApparentAcceptability
  reference : ThesisReference := .unqualified
  deriving DecidableEq, Repr

namespace ApparentAcceptability

/--
Relative to an assigned thesis, the questioner aims at the contradictory
standing for the resulting conclusion: acceptable theses are attacked toward an
unacceptable consequence, and unacceptable theses toward an acceptable one.
-/
def contrary : ApparentAcceptability → ApparentAcceptability
  | .acceptable => .unacceptable
  | .unacceptable => .acceptable
  | .neither => .neither

@[simp] theorem contrary_contrary (standing : ApparentAcceptability) :
    contrary (contrary standing) = standing := by
  cases standing <;> rfl

end ApparentAcceptability

namespace AssignedThesis

def expectedConclusionStanding (thesis : AssignedThesis) : ApparentAcceptability :=
  thesis.standing.contrary

@[simp] theorem expectedConclusionStanding_expectedConclusionStanding
    (thesis : AssignedThesis) :
    thesis.expectedConclusionStanding.contrary = thesis.standing := by
  simp [expectedConclusionStanding, ApparentAcceptability.contrary_contrary]

end AssignedThesis

/--
`Topics` I.14 sorts collected material according to whether it belongs to
practical choice, theoretical inquiry, or widely applicable/logical discussion.
-/
inductive PremissDomain where
  | ethical
  | scientific
  | logical
  deriving DecidableEq, Repr, Inhabited

/--
Collected premisses need not come only from raw endoxa: Aristotle also permits
similarities, negated contraries, parallel contrary transformations, arts, and
written authorities to feed the dialectician's tables.
-/
inductive CollectedPremissOrigin where
  | direct (source : RespondentKind)
  | similarTo (base : Categorical)
  | contraryByNegation (base : Categorical)
  | parallelContrary (base : Categorical)
  | fromArt (authority : DialecticalTerm)
  | fromWriting (authority : DialecticalTerm)
  | apparentConcession
  deriving DecidableEq, Repr, Inhabited

/--
A premiss once collected is stored together with its dialectical provenance and
domain-classification, mirroring the tabular preparation urged in `Topics` I.14.
-/
structure CollectedPremiss where
  proposition : Categorical
  origin : CollectedPremissOrigin
  domain : PremissDomain
  deriving DecidableEq, Repr

namespace CollectedPremiss

def subject (entry : CollectedPremiss) : DialecticalTerm :=
  entry.proposition.subject

def predicate (entry : CollectedPremiss) : DialecticalTerm :=
  entry.proposition.predicate

end CollectedPremiss

/--
Aristotle's `diagraphai` are modeled as premiss tables that can be searched by
subject, domain, or source-type rather than as an undifferentiated heap.
-/
structure PremissTable where
  entries : List CollectedPremiss
  deriving Repr

namespace PremissTable

def aboutSubject (table : PremissTable) (subject : DialecticalTerm) : List CollectedPremiss :=
  table.entries.filter (fun entry => entry.subject = subject)

def ofDomain (table : PremissTable) (domain : PremissDomain) : List CollectedPremiss :=
  table.entries.filter (fun entry => entry.domain = domain)

def ofOrigin (table : PremissTable)
    (p : CollectedPremissOrigin → Prop) [DecidablePred p] : List CollectedPremiss :=
  table.entries.filter (fun entry => p entry.origin)

@[simp] theorem mem_aboutSubject_iff (table : PremissTable)
    (subject : DialecticalTerm) (entry : CollectedPremiss) :
    entry ∈ table.aboutSubject subject ↔
      entry ∈ table.entries ∧ entry.subject = subject := by
  simp [aboutSubject, CollectedPremiss.subject]

@[simp] theorem mem_ofDomain_iff (table : PremissTable)
    (domain : PremissDomain) (entry : CollectedPremiss) :
    entry ∈ table.ofDomain domain ↔
      entry ∈ table.entries ∧ entry.domain = domain := by
  simp [ofDomain]

end PremissTable

/--
Book VIII distinguishes the premisses strictly needed for the deduction from
additional questions used for induction, bulk, concealment, or clarity.
-/
inductive QuestionRole where
  | necessary
  | inductionSupport
  | bulk
  | concealment
  | clarity
  deriving DecidableEq, Repr, Inhabited

namespace QuestionRole

def isNecessary : QuestionRole → Bool
  | .necessary => true
  | _ => false

end QuestionRole

/--
The questioner can obtain premisses directly, by standing off, by induction,
through similarity, through co-ordinate definition, or by interleaving
otherwise connected steps to conceal the route to the thesis.
-/
inductive ArrangementTechnique where
  | direct
  | standingOff
  | induction
  | similarity
  | coordinateDefinition
  | interleaved
  deriving DecidableEq, Repr, Inhabited

/--
An arranged question records not merely what is asked, but what role it plays
and by which tactical route it is being obtained.
-/
structure ArrangedQuestion where
  premiss : CollectedPremiss
  role : QuestionRole
  technique : ArrangementTechnique
  deriving DecidableEq, Repr

/--
An arranged exchange packages the Book-VIII ordering of questions around an
assigned thesis and one of its refutatory targets. The `conclusionNotAsked`
field enforces Aristotle's instruction not to put the conclusion itself as a
question.
-/
structure ArrangedExchange where
  thesis : AssignedThesis
  target : Categorical
  questions : List ArrangedQuestion
  aligned : target ∈ thesis.problem.refutationTargets
  conclusionNotAsked : ∀ q ∈ questions, q.premiss.proposition ≠ target

namespace ArrangedExchange

def necessaryQuestions (exchange : ArrangedExchange) : List ArrangedQuestion :=
  exchange.questions.filter (fun question => question.role = .necessary)

def additionalQuestions (exchange : ArrangedExchange) : List ArrangedQuestion :=
  exchange.questions.filter (fun question => question.role ≠ .necessary)

@[simp] theorem mem_necessaryQuestions_iff (exchange : ArrangedExchange)
    (question : ArrangedQuestion) :
    question ∈ exchange.necessaryQuestions ↔
      question ∈ exchange.questions ∧ question.role = .necessary := by
  simp [necessaryQuestions]

@[simp] theorem mem_additionalQuestions_iff (exchange : ArrangedExchange)
    (question : ArrangedQuestion) :
    question ∈ exchange.additionalQuestions ↔
      question ∈ exchange.questions ∧ question.role ≠ .necessary := by
  simp [additionalQuestions]

theorem question_ne_target (exchange : ArrangedExchange)
    {question : ArrangedQuestion} (h : question ∈ exchange.questions) :
    question.premiss.proposition ≠ exchange.target :=
  exchange.conclusionNotAsked question h

end ArrangedExchange

/--
When induction is used in debate, Aristotle distinguishes cases where the
universal already has a common name from those where the dialectician must coin
one in order to block evasive objections.
-/
inductive InductionDesignation where
  | named (term : DialecticalTerm)
  | coined (term : DialecticalTerm)
  | anonymous
  deriving DecidableEq, Repr, Inhabited

/--
The dialectical induction stores the conceded cases together with the universal
to be asked and the way in which that universal is designated.
-/
structure DialecticalInduction where
  cases : List Categorical
  universal : Categorical
  designation : InductionDesignation := .anonymous
  nonempty : cases ≠ []

namespace DialecticalInduction

def mayAskForObjection (induction : DialecticalInduction) : Prop :=
  induction.cases ≠ []

@[simp] theorem mayAskForObjection_iff (induction : DialecticalInduction) :
    induction.mayAskForObjection ↔ induction.cases ≠ [] := by
  rfl

@[simp] theorem mayAskForObjection_holds (induction : DialecticalInduction) :
    induction.mayAskForObjection := induction.nonempty

end DialecticalInduction

/--
Book VIII distinguishes objections from equivocation from objections by fresh
counterinstance; only in the unique-case situation may the answerer object by
appealing to the originally proposed case itself.
-/
inductive InductionObjectionKind where
  | equivocalCase (term : DialecticalTerm)
  | freshCounterinstance (counterexample : Categorical)
  | uniqueCounterinstance (counterexample : Categorical)
  deriving DecidableEq, Repr, Inhabited

structure InductionObjection where
  kind : InductionObjectionKind
  deriving DecidableEq, Repr

namespace InductionObjection

def properAgainst (objection : InductionObjection)
    (induction : DialecticalInduction) : Prop :=
  match objection.kind with
  | .equivocalCase _ => True
  | .freshCounterinstance counterexample => counterexample ∉ induction.cases
  | .uniqueCounterinstance _ => True

end InductionObjection

/--
When a sound objection targets the thing itself rather than an equivocation,
Aristotle recommends subtracting the exceptional case and restating the
remainder as the new universal.
-/
inductive UniversalRepair where
  | distinction (term : DialecticalTerm)
  | subtraction (refined : Categorical) (excludedCases : List Categorical)
  deriving DecidableEq, Repr, Inhabited

namespace UniversalRepair

def repairs (repair : UniversalRepair) (objection : InductionObjection) : Prop :=
  match repair, objection.kind with
  | .distinction term, .equivocalCase offendingTerm => term = offendingTerm
  | .subtraction _ excludedCases, .freshCounterinstance counterexample =>
      counterexample ∈ excludedCases
  | .subtraction _ excludedCases, .uniqueCounterinstance counterexample =>
      counterexample ∈ excludedCases
  | _, _ => False

end UniversalRepair

/--
Book VIII evaluates each asked premiss according to whether it is acceptable,
unacceptable, or neutral, and whether it is relevant to the route against the
thesis.
-/
inductive QuestionRelevance where
  | relevant
  | irrelevant
  deriving DecidableEq, Repr, Inhabited

/--
The answerer may meet a question by simple concession/rejection only when it is
clear and single-sensed; otherwise the right reply is to request clarification
or distinguish the senses up front.
-/
inductive QuestionClarity where
  | clear
  | unclear
  | ambiguous
  deriving DecidableEq, Repr, Inhabited

inductive AnswererRemark where
  | acceptableButIrrelevant
  | notAcceptableButIrrelevant
  | tooCloseToInitialThesis
  | tooUnacceptable
  | relevantButNeutral
  deriving DecidableEq, Repr, Inhabited

inductive AnswererGuidance where
  | concede (remark : Option AnswererRemark := none)
  | reject (remark : Option AnswererRemark := none)
  | askClarification
  | distinguishManyWays
  deriving DecidableEq, Repr, Inhabited

/--
This packages the Book-VIII norms for what the answerer should do with a
question once its apparent acceptability, relevance, and clarity are fixed.
-/
def adviseAnswerer (standing : ApparentAcceptability)
    (relevance : QuestionRelevance)
    (clarity : QuestionClarity) : AnswererGuidance :=
  match clarity with
  | .unclear => .askClarification
  | .ambiguous => .distinguishManyWays
  | .clear =>
      match standing, relevance with
      | .acceptable, .irrelevant => .concede (some .acceptableButIrrelevant)
      | .unacceptable, .irrelevant => .concede (some .notAcceptableButIrrelevant)
      | .acceptable, .relevant => .concede (some .tooCloseToInitialThesis)
      | .unacceptable, .relevant => .reject (some .tooUnacceptable)
      | .neither, .irrelevant => .concede
      | .neither, .relevant => .concede (some .relevantButNeutral)

/--
The four Book-VIII ways of hindering an argument. Only the first is a genuine
solution; the others merely block or delay the deduction.
-/
inductive ObstructionMode where
  | rejectCauseOfFalsehood
  | againstQuestioner
  | againstQuestions
  | time
  deriving DecidableEq, Repr, Inhabited

namespace ObstructionMode

def isSolution : ObstructionMode → Prop
  | .rejectCauseOfFalsehood => True
  | _ => False

@[simp] theorem isSolution_rejectCauseOfFalsehood :
    ObstructionMode.isSolution .rejectCauseOfFalsehood := by
  trivial

@[simp] theorem not_isSolution_againstQuestioner :
    ¬ ObstructionMode.isSolution .againstQuestioner := by
  simp [isSolution]

@[simp] theorem not_isSolution_againstQuestions :
    ¬ ObstructionMode.isSolution .againstQuestions := by
  simp [isSolution]

@[simp] theorem not_isSolution_time :
    ¬ ObstructionMode.isSolution .time := by
  simp [isSolution]

end ObstructionMode

/--
An elenchus succeeds when the concessions yield one of the contradictory targets
carried by the thesis. For definition-problems, this means any contradicted
genus/differentia commitment can refute the candidate account, in line with the
Book-I treatment of definitions as structured dialectical material.
-/
def Elenchus [PredicationalManual] (state : GameState) : Prop :=
  match state.thesisRefutationTargets? with
  | some targets => ∃ target, target ∈ targets ∧ Derives state.concessions target
  | none => False

def DialecticalSyllogism (art : DialecticalArt)
    (respondent : RespondentKind)
    (premises : List Categorical) (conclusion : Categorical) : Prop :=
  (∀ ⦃premise : Categorical⦄, premise ∈ premises → acceptableTo art respondent premise) ∧
    Derives premises conclusion

end Aristotle.Dialectic
