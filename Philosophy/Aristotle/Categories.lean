import Philosophy.Aristotle.Core

namespace Aristotle.Categories

open Philosophy.Aristotle.Core

/-!
# The Categories as Dialectical Manual

`Philosophy/Aristotle/Aristotle.md` treats the `Categories` and the
pre-Topics material as background for dialectic rather than as an already
scientific theory. `Philosophy/Aristotle/MDC_Menn.md` sharpens that role for
this project. So the present file is a manual for preparing dialectical
materials:

- a `Term` is a simple linguistic item
- a `CategorialCandidate` records the referent and logos fixed by a univocal
  use of that term
- a `PositionedCandidate` adds categorial placement
- genus work then proceeds through explicit compatibility checks rather than
  identifying genus-candidacy with same-category alone

It therefore carries the tests needed to distinguish synonymy, category,
said-of, in-subject, and substance rank before any stronger scientific use is
attempted.

The most immediate textual guides here are now Smith's translated/commented
`Topics` Book I files:

- `Topics-I.4,5,6.md` for predicables
- `Topics-I.7,8.md` for sameness and the completeness of the predicable split
- `Topics-I.9,10,11.md` for categories, dialectical premisses, problems, and
  theses
- `Topics-I.15.md` and `Topics-I.16,17,18.md` for many-ways-said, differences,
  likenesses, and the tools of inquiry
-/

abbrev Lexis := Philosophy.Aristotle.Core.Lexis
abbrev Logos := Philosophy.Aristotle.Core.Logos
abbrev Signified := Philosophy.Aristotle.Core.Signified
abbrev Term := Philosophy.Aristotle.Core.Term
abbrev Expression := Philosophy.Aristotle.Core.Expression
abbrev DefinitionalPhrase := Philosophy.Aristotle.Core.DefinitionalPhrase
abbrev DefinitionKind := Philosophy.Aristotle.Core.DefinitionKind
abbrev DialecticalDefinition := Philosophy.Aristotle.Core.DialecticalDefinition
abbrev ScientificDefinition := Philosophy.Aristotle.Core.ScientificDefinition
abbrev Predicable := Philosophy.Aristotle.Core.Predicable
abbrev Category := Philosophy.Aristotle.Core.Category
abbrev OppositionKind := Philosophy.Aristotle.Core.OppositionKind
abbrev SubjectRelation := Philosophy.Aristotle.Core.SubjectRelation

namespace Predicable

abbrev idion : Predicable := .proprium

end Predicable

namespace Category

abbrev ousia : Category := .substance
abbrev poson : Category := .quantity
abbrev poion : Category := .quality
abbrev prosTi : Category := .relation
abbrev pou : Category := .place
abbrev pote : Category := .time
abbrev keisthai : Category := .position
abbrev echein : Category := .state
abbrev poiein : Category := .action
abbrev paschein : Category := .affection

end Category

/--
`SurfaceVoice` tracks the grammatical appearance that can mislead a dialectician
before categorial placement has done its work. This is the local hook for the
`SE` 22-style cases Menn highlights, where active surface form can suggest
`poiein` even when the thing belongs under `paschein`.
-/
inductive SurfaceVoice
  | active
  | passive
  deriving DecidableEq, Repr, Inhabited

namespace SurfaceVoice

def suggestedCategory : SurfaceVoice → Category
  | .active => Category.poiein
  | .passive => Category.paschein

end SurfaceVoice

structure SurfaceTrap where
  suggestedCategory : Category
  voice? : Option SurfaceVoice := none
  deriving DecidableEq, Repr, Inhabited

namespace SurfaceTrap

def ofVoice (voice : SurfaceVoice) : SurfaceTrap :=
  { suggestedCategory := voice.suggestedCategory
    voice? := some voice }

@[simp] theorem ofVoice_suggestedCategory (voice : SurfaceVoice) :
    (ofVoice voice).suggestedCategory = voice.suggestedCategory := by
  rfl

@[simp] theorem ofVoice_voice? (voice : SurfaceVoice) :
    (ofVoice voice).voice? = some voice := by
  rfl

end SurfaceTrap

namespace SubjectRelation

abbrev kathHupokeimenou : SubjectRelation := .saidOf
abbrev enHupokeimenōi : SubjectRelation := .inSubject

end SubjectRelation

structure CategoryProfile where
  kind : Category
  oppositions : List OppositionKind := []
  hasContrary : Prop := False
  admitsMoreAndLess : Prop := False

/--
Operational tests for the Book-I classificatory work that precedes a dialectical
exchange. In Smith's presentation of `Topics` I, these are the sorts of
questions by which one screens said-of / in-subject structure before assigning
predicables and categories.
-/
class AntepredicamentalManual extends
    Philosophy.Aristotle.Core.Signification Term Signified Logos,
    Philosophy.Aristotle.Core.Morphology Term where
  saidOfTest : Signified → Prop
  inSubjectTest : Signified → Prop

/--
Adds the category-sensitive and similarity-sensitive tests needed for the wider
Book-I toolkit, especially the transition from predicables to categories and to
the later tests for many-ways-said, likeness, and difference.
-/
class Manual extends AntepredicamentalManual where
  fallsUnderTest : Signified → Category → Prop
  signifiesThisTest : Signified → Prop
  similarityTest : Signified → Prop
  surfaceVoice : Term → Option SurfaceVoice := fun _ => none
  surfaceTraps : Term → List SurfaceTrap := fun term =>
    match surfaceVoice term with
    | some voice => [SurfaceTrap.ofVoice voice]
    | none => []
  voice_surfaceTrap :
      ∀ {term : Term} {voice : SurfaceVoice},
        surfaceVoice term = some voice →
          SurfaceTrap.ofVoice voice ∈ surfaceTraps term := by
    intro term voice hvoice
    simp [surfaceTraps, hvoice]
  profile : Category → CategoryProfile
  category_unique : ∀ {b : Signified} {left right : Category},
    fallsUnderTest b left → fallsUnderTest b right → left = right
  profile_matches : ∀ category, (profile category).kind = category
  similarity_of_quality : ∀ {b : Signified},
    fallsUnderTest b Category.quality → similarityTest b
  quality_of_similarity : ∀ {b : Signified},
    similarityTest b → fallsUnderTest b Category.quality

class DialecticalPredication (B : Type) extends
    Philosophy.Aristotle.Core.Predication B where
  genus_respects_category :
    ∀ {g s : B} {category : Category},
      genus_of g s → falls_under s category → falls_under g category
  proprium_implies_said_of :
    ∀ {p s : B}, proprium_of p s → said_of p s
  differentia_not_in_subject :
    ∀ {d s carrier : B}, differentia_of d s → ¬ in_subject d carrier
  proprium_not_in_subject :
    ∀ {p s carrier : B}, proprium_of p s → ¬ in_subject p carrier

class PredicationalManual extends Manual, DialecticalPredication Signified where
  saidOfTest_iff :
    ∀ {b : Signified},
      saidOfTest b ↔ ∃ subject : Signified,
        Philosophy.Aristotle.Core.Predication.said_of b subject
  inSubjectTest_iff :
    ∀ {b : Signified},
      inSubjectTest b ↔ ∃ subject : Signified,
        Philosophy.Aristotle.Core.Predication.in_subject b subject
  fallsUnderTest_iff :
    ∀ {b : Signified} {category : Category},
      fallsUnderTest b category ↔
        Philosophy.Aristotle.Core.Predication.falls_under b category

def Synonymous [AntepredicamentalManual] (term : Term)
    (left right : Signified) : Prop :=
  AreSynonymous (L := Logos) term left right

def Homonymous [AntepredicamentalManual] (term : Term)
    (left right : Signified) : Prop :=
  AreHomonymous (L := Logos) term left right

def Paronymous [AntepredicamentalManual] (derived root : Term)
    (left right : Signified) : Prop :=
  IsParonymous (L := Logos) derived root left right

def HasReference [AntepredicamentalManual] (term : Term) : Prop :=
  ∃ referent : Signified, ∃ logos : Logos, signifiesAs term referent logos

def IsUnivocal [AntepredicamentalManual] (term : Term) : Prop :=
  ∃ referent : Signified, ∃ logos : Logos,
    signifiesAs term referent logos ∧
      ∀ {referent' : Signified} {logos' : Logos},
        signifiesAs term referent' logos' →
          referent' = referent ∧ logos' = logos

def RequiresClarification [AntepredicamentalManual] (term : Term) : Prop :=
  HasReference term ∧ ¬ IsUnivocal term

def RequiresParonymResolution [AntepredicamentalManual] (term : Term) : Prop :=
  ∃ root : Term, ∃ left right : Signified, Paronymous term root left right

def EligibleForGenusOrDefinition [AntepredicamentalManual] (term : Term) : Prop :=
  IsUnivocal term ∧ ¬ RequiresParonymResolution term

structure CategorialCandidate [AntepredicamentalManual] where
  term : Term
  referent : Signified
  logos : Logos
  witness : signifiesAs term referent logos
  univocal : IsUnivocal term
  notParonymous : ¬ RequiresParonymResolution term

noncomputable def candidateOfEligibility [AntepredicamentalManual]
    (term : Term) (h : EligibleForGenusOrDefinition term) : CategorialCandidate := by
  classical
  have hexists : ∃ p : Signified × Logos, signifiesAs term p.1 p.2 := by
    rcases h.1 with ⟨referent, logos, hwitness, _⟩
    exact ⟨(referent, logos), hwitness⟩
  let witness := Classical.choose hexists
  have hwitness : signifiesAs term witness.1 witness.2 :=
    Classical.choose_spec hexists
  exact
    { term := term
      referent := witness.1
      logos := witness.2
      witness := hwitness
      univocal := h.1
      notParonymous := h.2 }

inductive BlockedSimpleTermScreening [AntepredicamentalManual] (term : Term) : Type where
  | requiresClarification (h : RequiresClarification term)
  | requiresParonymResolution (h : RequiresParonymResolution term)
  | lacksReference (h : ¬ HasReference term)

inductive SimpleTermScreening [AntepredicamentalManual] (term : Term) : Type where
  | blocked (blocked : BlockedSimpleTermScreening term)
  | candidate (candidate : CategorialCandidate)

noncomputable def screenSimpleTerm [AntepredicamentalManual]
    (term : Term) : SimpleTermScreening term := by
  classical
  by_cases hpar : RequiresParonymResolution term
  · exact .blocked (.requiresParonymResolution hpar)
  · by_cases href : HasReference term
    · by_cases huni : IsUnivocal term
      · exact .candidate (candidateOfEligibility term ⟨huni, hpar⟩)
      · exact .blocked (.requiresClarification ⟨href, huni⟩)
    · exact .blocked (.lacksReference href)

inductive ScreenedExpression [AntepredicamentalManual] : Expression → Type where
  | combined (parts : List Lexis) : ScreenedExpression (.combined parts)
  | simple (term : Term) (screening : SimpleTermScreening term) :
      ScreenedExpression (.simple term)

def admissibleExpression [AntepredicamentalManual] : Expression → Prop
  | .simple term => ∃ candidate : CategorialCandidate, candidate.term = term
  | .combined _ => False

noncomputable def screenExpression [AntepredicamentalManual]
    (expr : Expression) : ScreenedExpression expr := by
  cases expr with
  | simple term => exact .simple term (screenSimpleTerm term)
  | combined parts => exact .combined parts

/--
A dialectical definition whose genus and differentiae have passed the initial
Book-I screening for univocity/paronymy/reference and are therefore fit to be
tested further.
-/
structure ScreenedDefinitionalPhrase [AntepredicamentalManual] where
  genus : CategorialCandidate
  differentiae : List CategorialCandidate
  lexicalForm : Option Lexis := none
  nonempty : differentiae ≠ []

namespace ScreenedDefinitionalPhrase

def toPhrase [AntepredicamentalManual]
    (phrase : ScreenedDefinitionalPhrase) : DefinitionalPhrase :=
  { genus := phrase.genus.term
    differentiae := phrase.differentiae.map CategorialCandidate.term
    lexicalForm := phrase.lexicalForm }

def toDefinition [AntepredicamentalManual]
    (phrase : ScreenedDefinitionalPhrase) : DialecticalDefinition :=
  phrase.toPhrase.asDialecticalDefinition

end ScreenedDefinitionalPhrase

def isSaidOf [AntepredicamentalManual] (candidate : CategorialCandidate) : Prop :=
  AntepredicamentalManual.saidOfTest candidate.referent

def isInSubject [AntepredicamentalManual] (candidate : CategorialCandidate) : Prop :=
  AntepredicamentalManual.inSubjectTest candidate.referent

def saidOfSubject [PredicationalManual]
    (predicate subject : CategorialCandidate) : Prop :=
  Philosophy.Aristotle.Core.Predication.said_of
    predicate.referent subject.referent

def inSubjectOf [PredicationalManual]
    (predicate subject : CategorialCandidate) : Prop :=
  Philosophy.Aristotle.Core.Predication.in_subject
    predicate.referent subject.referent

def genusOfSubject [PredicationalManual]
    (genus subject : CategorialCandidate) : Prop :=
  Philosophy.Aristotle.Core.Predication.genus_of
    genus.referent subject.referent

def differentiaOfSubject [PredicationalManual]
    (differentia subject : CategorialCandidate) : Prop :=
  Philosophy.Aristotle.Core.Predication.differentia_of
    differentia.referent subject.referent

def propriumOfSubject [PredicationalManual]
    (property subject : CategorialCandidate) : Prop :=
  Philosophy.Aristotle.Core.Predication.proprium_of
    property.referent subject.referent

def accidentOfSubject [PredicationalManual]
    (accident subject : CategorialCandidate) : Prop :=
  Philosophy.Aristotle.Core.Predication.accident_of
    accident.referent subject.referent

def fallsUnder [Manual] (candidate : CategorialCandidate) (category : Category) : Prop :=
  Manual.fallsUnderTest candidate.referent category

def signifiesThis [Manual] (candidate : CategorialCandidate) : Prop :=
  Manual.signifiesThisTest candidate.referent

def supportsSimilarity [Manual] (candidate : CategorialCandidate) : Prop :=
  Manual.similarityTest candidate.referent

def supportsOpposition [Manual] (category : Category) (kind : OppositionKind) : Prop :=
  kind ∈ (Manual.profile category).oppositions

def categoryHasContrary [Manual] (category : Category) : Prop :=
  (Manual.profile category).hasContrary

def categoryAdmitsMoreAndLess [Manual] (category : Category) : Prop :=
  (Manual.profile category).admitsMoreAndLess

structure CategoryPlacement [Manual] (candidate : CategorialCandidate) where
  category : Category
  witness : fallsUnder candidate category

structure PositionedCandidate [Manual] where
  candidate : CategorialCandidate
  placement : CategoryPlacement candidate

def sameCategory [Manual] (left right : PositionedCandidate) : Prop :=
  left.placement.category = right.placement.category

def hasSurfaceVoice [Manual] (term : Term) (voice : SurfaceVoice) : Prop :=
  Manual.surfaceVoice term = some voice

def hasSurfaceTrap [Manual] (term : Term) (trap : SurfaceTrap) : Prop :=
  trap ∈ Manual.surfaceTraps term

theorem hasSurfaceTrap_of_hasSurfaceVoice [Manual]
    {term : Term} {voice : SurfaceVoice}
    (h : hasSurfaceVoice term voice) :
    hasSurfaceTrap term (SurfaceTrap.ofVoice voice) :=
  Manual.voice_surfaceTrap h

def surfaceCategorySuggestion [Manual] (term : Term) (category : Category) : Prop :=
  ∃ trap : SurfaceTrap,
    hasSurfaceTrap term trap ∧ trap.suggestedCategory = category

structure SurfaceTrapMismatch [Manual] (candidate : PositionedCandidate) where
  trap : SurfaceTrap
  surface : hasSurfaceTrap candidate.candidate.term trap
  actualDiffers : candidate.placement.category ≠ trap.suggestedCategory

/--
An `SE` 22-style mismatch: the term's grammatical surface suggests one
category, but categorial placement locates it elsewhere.
-/
structure FigureOfSpeechMismatch [Manual] (candidate : PositionedCandidate) where
  voice : SurfaceVoice
  surface : hasSurfaceVoice candidate.candidate.term voice
  actualDiffers : candidate.placement.category ≠ voice.suggestedCategory

def FigureOfSpeechMismatch.toSurfaceTrapMismatch [Manual]
    {candidate : PositionedCandidate}
    (h : FigureOfSpeechMismatch candidate) :
    SurfaceTrapMismatch candidate where
  trap := SurfaceTrap.ofVoice h.voice
  surface := hasSurfaceTrap_of_hasSurfaceVoice h.surface
  actualDiffers := by
    simpa [SurfaceTrap.ofVoice] using h.actualDiffers

/--
The characteristic Menn case: an active-looking term whose true category is
`paschein`.
-/
def ActiveSurfaceAffection [Manual] (candidate : PositionedCandidate) : Prop :=
  hasSurfaceVoice candidate.candidate.term .active ∧
    candidate.placement.category = Category.paschein

def ActiveSurfaceAffection.figureOfSpeechMismatch [Manual]
    {candidate : PositionedCandidate}
    (h : ActiveSurfaceAffection candidate) :
    FigureOfSpeechMismatch candidate := by
  refine
    { voice := .active
      surface := h.1
      actualDiffers := ?_ }
  intro hEq
  have hcontra : Category.paschein = Category.poiein := by
    calc
      Category.paschein = candidate.placement.category := h.2.symm
      _ = Category.poiein := by simpa [SurfaceVoice.suggestedCategory] using hEq
  exact (show Category.paschein ≠ Category.poiein by decide) hcontra

def ActiveSurfaceAffection.surfaceTrapMismatch [Manual]
    {candidate : PositionedCandidate}
    (h : ActiveSurfaceAffection candidate) :
    SurfaceTrapMismatch candidate :=
  (h.figureOfSpeechMismatch).toSurfaceTrapMismatch

theorem SurfaceTrapMismatch.not_sameCategory_of_suggestedCategory [Manual]
    {candidate other : PositionedCandidate}
    (h : SurfaceTrapMismatch candidate)
    (hother : other.placement.category = h.trap.suggestedCategory) :
    ¬ sameCategory candidate other := by
  intro hsame
  apply h.actualDiffers
  calc
    candidate.placement.category = other.placement.category := hsame
    _ = h.trap.suggestedCategory := hother

theorem FigureOfSpeechMismatch.not_sameCategory_of_suggestedCategory [Manual]
    {candidate other : PositionedCandidate}
    (h : FigureOfSpeechMismatch candidate)
    (hother : other.placement.category = h.voice.suggestedCategory) :
    ¬ sameCategory candidate other := by
  intro hsame
  apply h.actualDiffers
  calc
    candidate.placement.category = other.placement.category := hsame
    _ = h.voice.suggestedCategory := hother

structure GenusCompatibility [Manual]
    (subject genus : PositionedCandidate) : Prop where
  sameCategory : Aristotle.Categories.sameCategory subject genus

structure CategoryMismatch [Manual]
    (subject genus : PositionedCandidate) : Prop where
  mismatch : ¬ Aristotle.Categories.sameCategory subject genus

def SurfaceTrapMismatch.categoryMismatch [Manual]
    {candidate other : PositionedCandidate}
    (h : SurfaceTrapMismatch candidate)
    (hother : other.placement.category = h.trap.suggestedCategory) :
    CategoryMismatch candidate other :=
  ⟨h.not_sameCategory_of_suggestedCategory hother⟩

def FigureOfSpeechMismatch.categoryMismatch [Manual]
    {candidate other : PositionedCandidate}
    (h : FigureOfSpeechMismatch candidate)
    (hother : other.placement.category = h.voice.suggestedCategory) :
    CategoryMismatch candidate other :=
  ⟨h.not_sameCategory_of_suggestedCategory hother⟩

structure ProvisionalGenus [PredicationalManual] where
  subject : PositionedCandidate
  genus : PositionedCandidate
  compatibility : GenusCompatibility subject genus
  genusSaidOf : genusOfSubject genus.candidate subject.candidate

noncomputable def positionCandidate? [Manual]
    (candidate : CategorialCandidate) : Option PositionedCandidate := by
  classical
  by_cases h : ∃ category : Category, fallsUnder candidate category
  · let category := Classical.choose h
    have hwitness : fallsUnder candidate category := Classical.choose_spec h
    exact some ⟨candidate, ⟨category, hwitness⟩⟩
  · exact none

/--
A screened dialectical definition after categorial placement of its genus and
differentiae. This is still dialectical material: it has been positioned for
testing, not elevated to scientific definition.
-/
structure PositionedDefinitionalPhrase [Manual] where
  genus : PositionedCandidate
  differentiae : List PositionedCandidate
  lexicalForm : Option Lexis := none
  nonempty : differentiae ≠ []

namespace PositionedDefinitionalPhrase

def toPhrase [Manual]
    (phrase : PositionedDefinitionalPhrase) : DefinitionalPhrase :=
  { genus := phrase.genus.candidate.term
    differentiae := phrase.differentiae.map (fun candidate => candidate.candidate.term)
    lexicalForm := phrase.lexicalForm }

def toDefinition [Manual]
    (phrase : PositionedDefinitionalPhrase) : DialecticalDefinition :=
  phrase.toPhrase.asDialecticalDefinition

end PositionedDefinitionalPhrase

noncomputable def positionCandidates? [Manual] :
    List CategorialCandidate → Option (List PositionedCandidate)
  | [] => some []
  | candidate :: rest =>
      match positionCandidate? candidate, positionCandidates? rest with
      | some positioned, some positionedRest => some (positioned :: positionedRest)
      | _, _ => none

theorem positionCandidates?_some_nil_iff [Manual]
    {candidates : List CategorialCandidate} :
    positionCandidates? candidates = some [] ↔ candidates = [] := by
  constructor
  · intro h
    cases candidates with
    | nil =>
        rfl
    | cons candidate rest =>
        cases hcandidate : positionCandidate? candidate <;>
          cases hrest : positionCandidates? rest <;>
            simp [positionCandidates?, hcandidate, hrest] at h
  · intro h
    subst h
    simp [positionCandidates?]

noncomputable def positionDefinitionalPhrase? [Manual]
    (phrase : ScreenedDefinitionalPhrase) : Option PositionedDefinitionalPhrase := by
  classical
  match hgenus : positionCandidate? phrase.genus,
      hdiffs : positionCandidates? phrase.differentiae with
  | some genus, some differentiae =>
      have hne : differentiae ≠ [] := by
        intro hnil
        have hsomeNil : positionCandidates? phrase.differentiae = some [] := by
          simp [hdiffs, hnil]
        have hsourceNil : phrase.differentiae = [] :=
          (positionCandidates?_some_nil_iff).1 hsomeNil
        exact phrase.nonempty hsourceNil
      exact some
        { genus := genus
          differentiae := differentiae
          lexicalForm := phrase.lexicalForm
          nonempty := hne }
  | _, _ => exact none

def hasContrary [Manual] (candidate : PositionedCandidate) : Prop :=
  categoryHasContrary candidate.placement.category

def lacksContrary [Manual] (candidate : PositionedCandidate) : Prop :=
  ¬ hasContrary candidate

def admitsMoreAndLess [Manual] (candidate : PositionedCandidate) : Prop :=
  categoryAdmitsMoreAndLess candidate.placement.category

def lacksMoreAndLess [Manual] (candidate : PositionedCandidate) : Prop :=
  ¬ admitsMoreAndLess candidate

def ContraryMismatch [Manual]
    (subject predicate : PositionedCandidate) : Prop :=
  hasContrary predicate ∧ lacksContrary subject

def DegreeMismatch [Manual]
    (subject predicate : PositionedCandidate) : Prop :=
  admitsMoreAndLess predicate ∧ lacksMoreAndLess subject

structure ContraryCompatibility [Manual]
    (subject predicate : PositionedCandidate) : Prop where
  compatible : hasContrary predicate → hasContrary subject

structure DegreeCompatibility [Manual]
    (subject predicate : PositionedCandidate) : Prop where
  compatible : admitsMoreAndLess predicate → admitsMoreAndLess subject

structure GenusDossier [PredicationalManual]
    (subject genus : PositionedCandidate) : Prop where
  sameCategory : Aristotle.Categories.sameCategory subject genus
  contrary : ContraryCompatibility subject genus
  degree : DegreeCompatibility subject genus
  genusSaidOf : genusOfSubject genus.candidate subject.candidate

def GenusRefutationByNotSaidOf [PredicationalManual]
    (subject genus : PositionedCandidate) : Prop :=
  ¬ genusOfSubject genus.candidate subject.candidate

def DefinitionRefutationByCategoryMismatch [Manual]
    (subject : PositionedCandidate) (phrase : PositionedDefinitionalPhrase) : Prop :=
  ¬ Aristotle.Categories.sameCategory subject phrase.genus

def DefinitionRefutationByContraryMismatch [Manual]
    (subject : PositionedCandidate) (phrase : PositionedDefinitionalPhrase) : Prop :=
  ContraryMismatch subject phrase.genus

def DefinitionRefutationByDegreeMismatch [Manual]
    (subject : PositionedCandidate) (phrase : PositionedDefinitionalPhrase) : Prop :=
  DegreeMismatch subject phrase.genus

def DefinitionRefutationByGenusNotSaidOf [PredicationalManual]
    (subject : PositionedCandidate) (phrase : PositionedDefinitionalPhrase) : Prop :=
  ¬ genusOfSubject phrase.genus.candidate subject.candidate

def DefinitionRefutationByDifferentiaNotSaidOf [PredicationalManual]
    (subject : PositionedCandidate) (phrase : PositionedDefinitionalPhrase) : Prop :=
  ∃ differentia : PositionedCandidate,
    differentia ∈ phrase.differentiae ∧
      ¬ differentiaOfSubject differentia.candidate subject.candidate

def DefinitionRefutationByInSubject [Manual]
    (_subject : PositionedCandidate) (phrase : PositionedDefinitionalPhrase) : Prop :=
  ∃ differentia : PositionedCandidate,
    differentia ∈ phrase.differentiae ∧ isInSubject differentia.candidate

structure DialecticalDefinitionDossier [PredicationalManual]
    (subject : PositionedCandidate) (phrase : PositionedDefinitionalPhrase) : Prop where
  sameCategory : Aristotle.Categories.sameCategory subject phrase.genus
  contrary : ContraryCompatibility subject phrase.genus
  degree : DegreeCompatibility subject phrase.genus
  genusSaidOf : genusOfSubject phrase.genus.candidate subject.candidate
  differentiaeSaidOf :
    ∀ {differentia : PositionedCandidate},
      differentia ∈ phrase.differentiae →
        differentiaOfSubject differentia.candidate subject.candidate
  differentiaeNotInSubject :
    ∀ {differentia : PositionedCandidate},
      differentia ∈ phrase.differentiae →
        ¬ isInSubject differentia.candidate

def PropriumRefutationByNotSaidOf [PredicationalManual]
    (subject property : PositionedCandidate) : Prop :=
  ¬ propriumOfSubject property.candidate subject.candidate

def PropriumRefutationByInSubject [Manual]
    (_subject property : PositionedCandidate) : Prop :=
  isInSubject property.candidate

structure PropriumDossier [PredicationalManual]
    (subject property : PositionedCandidate) : Prop where
  propertySaidOf : propriumOfSubject property.candidate subject.candidate
  notInSubject : ¬ isInSubject property.candidate

inductive SubstanceRank
  | primary
  | secondary
  deriving DecidableEq, Repr, Inhabited

structure SubstanceCategoryIdia [Manual] (candidate : PositionedCandidate) : Prop where
  isSubstance : candidate.placement.category = Category.substance
  lacksContrary : Aristotle.Categories.lacksContrary candidate
  lacksMoreAndLess : Aristotle.Categories.lacksMoreAndLess candidate

abbrev SubstanceIdia [Manual] (candidate : PositionedCandidate) : Prop :=
  SubstanceCategoryIdia candidate

structure QualityIdia [Manual] (candidate : PositionedCandidate) : Prop where
  isQuality : candidate.placement.category = Category.quality
  supportsSimilarity : supportsSimilarity candidate.candidate

structure PrimarySubstanceMarks [Manual] (candidate : PositionedCandidate) : Prop where
  idia : SubstanceIdia candidate
  signifiesThis : signifiesThis candidate.candidate
  notSaidOf : ¬ isSaidOf candidate.candidate
  notInSubject : ¬ isInSubject candidate.candidate

structure SecondarySubstanceMarks [Manual] (candidate : PositionedCandidate) : Prop where
  idia : SubstanceIdia candidate
  saidOf : isSaidOf candidate.candidate
  notInSubject : ¬ isInSubject candidate.candidate

abbrev RecognizedPrimarySubstance [Manual] (candidate : PositionedCandidate) : Prop :=
  PrimarySubstanceMarks candidate

abbrev RecognizedSecondarySubstance [Manual] (candidate : PositionedCandidate) : Prop :=
  SecondarySubstanceMarks candidate

def RecognizedSubstance [Manual] (candidate : PositionedCandidate) : Prop :=
  RecognizedPrimarySubstance candidate ∨ RecognizedSecondarySubstance candidate

theorem RecognizedPrimarySubstance.of_marks [Manual]
    {candidate : PositionedCandidate} (h : PrimarySubstanceMarks candidate) :
    RecognizedPrimarySubstance candidate :=
  h

theorem RecognizedSecondarySubstance.of_marks [Manual]
    {candidate : PositionedCandidate} (h : SecondarySubstanceMarks candidate) :
    RecognizedSecondarySubstance candidate :=
  h

theorem primary_not_secondary [Manual] {candidate : PositionedCandidate}
    (hprimary : RecognizedPrimarySubstance candidate) :
    ¬ RecognizedSecondarySubstance candidate := by
  intro hsecondary
  exact hprimary.notSaidOf hsecondary.saidOf

theorem secondary_not_primary_of_saidOf [Manual]
    {candidate : PositionedCandidate}
    (hsecondary : RecognizedSecondarySubstance candidate) :
    ¬ RecognizedPrimarySubstance candidate := by
  intro hprimary
  exact hprimary.notSaidOf hsecondary.saidOf

structure RecognizedQuality [Manual] (candidate : PositionedCandidate) : Prop where
  idia : QualityIdia candidate

theorem fallsUnder_unique [Manual] {candidate : CategorialCandidate}
    {left right : Category}
    (hleft : fallsUnder candidate left) (hright : fallsUnder candidate right) :
    left = right :=
  Manual.category_unique hleft hright

theorem isSaidOf_iff_exists_saidOfSubject [PredicationalManual]
    {candidate : CategorialCandidate} :
    isSaidOf candidate ↔
      ∃ subject : Signified,
        Philosophy.Aristotle.Core.Predication.said_of candidate.referent subject := by
  simpa [isSaidOf] using
    (PredicationalManual.saidOfTest_iff (b := candidate.referent))

theorem isInSubject_iff_exists_inSubjectCarrier [PredicationalManual]
    {candidate : CategorialCandidate} :
    isInSubject candidate ↔
      ∃ subject : Signified,
        Philosophy.Aristotle.Core.Predication.in_subject candidate.referent subject := by
  simpa [isInSubject] using
    (PredicationalManual.inSubjectTest_iff (b := candidate.referent))

theorem fallsUnder_iff_predicational [PredicationalManual]
    {candidate : CategorialCandidate} {category : Category} :
    fallsUnder candidate category ↔
      Philosophy.Aristotle.Core.Predication.falls_under candidate.referent category := by
  simpa [fallsUnder] using
    (PredicationalManual.fallsUnderTest_iff
      (b := candidate.referent) (category := category))

theorem isSaidOf_of_saidOfSubject [PredicationalManual]
    {predicate subject : CategorialCandidate}
    (h : saidOfSubject predicate subject) :
    isSaidOf predicate := by
  rw [isSaidOf_iff_exists_saidOfSubject]
  exact ⟨subject.referent, h⟩

theorem isInSubject_of_inSubjectOf [PredicationalManual]
    {predicate subject : CategorialCandidate}
    (h : inSubjectOf predicate subject) :
    isInSubject predicate := by
  rw [isInSubject_iff_exists_inSubjectCarrier]
  exact ⟨subject.referent, h⟩

theorem isSaidOf_of_genusOfSubject [PredicationalManual]
    {genus subject : CategorialCandidate}
    (h : genusOfSubject genus subject) :
    isSaidOf genus :=
  isSaidOf_of_saidOfSubject
    (predicate := genus) (subject := subject)
    (Philosophy.Aristotle.Core.Predication.genus_implies_said_of h)

theorem isSaidOf_of_differentiaOfSubject [PredicationalManual]
    {differentia subject : CategorialCandidate}
    (h : differentiaOfSubject differentia subject) :
    isSaidOf differentia :=
  isSaidOf_of_saidOfSubject
    (predicate := differentia) (subject := subject)
    (Philosophy.Aristotle.Core.Predication.differentia_implies_said_of h)

theorem isSaidOf_of_propriumOfSubject [PredicationalManual]
    {property subject : CategorialCandidate}
    (h : propriumOfSubject property subject) :
    isSaidOf property :=
  isSaidOf_of_saidOfSubject
    (predicate := property) (subject := subject)
    (DialecticalPredication.proprium_implies_said_of h)

theorem fallsUnder_subjectCategory_of_genusOfSubject [PredicationalManual]
    {genus subject : PositionedCandidate}
    (h : genusOfSubject genus.candidate subject.candidate) :
    fallsUnder genus.candidate subject.placement.category := by
  have hsubject :
      Philosophy.Aristotle.Core.Predication.falls_under
        subject.candidate.referent subject.placement.category := by
    exact (fallsUnder_iff_predicational
      (candidate := subject.candidate)
      (category := subject.placement.category)).mp subject.placement.witness
  have hgenus :
      Philosophy.Aristotle.Core.Predication.falls_under
        genus.candidate.referent subject.placement.category :=
    DialecticalPredication.genus_respects_category
      (category := subject.placement.category) h hsubject
  exact (fallsUnder_iff_predicational
    (candidate := genus.candidate)
    (category := subject.placement.category)).mpr hgenus

theorem sameCategory_of_genusOfSubject [PredicationalManual]
    {genus subject : PositionedCandidate}
    (h : genusOfSubject genus.candidate subject.candidate) :
    sameCategory subject genus := by
  have hgenus :
      fallsUnder genus.candidate subject.placement.category :=
    fallsUnder_subjectCategory_of_genusOfSubject h
  have hcat : genus.placement.category = subject.placement.category :=
    fallsUnder_unique genus.placement.witness hgenus
  exact hcat.symm

theorem contraryCompatibility_of_genusOfSubject [PredicationalManual]
    {genus subject : PositionedCandidate}
    (h : genusOfSubject genus.candidate subject.candidate) :
    ContraryCompatibility subject genus := by
  refine ⟨?_⟩
  intro hcontra
  have hsame := sameCategory_of_genusOfSubject h
  simpa [hasContrary] using (hsame.symm ▸ hcontra)

theorem degreeCompatibility_of_genusOfSubject [PredicationalManual]
    {genus subject : PositionedCandidate}
    (h : genusOfSubject genus.candidate subject.candidate) :
    DegreeCompatibility subject genus := by
  refine ⟨?_⟩
  intro hdegree
  have hsame := sameCategory_of_genusOfSubject h
  simpa [admitsMoreAndLess] using (hsame.symm ▸ hdegree)

theorem genusDossier_of_genusOfSubject [PredicationalManual]
    {genus subject : PositionedCandidate}
    (h : genusOfSubject genus.candidate subject.candidate) :
    GenusDossier subject genus :=
  { sameCategory := sameCategory_of_genusOfSubject h
    contrary := contraryCompatibility_of_genusOfSubject h
    degree := degreeCompatibility_of_genusOfSubject h
    genusSaidOf := h }

theorem notInSubject_of_differentiaOfSubject [PredicationalManual]
    {differentia subject : CategorialCandidate}
    (h : differentiaOfSubject differentia subject) :
    ¬ isInSubject differentia := by
  intro hin
  rcases (isInSubject_iff_exists_inSubjectCarrier
      (candidate := differentia)).mp hin with ⟨carrier, hcarrier⟩
  exact (DialecticalPredication.differentia_not_in_subject
    (carrier := carrier) h) hcarrier

theorem notInSubject_of_propriumOfSubject [PredicationalManual]
    {property subject : CategorialCandidate}
    (h : propriumOfSubject property subject) :
    ¬ isInSubject property := by
  intro hin
  rcases (isInSubject_iff_exists_inSubjectCarrier
      (candidate := property)).mp hin with ⟨carrier, hcarrier⟩
  exact (DialecticalPredication.proprium_not_in_subject
    (carrier := carrier) h) hcarrier

theorem propriumDossier_of_propriumOfSubject [PredicationalManual]
    {property subject : PositionedCandidate}
    (h : propriumOfSubject property.candidate subject.candidate) :
    PropriumDossier subject property :=
  { propertySaidOf := h
    notInSubject := notInSubject_of_propriumOfSubject h }

theorem quality_of_supportsSimilarity [Manual] {candidate : PositionedCandidate}
    (h : supportsSimilarity candidate.candidate) :
    candidate.placement.category = Category.quality := by
  have hquality := Manual.quality_of_similarity h
  exact fallsUnder_unique candidate.placement.witness hquality

theorem supportsSimilarity_of_quality [Manual] {candidate : PositionedCandidate}
    (h : candidate.placement.category = Category.quality) :
    supportsSimilarity candidate.candidate := by
  have hquality : fallsUnder candidate.candidate Category.quality := by
    simpa [h] using candidate.placement.witness
  exact Manual.similarity_of_quality hquality

theorem contraryCompatibility_of_not_mismatch [Manual]
    {subject predicate : PositionedCandidate}
    (h : ¬ ContraryMismatch subject predicate) :
    ContraryCompatibility subject predicate := by
  refine ⟨?_⟩
  intro hcontra
  by_cases hsubject : hasContrary subject
  · exact hsubject
  · exact False.elim <| h ⟨hcontra, hsubject⟩

theorem degreeCompatibility_of_not_mismatch [Manual]
    {subject predicate : PositionedCandidate}
    (h : ¬ DegreeMismatch subject predicate) :
    DegreeCompatibility subject predicate := by
  refine ⟨?_⟩
  intro hdegree
  by_cases hsubject : admitsMoreAndLess subject
  · exact hsubject
  · exact False.elim <| h ⟨hdegree, hsubject⟩

theorem GenusDossier.notContraryMismatch [PredicationalManual]
    {subject genus : PositionedCandidate}
    (h : GenusDossier subject genus) :
    ¬ ContraryMismatch subject genus := by
  intro hmismatch
  exact hmismatch.2 (h.contrary.compatible hmismatch.1)

theorem GenusDossier.notDegreeMismatch [PredicationalManual]
    {subject genus : PositionedCandidate}
    (h : GenusDossier subject genus) :
    ¬ DegreeMismatch subject genus := by
  intro hmismatch
  exact hmismatch.2 (h.degree.compatible hmismatch.1)

theorem GenusDossier.notNotSaidOf_refutation [PredicationalManual]
    {subject genus : PositionedCandidate}
    (h : GenusDossier subject genus) :
    ¬ GenusRefutationByNotSaidOf subject genus := by
  intro hrefute
  exact hrefute h.genusSaidOf

theorem DialecticalDefinitionDossier.notCategoryMismatch [PredicationalManual]
    {subject : PositionedCandidate} {phrase : PositionedDefinitionalPhrase}
    (h : DialecticalDefinitionDossier subject phrase) :
    ¬ DefinitionRefutationByCategoryMismatch subject phrase := by
  intro hmismatch
  exact hmismatch h.sameCategory

theorem DialecticalDefinitionDossier.notContraryMismatch [PredicationalManual]
    {subject : PositionedCandidate} {phrase : PositionedDefinitionalPhrase}
    (h : DialecticalDefinitionDossier subject phrase) :
    ¬ DefinitionRefutationByContraryMismatch subject phrase := by
  intro hmismatch
  exact hmismatch.2 (h.contrary.compatible hmismatch.1)

theorem DialecticalDefinitionDossier.notDegreeMismatch [PredicationalManual]
    {subject : PositionedCandidate} {phrase : PositionedDefinitionalPhrase}
    (h : DialecticalDefinitionDossier subject phrase) :
    ¬ DefinitionRefutationByDegreeMismatch subject phrase := by
  intro hmismatch
  exact hmismatch.2 (h.degree.compatible hmismatch.1)

theorem DialecticalDefinitionDossier.notGenusNotSaidOf [PredicationalManual]
    {subject : PositionedCandidate} {phrase : PositionedDefinitionalPhrase}
    (h : DialecticalDefinitionDossier subject phrase) :
    ¬ DefinitionRefutationByGenusNotSaidOf subject phrase := by
  intro hrefute
  exact hrefute h.genusSaidOf

theorem DialecticalDefinitionDossier.notDifferentiaNotSaidOf [PredicationalManual]
    {subject : PositionedCandidate} {phrase : PositionedDefinitionalPhrase}
    (h : DialecticalDefinitionDossier subject phrase) :
    ¬ DefinitionRefutationByDifferentiaNotSaidOf subject phrase := by
  intro hrefute
  rcases hrefute with ⟨differentia, hmem, hnot⟩
  exact hnot (h.differentiaeSaidOf hmem)

theorem DialecticalDefinitionDossier.notInSubject_refutation [PredicationalManual]
    {subject : PositionedCandidate} {phrase : PositionedDefinitionalPhrase}
    (h : DialecticalDefinitionDossier subject phrase) :
    ¬ DefinitionRefutationByInSubject subject phrase := by
  intro hrefute
  rcases hrefute with ⟨differentia, hmem, hin⟩
  exact (h.differentiaeNotInSubject hmem) hin

theorem PropriumDossier.notNotSaidOf_refutation [PredicationalManual]
    {subject property : PositionedCandidate}
    (h : PropriumDossier subject property) :
    ¬ PropriumRefutationByNotSaidOf subject property := by
  intro hrefute
  exact hrefute h.propertySaidOf

theorem PropriumDossier.notInSubject_refutation [PredicationalManual]
    {subject property : PositionedCandidate}
    (h : PropriumDossier subject property) :
    ¬ PropriumRefutationByInSubject subject property :=
  h.notInSubject

theorem recognizedSubstance_sameCategory [Manual]
    {left right : PositionedCandidate}
    (hleft : RecognizedSubstance left) (hright : RecognizedSubstance right) :
    sameCategory left right := by
  rcases hleft with hleft | hleft <;> rcases hright with hright | hright
  all_goals
    simp [sameCategory, hleft.idia.isSubstance, hright.idia.isSubstance]

theorem recognizedQuality_sameCategory [Manual]
    {left right : PositionedCandidate}
    (hleft : RecognizedQuality left) (hright : RecognizedQuality right) :
    sameCategory left right := by
  simp [sameCategory, hleft.idia.isQuality, hright.idia.isQuality]

end Aristotle.Categories
