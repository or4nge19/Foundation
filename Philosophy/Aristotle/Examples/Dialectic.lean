import Philosophy.Aristotle.InquiryBoundary

namespace Aristotle.Examples.Dialectic

open Aristotle.Categories
open Aristotle.Dialectic
open Aristotle.InquiryBoundary
open Aristotle.PosteriorAnalytics

abbrev DemoTerm := Aristotle.Categories.Term
abbrev DemoSignified := Aristotle.Categories.Signified
abbrev DemoLogos := Aristotle.Categories.Logos
abbrev CoreCategory := Philosophy.Aristotle.Core.Category

@[simp] def mkLexis (tokens : List String) : Lexis :=
  Philosophy.Aristotle.Core.Lexis.ofWords tokens

@[simp] def mkTerm (tokens : List String) : DemoTerm :=
  Philosophy.Aristotle.Core.Term.ofWords tokens

@[simp] def mkReferent (tokens : List String) : DemoSignified :=
  Philosophy.Aristotle.Core.Signified.ofWords tokens

@[simp] def mkLogos (tokens : List String) : DemoLogos :=
  Philosophy.Aristotle.Core.Logos.ofWords tokens

def substanceCategory : CoreCategory := .substance
def qualityCategory : CoreCategory := .quality
def actionCategory : CoreCategory := .action
def affectionCategory : CoreCategory := .affection
def contraryOpposition : OppositionKind := .contrary

def soulTerm : DemoTerm := mkTerm ["soul"]
def harmonyTerm : DemoTerm := mkTerm ["harmony"]
def humanTerm : DemoTerm := mkTerm ["human"]
def animalTerm : DemoTerm := mkTerm ["animal"]
def rationalAnimalTerm : DemoTerm := mkTerm ["rational", "animal"]
def rationalTerm : DemoTerm := mkTerm ["rational"]
def laughableTerm : DemoTerm := mkTerm ["laughable"]
def seeingTerm : DemoTerm := mkTerm ["seeing"]
def heatingTerm : DemoTerm := mkTerm ["heating"]

def soulReferent : DemoSignified := mkReferent ["soul"]
def harmonyReferent : DemoSignified := mkReferent ["harmony"]
def humanReferent : DemoSignified := mkReferent ["human"]
def animalReferent : DemoSignified := mkReferent ["animal"]
def rationalAnimalReferent : DemoSignified := mkReferent ["rational", "animal"]
def rationalReferent : DemoSignified := mkReferent ["rational"]
def laughableReferent : DemoSignified := mkReferent ["laughable"]
def seeingReferent : DemoSignified := mkReferent ["seeing"]
def heatingReferent : DemoSignified := mkReferent ["heating"]

def soulLogos : DemoLogos := mkLogos ["substantial", "source", "of", "life"]
def harmonyLogos : DemoLogos := mkLogos ["ordered", "tuning"]
def humanLogos : DemoLogos := mkLogos ["two-footed", "living", "being"]
def animalLogos : DemoLogos := mkLogos ["living", "being"]
def rationalAnimalLogos : DemoLogos := mkLogos ["rational", "animal"]
def rationalLogos : DemoLogos := mkLogos ["capable", "of", "reason"]
def laughableLogos : DemoLogos := mkLogos ["capable", "of", "laughter"]
def seeingLogos : DemoLogos := mkLogos ["visual", "reception"]
def heatingLogos : DemoLogos := mkLogos ["warming", "another", "body"]

@[simp] theorem humanReferent_ne_animalReferent : humanReferent ≠ animalReferent := by
  decide

@[simp] theorem animalReferent_ne_humanReferent : animalReferent ≠ humanReferent := by
  intro h
  exact humanReferent_ne_animalReferent h.symm

@[simp] theorem soulReferent_ne_humanReferent : soulReferent ≠ humanReferent := by
  decide

@[simp] theorem soulReferent_ne_animalReferent : soulReferent ≠ animalReferent := by
  decide

@[simp] theorem soulReferent_ne_rationalReferent : soulReferent ≠ rationalReferent := by
  decide

@[simp] theorem soulReferent_ne_laughableReferent : soulReferent ≠ laughableReferent := by
  decide

@[simp] theorem soulReferent_ne_rationalAnimalReferent :
    soulReferent ≠ rationalAnimalReferent := by
  decide

@[simp] theorem rationalReferent_ne_laughableReferent :
    rationalReferent ≠ laughableReferent := by
  decide

@[simp] theorem laughableReferent_ne_rationalReferent :
    laughableReferent ≠ rationalReferent := by
  intro h
  exact rationalReferent_ne_laughableReferent h.symm

def hierarchyLe (left right : DemoSignified) : Prop :=
  left = right ∨ (left = humanReferent ∧ right = animalReferent)

def categoryOf (referent : DemoSignified) : Option Category :=
  match referent.tokens with
  | ["soul"] => some substanceCategory
  | ["harmony"] => some qualityCategory
  | ["human"] => some substanceCategory
  | ["animal"] => some substanceCategory
  | ["rational", "animal"] => some substanceCategory
  | ["rational"] => some qualityCategory
  | ["laughable"] => some qualityCategory
  | ["seeing"] => some affectionCategory
  | ["heating"] => some actionCategory
  | _ => none

def meaningOf (term : DemoTerm) : Option (DemoSignified × DemoLogos) :=
  match term.lexis.tokens with
  | ["soul"] => some (soulReferent, soulLogos)
  | ["harmony"] => some (harmonyReferent, harmonyLogos)
  | ["human"] => some (humanReferent, humanLogos)
  | ["animal"] => some (animalReferent, animalLogos)
  | ["rational", "animal"] => some (rationalAnimalReferent, rationalAnimalLogos)
  | ["rational"] => some (rationalReferent, rationalLogos)
  | ["laughable"] => some (laughableReferent, laughableLogos)
  | ["seeing"] => some (seeingReferent, seeingLogos)
  | ["heating"] => some (heatingReferent, heatingLogos)
  | _ => none

def genusOfRel (predicate subject : DemoSignified) : Prop :=
  hierarchyLe subject predicate ∧ ¬ hierarchyLe predicate subject

def differentiaOfRel (predicate subject : DemoSignified) : Prop :=
  predicate = rationalReferent ∧ subject = humanReferent

def propriumOfRel (predicate subject : DemoSignified) : Prop :=
  predicate = laughableReferent ∧ subject = humanReferent

def definitionRel (predicate subject : DemoSignified) : Prop :=
  predicate = rationalAnimalReferent ∧ subject = humanReferent

def saidOfRel (predicate subject : DemoSignified) : Prop :=
  genusOfRel predicate subject ∨
    differentiaOfRel predicate subject ∨
    propriumOfRel predicate subject ∨
    definitionRel predicate subject

def inSubjectRel (_predicate _subject : DemoSignified) : Prop := False

def demoSurfaceVoice (term : DemoTerm) : Option SurfaceVoice :=
  match term.lexis.tokens with
  | ["seeing"] => some .active
  | ["heating"] => some .active
  | _ => none

def demoSurfaceTraps (term : DemoTerm) : List SurfaceTrap :=
  Option.toList ((demoSurfaceVoice term).map SurfaceTrap.ofVoice)

lemma demoVoice_surfaceTrap {term : DemoTerm} {voice : SurfaceVoice}
    (h : demoSurfaceVoice term = some voice) :
    SurfaceTrap.ofVoice voice ∈ demoSurfaceTraps term := by
  simp [demoSurfaceTraps, h]

instance : PredicationalManual where
  Hom _ _ := PEmpty
  thin := by
    infer_instance
  signifies_as term referent logos := meaningOf term = some (referent, logos)
  saidOfTest referent := ∃ subject : DemoSignified, saidOfRel referent subject
  inSubjectTest referent := ∃ subject : DemoSignified, inSubjectRel referent subject
  fallsUnderTest referent category := categoryOf referent = some category
  signifiesThisTest referent := categoryOf referent = some substanceCategory
  similarityTest referent := categoryOf referent = some qualityCategory
  surfaceVoice := demoSurfaceVoice
  surfaceTraps := demoSurfaceTraps
  voice_surfaceTrap := by
    intro term voice hvoice
    exact demoVoice_surfaceTrap hvoice
  le := hierarchyLe
  le_refl := by
    intro referent
    exact Or.inl rfl
  le_trans := by
    intro left middle right hleft hright
    rcases hleft with rfl | ⟨hleftHuman, hmiddleAnimal⟩
    · exact hright
    · rcases hright with hEq | ⟨hmiddleHuman, hrightAnimal⟩
      · subst hEq
        exact Or.inr ⟨hleftHuman, hmiddleAnimal⟩
      · have : humanReferent = animalReferent := by
          simpa [hmiddleAnimal] using hmiddleHuman.symm
        exact False.elim (humanReferent_ne_animalReferent this)
  le_antisymm := by
    intro left right hleft hright
    rcases hleft with rfl | ⟨hleftHuman, hrightAnimal⟩
    · rfl
    · rcases hright with hEq | ⟨hrightHuman, hleftAnimal⟩
      · have hEq' := hEq
        simp [hleftHuman, hrightAnimal] at hEq'
      · have : humanReferent = animalReferent := by
          simpa [hleftAnimal] using hleftHuman.symm
        exact False.elim (humanReferent_ne_animalReferent this)
  genus_of := genusOfRel
  species_of := genusOfRel
  profile
    | .substance => { kind := substanceCategory }
    | .quality =>
        { kind := qualityCategory
          oppositions := [contraryOpposition]
          hasContrary := True
          admitsMoreAndLess := True }
    | category => { kind := category }
  category_unique := by
    intro b left right hleft hright
    exact Option.some.inj (hleft.symm.trans hright)
  profile_matches := by
    intro category
    cases category <;> rfl
  similarity_of_quality := by
    intro b hb
    simpa [Manual.similarityTest] using hb
  quality_of_similarity := by
    intro b hb
    simpa [Manual.fallsUnderTest] using hb
  said_of := saidOfRel
  in_subject := inSubjectRel
  differentia_of := differentiaOfRel
  proprium_of := propriumOfRel
  accident_of _ _ := False
  falls_under referent category := categoryOf referent = some category
  genus_iff_lt := by
    intro g s
    rfl
  species_iff_lt := by
    intro sp s
    rfl
  order_implies_said_of := by
    intro universal particular h
    exact Or.inl h
  differentia_implies_said_of := by
    intro d s h
    exact Or.inr <| Or.inl h
  genus_respects_category := by
    intro g s category hgenus hs
    rcases hgenus with ⟨hforward, hbackward⟩
    rcases hforward with hEq | ⟨hsHuman, hgAnimal⟩
    · exfalso
      exact hbackward (Or.inl hEq.symm)
    · rcases hsHuman with rfl
      rcases hgAnimal with rfl
      have hcategory : category = substanceCategory := by
        exact Option.some.inj (by simpa [categoryOf, humanReferent] using hs.symm)
      subst hcategory
      simp [categoryOf, animalReferent]
  proprium_implies_said_of := by
    intro p s h
    exact Or.inr <| Or.inr <| Or.inl h
  differentia_not_in_subject := by
    intro d s carrier h
    simp [inSubjectRel]
  proprium_not_in_subject := by
    intro p s carrier h
    simp [inSubjectRel]
  saidOfTest_iff := by
    intro b
    rfl
  inSubjectTest_iff := by
    intro b
    rfl
  fallsUnderTest_iff := by
    intro b category
    rfl

lemma notParonymous (term : DemoTerm) :
    ¬ RequiresParonymResolution term := by
  intro h
  rcases h with ⟨root, left, right, hpar⟩
  exact nomatch hpar.1

lemma meaning_unique
    {term : DemoTerm} {referent : DemoSignified} {logos : DemoLogos}
    (hw : meaningOf term = some (referent, logos))
    {referent' : DemoSignified} {logos' : DemoLogos}
    (h : meaningOf term = some (referent', logos')) :
    referent' = referent ∧ logos' = logos := by
  have hpairs : (referent', logos') = (referent, logos) := by
    exact Option.some.inj (h.symm.trans hw)
  cases hpairs
  exact ⟨rfl, rfl⟩

def mkCandidate (term : DemoTerm) (referent : DemoSignified) (logos : DemoLogos)
    (hw : meaningOf term = some (referent, logos)) :
    CategorialCandidate where
  term := term
  referent := referent
  logos := logos
  witness := hw
  univocal := by
    refine ⟨referent, logos, hw, ?_⟩
    intro referent' logos' h
    exact meaning_unique hw h
  notParonymous := notParonymous term

def soulCandidate : CategorialCandidate :=
  mkCandidate soulTerm soulReferent soulLogos (by
    rfl)

def harmonyCandidate : CategorialCandidate :=
  mkCandidate harmonyTerm harmonyReferent harmonyLogos (by
    rfl)

def humanCandidate : CategorialCandidate :=
  mkCandidate humanTerm humanReferent humanLogos (by
    rfl)

def animalCandidate : CategorialCandidate :=
  mkCandidate animalTerm animalReferent animalLogos (by
    rfl)

def rationalAnimalCandidate : CategorialCandidate :=
  mkCandidate rationalAnimalTerm rationalAnimalReferent rationalAnimalLogos (by
    rfl)

def rationalCandidate : CategorialCandidate :=
  mkCandidate rationalTerm rationalReferent rationalLogos (by
    rfl)

def laughableCandidate : CategorialCandidate :=
  mkCandidate laughableTerm laughableReferent laughableLogos (by
    rfl)

def seeingCandidate : CategorialCandidate :=
  mkCandidate seeingTerm seeingReferent seeingLogos (by
    rfl)

def heatingCandidate : CategorialCandidate :=
  mkCandidate heatingTerm heatingReferent heatingLogos (by
    rfl)

def soulPositioned : PositionedCandidate where
  candidate := soulCandidate
  placement :=
    { category := substanceCategory
      witness := by
        change categoryOf soulReferent = some substanceCategory
        rfl }

def harmonyPositioned : PositionedCandidate where
  candidate := harmonyCandidate
  placement :=
    { category := qualityCategory
      witness := by
        change categoryOf harmonyReferent = some qualityCategory
        rfl }

def humanPositioned : PositionedCandidate where
  candidate := humanCandidate
  placement :=
    { category := substanceCategory
      witness := by
        change categoryOf humanReferent = some substanceCategory
        rfl }

def animalPositioned : PositionedCandidate where
  candidate := animalCandidate
  placement :=
    { category := substanceCategory
      witness := by
        change categoryOf animalReferent = some substanceCategory
        rfl }

def rationalAnimalPositioned : PositionedCandidate where
  candidate := rationalAnimalCandidate
  placement :=
    { category := substanceCategory
      witness := by
        change categoryOf rationalAnimalReferent = some substanceCategory
        rfl }

def rationalPositioned : PositionedCandidate where
  candidate := rationalCandidate
  placement :=
    { category := qualityCategory
      witness := by
        change categoryOf rationalReferent = some qualityCategory
        rfl }

def laughablePositioned : PositionedCandidate where
  candidate := laughableCandidate
  placement :=
    { category := qualityCategory
      witness := by
        change categoryOf laughableReferent = some qualityCategory
        rfl }

def seeingPositioned : PositionedCandidate where
  candidate := seeingCandidate
  placement :=
    { category := affectionCategory
      witness := by
        change categoryOf seeingReferent = some affectionCategory
        rfl }

def heatingPositioned : PositionedCandidate where
  candidate := heatingCandidate
  placement :=
    { category := actionCategory
      witness := by
        change categoryOf heatingReferent = some actionCategory
        rfl }

example : hasSurfaceVoice seeingTerm .active := by
  rfl

example : surfaceCategorySuggestion seeingTerm Category.poiein := by
  exact ⟨SurfaceTrap.ofVoice .active, demoVoice_surfaceTrap rfl, by rfl⟩

example : surfaceCategorySuggestion heatingTerm Category.poiein := by
  exact ⟨SurfaceTrap.ofVoice .active, demoVoice_surfaceTrap rfl, by rfl⟩

def seeingActiveSurfaceAffection : ActiveSurfaceAffection seeingPositioned := by
  exact ⟨rfl, rfl⟩

def seeingFigureOfSpeechMismatch : FigureOfSpeechMismatch seeingPositioned :=
  ActiveSurfaceAffection.figureOfSpeechMismatch seeingActiveSurfaceAffection

def seeingHeatingGenusProblem : PositionedGenusProblem :=
  ⟨seeingPositioned, heatingPositioned⟩

def seeingHeatingDefinitionPositionedPhrase : PositionedDefinitionalPhrase :=
  { genus := heatingPositioned
    differentiae := [laughablePositioned]
    lexicalForm := some (mkLexis ["laughable", "heating"])
    nonempty := by simp }

def seeingHeatingDefinitionProblem : PositionedDefinitionProblem :=
  ⟨seeingPositioned, seeingHeatingDefinitionPositionedPhrase⟩

def soulHarmonyDefinitionPositionedPhrase : PositionedDefinitionalPhrase :=
  { genus := harmonyPositioned
    differentiae := [laughablePositioned]
    lexicalForm := some (mkLexis ["laughable", "harmony"])
    nonempty := by simp }

def soulHarmonyDefinitionProblem : PositionedDefinitionProblem :=
  ⟨soulPositioned, soulHarmonyDefinitionPositionedPhrase⟩

example : GenusRefutationByFigureOfSpeechMismatch seeingHeatingGenusProblem := by
  exact ⟨seeingFigureOfSpeechMismatch, rfl⟩

example : ¬ sameCategory seeingPositioned heatingPositioned := by
  exact FigureOfSpeechMismatch.not_sameCategory_of_suggestedCategory
    seeingFigureOfSpeechMismatch rfl

example : CategoryMismatch seeingPositioned heatingPositioned := by
  refine ⟨?_⟩
  exact FigureOfSpeechMismatch.not_sameCategory_of_suggestedCategory
    seeingFigureOfSpeechMismatch rfl

example : DefinitionRefutationByFigureOfSpeechMismatch seeingHeatingDefinitionProblem := by
  exact ⟨seeingFigureOfSpeechMismatch, rfl⟩

example : GenusRefutationBySurfaceTrapMismatch seeingHeatingGenusProblem := by
  exact genusFigureOfSpeechMismatch_surfaceTrapMismatch
    (problem := seeingHeatingGenusProblem) ⟨seeingFigureOfSpeechMismatch, rfl⟩

example : DefinitionRefutationBySurfaceTrapMismatch seeingHeatingDefinitionProblem := by
  exact definitionFigureOfSpeechMismatch_surfaceTrapMismatch
    (problem := seeingHeatingDefinitionProblem) ⟨seeingFigureOfSpeechMismatch, rfl⟩

example :
    diagnoseDefinition seeingHeatingDefinitionProblem =
      DefinitionDiagnosis.figureOfSpeechMismatch ⟨seeingFigureOfSpeechMismatch, rfl⟩ := by
  exact diagnoseDefinition_of_figureOfSpeechMismatch
    (problem := seeingHeatingDefinitionProblem) ⟨seeingFigureOfSpeechMismatch, rfl⟩

example :
    ¬ ∃ provisional : ProvisionalGenus,
      provisional.subject = seeingHeatingGenusProblem.subject ∧
        provisional.genus = seeingHeatingGenusProblem.genusTerm := by
  exact genusSurfaceTrapMismatch_not_provisionalGenus
    (problem := seeingHeatingGenusProblem)
    (genusFigureOfSpeechMismatch_surfaceTrapMismatch
      (problem := seeingHeatingGenusProblem) ⟨seeingFigureOfSpeechMismatch, rfl⟩)

example :
    ¬ ∃ dossier, diagnoseDefinition seeingHeatingDefinitionProblem =
      DefinitionDiagnosis.admissible dossier := by
  exact diagnoseDefinition_not_admissible_of_surfaceTrapMismatch
    (problem := seeingHeatingDefinitionProblem)
    (definitionFigureOfSpeechMismatch_surfaceTrapMismatch
      (problem := seeingHeatingDefinitionProblem) ⟨seeingFigureOfSpeechMismatch, rfl⟩)

example {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} :
    ¬ NaiveScientificPromotionIn science seeingHeatingDefinitionProblem := by
  exact not_naiveScientificPromotionIn_of_definitionFigureOfSpeechMismatch
    (problem := seeingHeatingDefinitionProblem) ⟨seeingFigureOfSpeechMismatch, rfl⟩

example {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} :
    ¬ NaiveScientificPromotionIn science seeingHeatingDefinitionProblem := by
  exact not_naiveScientificPromotionIn_of_definitionSurfaceTrapMismatch
    (problem := seeingHeatingDefinitionProblem)
    (definitionFigureOfSpeechMismatch_surfaceTrapMismatch
      (problem := seeingHeatingDefinitionProblem) ⟨seeingFigureOfSpeechMismatch, rfl⟩)

example :
    ∃ h, diagnoseDefinition soulHarmonyDefinitionProblem =
      DefinitionDiagnosis.categoryMismatch h := by
  have hfigure :
      ¬ DefinitionRefutationByFigureOfSpeechMismatch soulHarmonyDefinitionProblem := by
    rintro ⟨⟨voice, hsurface, _⟩, _⟩
    change hasSurfaceVoice soulTerm voice at hsurface
    have hnone : Manual.surfaceVoice soulTerm = none := by rfl
    unfold hasSurfaceVoice at hsurface
    rw [hnone] at hsurface
    cases hsurface
  have hcategory :
      DefinitionRefutationByCategoryMismatch
        soulHarmonyDefinitionProblem.subject soulHarmonyDefinitionProblem.phrase := by
    change ¬ substanceCategory = qualityCategory
    decide
  exact (diagnoseDefinition_eq_categoryMismatch_iff (problem := soulHarmonyDefinitionProblem)).2
    ⟨hfigure, hcategory⟩

example {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} :
    ¬ NaiveScientificPromotionIn science soulHarmonyDefinitionProblem := by
  have hcategory :
      DefinitionRefutationByCategoryMismatch
        soulHarmonyDefinitionProblem.subject soulHarmonyDefinitionProblem.phrase := by
    change ¬ substanceCategory = qualityCategory
    decide
  exact not_naiveScientificPromotionIn_of_definitionCategoryMismatch
    (problem := soulHarmonyDefinitionProblem) hcategory

example :
    diagnoseGenus seeingHeatingGenusProblem =
      GenusDiagnosis.figureOfSpeechMismatch ⟨seeingFigureOfSpeechMismatch, rfl⟩ := by
  exact diagnoseGenus_of_figureOfSpeechMismatch
    (problem := seeingHeatingGenusProblem) ⟨seeingFigureOfSpeechMismatch, rfl⟩

def soulPrimary : RecognizedPrimarySubstance soulPositioned where
  idia :=
    { isSubstance := by
        rfl
      lacksContrary := by
        change ¬ False
        simp
      lacksMoreAndLess := by
        change ¬ False
        simp }
  signifiesThis := by
    change categoryOf soulReferent = some substanceCategory
    rfl
  notSaidOf := by
    intro hsaid
    rcases hsaid with ⟨subject, hsaid⟩
    rcases hsaid with hgenus | hdifferentia | hproprium | hdefinition
    · rcases hgenus with ⟨hforward, hbackward⟩
      rcases hforward with hEq | ⟨hsubjectHuman, hsoulAnimal⟩
      · exact hbackward (Or.inl hEq.symm)
      · have : soulReferent = animalReferent := hsoulAnimal
        simp at this
    · have : soulReferent = rationalReferent := hdifferentia.1
      simp at this
    · have : soulReferent = laughableReferent := hproprium.1
      simp at this
    · have : soulReferent = rationalAnimalReferent := hdefinition.1
      simp at this
  notInSubject := by
    change ¬ ∃ subject : DemoSignified, inSubjectRel soulReferent subject
    simp [inSubjectRel]

lemma harmonyHasContrary : hasContrary harmonyPositioned := by
  change True
  trivial

lemma humanHasAnimalGenus :
    genusOfSubject animalCandidate humanCandidate := by
  change genusOfRel animalReferent humanReferent
  constructor
  · exact Or.inr ⟨rfl, rfl⟩
  · simp [hierarchyLe, humanReferent_ne_animalReferent, animalReferent_ne_humanReferent]

lemma soulHasNoAnimalGenus :
    ¬ genusOfSubject animalCandidate soulCandidate := by
  intro hgenus
  change genusOfRel animalReferent soulReferent at hgenus
  rcases hgenus with ⟨hforward, _⟩
  rcases hforward with hEq | ⟨hsoulHuman, _⟩
  · simp at hEq
  · simp at hsoulHuman

def animalSecondary : RecognizedSecondarySubstance animalPositioned where
  idia :=
    { isSubstance := by
        rfl
      lacksContrary := by
        change ¬ False
        simp
      lacksMoreAndLess := by
        change ¬ False
        simp }
  saidOf := isSaidOf_of_genusOfSubject humanHasAnimalGenus
  notInSubject := by
    change ¬ ∃ subject : DemoSignified, inSubjectRel animalReferent subject
    simp [inSubjectRel]

lemma humanHasRationalDifferentia :
    differentiaOfSubject rationalCandidate humanCandidate := by
  exact ⟨rfl, rfl⟩

lemma humanIsLaughable :
    propriumOfSubject laughableCandidate humanCandidate := by
  exact ⟨rfl, rfl⟩

lemma humanIsNotRationalProprium :
    ¬ propriumOfSubject rationalCandidate humanCandidate := by
  change ¬ propriumOfRel rationalReferent humanReferent
  simp [propriumOfRel, rationalReferent, laughableReferent, humanReferent]

lemma humanHasNoLaughableDifferentia :
    ¬ differentiaOfSubject laughableCandidate humanCandidate := by
  change ¬ differentiaOfRel laughableReferent humanReferent
  simp [differentiaOfRel, laughableReferent, rationalReferent, humanReferent]

example :
    GenusRefutationByContraryMismatch soulPositioned harmonyPositioned :=
  contraryMismatch_of_recognizedSubstance (Or.inl soulPrimary) harmonyHasContrary

example : sameCategory soulPositioned animalPositioned :=
  recognizedSubstance_sameCategory (Or.inl soulPrimary) (Or.inr animalSecondary)

example : sameCategory humanPositioned animalPositioned :=
  sameCategory_of_genusOfSubject humanHasAnimalGenus

example : GenusDossier humanPositioned animalPositioned :=
  genusDossier_of_genusOfSubject humanHasAnimalGenus

example : isSaidOf animalCandidate :=
  isSaidOf_of_genusOfSubject humanHasAnimalGenus

example : isSaidOf rationalCandidate :=
  isSaidOf_of_differentiaOfSubject humanHasRationalDifferentia

example : ¬ isInSubject rationalCandidate :=
  notInSubject_of_differentiaOfSubject humanHasRationalDifferentia

example : isSaidOf laughableCandidate :=
  isSaidOf_of_propriumOfSubject humanIsLaughable

example : PropriumDossier humanPositioned laughablePositioned :=
  propriumDossier_of_propriumOfSubject humanIsLaughable

def soulAnimalGenusProblem : PositionedGenusProblem :=
  ⟨soulPositioned, animalPositioned⟩

example :
    ∃ h, diagnoseGenus soulAnimalGenusProblem =
      GenusDiagnosis.notSaidOf h := by
  have hsame : sameCategory soulPositioned animalPositioned := by
    rfl
  have hcontra :
      ¬ GenusRefutationByContraryMismatch soulPositioned animalPositioned := by
    simp [GenusRefutationByContraryMismatch, ContraryMismatch,
      hasContrary, lacksContrary, categoryHasContrary,
      soulPositioned, animalPositioned]
  have hdegree :
      ¬ GenusRefutationByDegreeMismatch soulPositioned animalPositioned := by
    simp [GenusRefutationByDegreeMismatch, DegreeMismatch,
      admitsMoreAndLess, lacksMoreAndLess, categoryAdmitsMoreAndLess,
      soulPositioned, animalPositioned]
  have hfigure :
      ¬ GenusRefutationByFigureOfSpeechMismatch soulAnimalGenusProblem := by
    intro h
    rcases h with ⟨⟨voice, _, _⟩, hvoice⟩
    cases voice
    · cases hvoice
    · cases hvoice
  let hgenus : GenusRefutationByNotSaidOf soulPositioned animalPositioned :=
    soulHasNoAnimalGenus
  exact ⟨hgenus, diagnoseGenus_of_notSaidOf
    (problem := soulAnimalGenusProblem) hfigure hsame hcontra hdegree hgenus⟩

def humanDefinitionPhrase : Aristotle.Categories.DefinitionalPhrase :=
  { genus := animalTerm
    differentiae := [rationalTerm]
    lexicalForm := some (mkLexis ["rational", "animal"]) }

def humanDialecticalDefinition : Aristotle.Categories.DialecticalDefinition :=
  humanDefinitionPhrase.asDialecticalDefinition

def emptyDefinitionPhrase : Aristotle.Categories.DefinitionalPhrase :=
  { genus := animalTerm
    differentiae := []
    lexicalForm := some (mkLexis ["animal"]) }

def emptyDialecticalDefinition : Aristotle.Categories.DialecticalDefinition :=
  emptyDefinitionPhrase.asDialecticalDefinition

def humanLaughableDefinitionPhrase : Aristotle.Categories.DefinitionalPhrase :=
  { genus := animalTerm
    differentiae := [laughableTerm]
    lexicalForm := some (mkLexis ["laughable", "animal"]) }

def humanLaughableDialecticalDefinition : Aristotle.Categories.DialecticalDefinition :=
  humanLaughableDefinitionPhrase.asDialecticalDefinition

def humanDefinitionPositionedPhrase : PositionedDefinitionalPhrase :=
  { genus := animalPositioned
    differentiae := [rationalPositioned]
    lexicalForm := some (mkLexis ["rational", "animal"])
    nonempty := by simp }

def humanLaughableDefinitionPositionedPhrase : PositionedDefinitionalPhrase :=
  { genus := animalPositioned
    differentiae := [laughablePositioned]
    lexicalForm := some (mkLexis ["laughable", "animal"])
    nonempty := by simp }

lemma humanLaughableDefinitionDifferentiaNotSaidOf :
    DefinitionRefutationByDifferentiaNotSaidOf
      humanPositioned humanLaughableDefinitionPositionedPhrase := by
  exact ⟨laughablePositioned, by simp [humanLaughableDefinitionPositionedPhrase], by
    simpa [humanPositioned, laughablePositioned] using humanHasNoLaughableDifferentia⟩

/--
This uses `Set` intersection as a mathlib-native stand-in for Menn's idea that
a dialectical definition locates its target by intersecting a genus with its
differentiae.
-/
def locatorOf (term : DemoTerm) : Set DemoSignified :=
  match term.lexis.tokens with
  | ["animal"] => { referent | referent = animalReferent ∨ referent = humanReferent }
  | ["rational"] => { referent | referent = humanReferent }
  | ["laughable"] => { referent | referent = humanReferent }
  | ["soul"] => { referent | referent = soulReferent }
  | ["harmony"] => { referent | referent = harmonyReferent }
  | ["rational", "animal"] => { referent | referent = humanReferent }
  | _ => ∅

example :
    humanDefinitionPhrase.meaning locatorOf = { referent | referent = humanReferent } := by
  ext referent
  change ((referent = animalReferent ∨ referent = humanReferent) ∧ referent = humanReferent) ↔
      referent = humanReferent
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨Or.inr h, h⟩

def humanEmptyDefinitionProblem : Problem :=
  .definition humanTerm emptyDialecticalDefinition

def humanDefinitionProblem : PositionedDefinitionProblem :=
  ⟨humanPositioned, humanDefinitionPositionedPhrase⟩

def humanLaughableDefinitionProblem : PositionedDefinitionProblem :=
  ⟨humanPositioned, humanLaughableDefinitionPositionedPhrase⟩

def humanPropriumProblem : PositionedPropriumProblem :=
  ⟨humanPositioned, laughablePositioned⟩

def humanRationalPropriumProblem : PositionedPropriumProblem :=
  ⟨humanPositioned, rationalPositioned⟩

example : (Problem.definition humanTerm humanDialecticalDefinition).aim = .hoti := by
  rfl

example : (Problem.genus humanTerm animalTerm).aim = .hoti := by
  rfl

example :
    Aristotle.InquiryBoundary.problemWhyQuestion? (Problem.genus humanTerm animalTerm) =
      some (WhyQuestion.ofConclusion (Aristotle.PriorAnalytics.Categorical.A humanTerm animalTerm)) := by
  exact Aristotle.InquiryBoundary.problemWhyQuestion_eq_some_of_statement
    (problem := .genus humanTerm animalTerm) rfl

example :
    (WhyQuestion.ofConclusion (Aristotle.PriorAnalytics.Categorical.A humanTerm animalTerm)).conclusion =
      Aristotle.PriorAnalytics.Categorical.A humanTerm animalTerm := by
  exact Aristotle.InquiryBoundary.problemOfConclusion_sameConclusion_of_statement
    (problem := .genus humanTerm animalTerm) rfl

example :
    (WhyQuestion.ofConclusion (Aristotle.PriorAnalytics.Categorical.A humanTerm animalTerm)).aim ≠
      (Problem.genus humanTerm animalTerm).aim := by
  exact Aristotle.InquiryBoundary.problemWhyQuestion_differentAim_of_statement
    (problem := .genus humanTerm animalTerm) rfl

example :
    screenDefinitionalPhrase emptyDialecticalDefinition =
      Except.error (.emptyDifferentiae emptyDialecticalDefinition) := by
  have hnil : emptyDialecticalDefinition.differentiae = [] := by
    rfl
  simp [screenDefinitionalPhrase, hnil]

example :
    ∃ dossier, diagnoseDefinition humanDefinitionProblem =
      DefinitionDiagnosis.admissible dossier := by
  have hfigure :
      ¬ DefinitionRefutationByFigureOfSpeechMismatch humanDefinitionProblem := by
    rintro ⟨⟨voice, hsurface, _⟩, _⟩
    change hasSurfaceVoice humanTerm voice at hsurface
    have hnone : Manual.surfaceVoice humanTerm = none := by rfl
    unfold hasSurfaceVoice at hsurface
    rw [hnone] at hsurface
    cases hsurface
  have hfigure' :
      ¬ ∃ x : FigureOfSpeechMismatch humanPositioned,
          humanDefinitionPositionedPhrase.genus.placement.category = x.voice.suggestedCategory := by
    simpa [humanDefinitionProblem, DefinitionRefutationByFigureOfSpeechMismatch] using hfigure
  have hsame : sameCategory humanPositioned humanDefinitionPositionedPhrase.genus :=
    sameCategory_of_genusOfSubject humanHasAnimalGenus
  have hcontra :
      ¬ DefinitionRefutationByContraryMismatch
        humanPositioned humanDefinitionPositionedPhrase := by
    simp [DefinitionRefutationByContraryMismatch, ContraryMismatch,
      hasContrary, lacksContrary, categoryHasContrary,
      humanPositioned, humanDefinitionPositionedPhrase, animalPositioned]
  have hdegree :
      ¬ DefinitionRefutationByDegreeMismatch
        humanPositioned humanDefinitionPositionedPhrase := by
    simp [DefinitionRefutationByDegreeMismatch, DegreeMismatch,
      admitsMoreAndLess, lacksMoreAndLess, categoryAdmitsMoreAndLess,
      humanPositioned, humanDefinitionPositionedPhrase, animalPositioned]
  have hgenus :
      ¬ DefinitionRefutationByGenusNotSaidOf
        humanPositioned humanDefinitionPositionedPhrase := by
    intro hrefute
    exact hrefute humanHasAnimalGenus
  have hdifferentia :
      ¬ DefinitionRefutationByDifferentiaNotSaidOf
        humanPositioned humanDefinitionPositionedPhrase := by
    intro hrefute
    rcases hrefute with ⟨differentia, hmem, hnot⟩
    have hdiff : differentia = rationalPositioned := by
      simpa [humanDefinitionPositionedPhrase] using hmem
    rcases hdiff with rfl
    exact hnot humanHasRationalDifferentia
  have hin :
      ¬ DefinitionRefutationByInSubject
        humanPositioned humanDefinitionPositionedPhrase := by
    intro hrefute
    rcases hrefute with ⟨differentia, hmem, hinDifferentia⟩
    have hdiff : differentia = rationalPositioned := by
      simpa [humanDefinitionPositionedPhrase] using hmem
    rcases hdiff with rfl
    exact (notInSubject_of_differentiaOfSubject humanHasRationalDifferentia) hinDifferentia
  refine ⟨
    ({ sameCategory := hsame
       contrary := contraryCompatibility_of_not_mismatch hcontra
       degree := degreeCompatibility_of_not_mismatch hdegree
       genusSaidOf := humanHasAnimalGenus
       differentiaeSaidOf := by
         intro differentia hmem
         have hdiff : differentia = rationalPositioned := by
           simpa [humanDefinitionProblem, humanDefinitionPositionedPhrase] using hmem
         rcases hdiff with rfl
         exact humanHasRationalDifferentia
       differentiaeNotInSubject := by
         intro differentia hmem hinDifferentia
         have hdiff : differentia = rationalPositioned := by
           simpa [humanDefinitionProblem, humanDefinitionPositionedPhrase] using hmem
         rcases hdiff with rfl
         exact
           (notInSubject_of_differentiaOfSubject humanHasRationalDifferentia)
             hinDifferentia } :
      DialecticalDefinitionDossier humanPositioned humanDefinitionPositionedPhrase),
    ?_⟩
  unfold humanDefinitionProblem diagnoseDefinition
  simp [DefinitionRefutationByFigureOfSpeechMismatch, hfigure', hsame, hcontra, hdegree,
    hgenus, hdifferentia, hin]

example :
    ∃ h, diagnoseDefinition humanLaughableDefinitionProblem =
      DefinitionDiagnosis.differentiaNotSaidOf h := by
  have hfigure :
      ¬ DefinitionRefutationByFigureOfSpeechMismatch humanLaughableDefinitionProblem := by
    rintro ⟨⟨voice, hsurface, _⟩, _⟩
    change hasSurfaceVoice humanTerm voice at hsurface
    have hnone : Manual.surfaceVoice humanTerm = none := by rfl
    unfold hasSurfaceVoice at hsurface
    rw [hnone] at hsurface
    cases hsurface
  have hfigure' :
      ¬ ∃ x : FigureOfSpeechMismatch humanPositioned,
          humanLaughableDefinitionPositionedPhrase.genus.placement.category =
            x.voice.suggestedCategory := by
    simpa [humanLaughableDefinitionProblem, DefinitionRefutationByFigureOfSpeechMismatch] using
      hfigure
  have hsame : sameCategory humanPositioned humanLaughableDefinitionPositionedPhrase.genus :=
    sameCategory_of_genusOfSubject humanHasAnimalGenus
  have hcontra :
      ¬ DefinitionRefutationByContraryMismatch
        humanPositioned humanLaughableDefinitionPositionedPhrase := by
    simp [DefinitionRefutationByContraryMismatch, ContraryMismatch,
      hasContrary, lacksContrary, categoryHasContrary,
      humanPositioned, humanLaughableDefinitionPositionedPhrase, animalPositioned]
  have hdegree :
      ¬ DefinitionRefutationByDegreeMismatch
        humanPositioned humanLaughableDefinitionPositionedPhrase := by
    simp [DefinitionRefutationByDegreeMismatch, DegreeMismatch,
      admitsMoreAndLess, lacksMoreAndLess, categoryAdmitsMoreAndLess,
      humanPositioned, humanLaughableDefinitionPositionedPhrase, animalPositioned]
  have hgenus :
      ¬ DefinitionRefutationByGenusNotSaidOf
        humanPositioned humanLaughableDefinitionPositionedPhrase := by
    intro hrefute
    exact hrefute humanHasAnimalGenus
  let hdifferentia :
      DefinitionRefutationByDifferentiaNotSaidOf
        humanPositioned humanLaughableDefinitionPositionedPhrase :=
    humanLaughableDefinitionDifferentiaNotSaidOf
  refine ⟨hdifferentia, ?_⟩
  unfold humanLaughableDefinitionProblem diagnoseDefinition
  simp [DefinitionRefutationByFigureOfSpeechMismatch, hfigure', hsame, hcontra, hdegree,
    hgenus, hdifferentia]

example {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} :
    ¬ NaiveScientificPromotionIn science humanLaughableDefinitionProblem := by
  exact not_naiveScientificPromotionIn_of_definitionDifferentiaNotSaidOf
    (problem := humanLaughableDefinitionProblem)
    humanLaughableDefinitionDifferentiaNotSaidOf

example :
    ∃ dossier, diagnoseProprium humanPropriumProblem =
      PropriumDiagnosis.admissible dossier := by
  have hprop :
      ¬ PropriumRefutationByNotSaidOf humanPositioned laughablePositioned := by
    intro hrefute
    exact hrefute humanIsLaughable
  have hin :
      ¬ PropriumRefutationByInSubject humanPositioned laughablePositioned := by
    change ¬ AntepredicamentalManual.inSubjectTest laughableCandidate.referent
    change ¬ ∃ subject : DemoSignified, inSubjectRel laughableReferent subject
    simp [inSubjectRel]
  refine ⟨{ propertySaidOf := humanIsLaughable, notInSubject := hin }, ?_⟩
  unfold humanPropriumProblem diagnoseProprium
  simp [hprop, hin]

example :
    ∃ h, diagnoseProprium humanRationalPropriumProblem =
      PropriumDiagnosis.notSaidOf h := by
  let hprop : PropriumRefutationByNotSaidOf
      humanPositioned rationalPositioned :=
    humanIsNotRationalProprium
  refine ⟨hprop, ?_⟩
  unfold humanRationalPropriumProblem diagnoseProprium
  simp [hprop]

def art : DialecticalArt where
  acceptedPremises _ := [Aristotle.PriorAnalytics.Categorical.A soulTerm soulTerm]

def endoxon : Endoxon :=
  ⟨Aristotle.PriorAnalytics.Categorical.A soulTerm soulTerm, .everyone⟩

def state : GameState where
  respondent := .many
  thesis := some (.genus soulTerm harmonyTerm)
  concessions := []
  availableEndoxa := [endoxon]

def definitionElenchusState : GameState where
  respondent := .many
  thesis := some (Problem.definition humanTerm humanDialecticalDefinition)
  concessions := [Aristotle.PriorAnalytics.Categorical.O humanTerm rationalTerm]
  availableEndoxa := []

example : state.stagedThesis? = some (stageProblem (.genus soulTerm harmonyTerm)) := by
  simp [GameState.stagedThesis?, state]

example : state.session.stagedThesis = state.stagedThesis? := by
  simp [state]

example : GameState.stagedThesis? (GameState.clearThesis state) = none := by
  simp [state]

example :
    GameState.stagedThesis?
        (GameState.withThesis state (Problem.definition humanTerm humanDialecticalDefinition)) =
      some (stageProblem (Problem.definition humanTerm humanDialecticalDefinition)) := by
  simp [state]

example :
    (GameState.proposeThesis state (Problem.definition humanTerm humanDialecticalDefinition)).1.thesis =
      some (Problem.definition humanTerm humanDialecticalDefinition) := by
  simp [state]

example :
    (GameState.proposeThesis state (Problem.definition humanTerm humanDialecticalDefinition)).2 =
      stageProblem (Problem.definition humanTerm humanDialecticalDefinition) := by
  simp [state]

example :
    (StagedSession.clearThesis state.session).stagedThesis = none := by
  simp [state]

example :
    (StagedSession.proposeThesis state.session
        (Problem.definition humanTerm humanDialecticalDefinition)).stagedThesis =
      some (stageProblem (Problem.definition humanTerm humanDialecticalDefinition)) := by
  simp [state]

example :
    (StagedSession.askConcession art state.session endoxon true).stagedThesis =
      state.session.stagedThesis := by
  simp [state]

example :
    definitionElenchusState.thesisRefutationTargets? =
      some [Aristotle.PriorAnalytics.Categorical.O humanTerm animalTerm,
        Aristotle.PriorAnalytics.Categorical.O humanTerm rationalTerm] := by
  rfl

example : Elenchus definitionElenchusState := by
  unfold Elenchus GameState.thesisRefutationTargets? definitionElenchusState
  refine ⟨Aristotle.PriorAnalytics.Categorical.O humanTerm rationalTerm, ?_, ?_⟩
  · have htargets :
        (Problem.definition humanTerm humanDialecticalDefinition).refutationTargets =
          [ Aristotle.PriorAnalytics.Categorical.O humanTerm animalTerm
          , Aristotle.PriorAnalytics.Categorical.O humanTerm rationalTerm ] := by
      rfl
    simp [htargets]
  · exact Aristotle.PriorAnalytics.Derives.premise (by simp)

example :
    endoxon.proposition ∈
      (StagedSession.askConcession art state.session endoxon true).state.concessions := by
  simpa [GameState.session, StagedSession.askConcession, StagedSession.ofState] using
    (askConcession_adds_available art state endoxon
      (by simp [state, endoxon])
      (by
        refine ⟨RespondentKind.everyone_admits _, ?_⟩
        simp [acceptableTo, art, endoxon]))

example : endoxon.proposition ∈ (askConcession art state endoxon true).concessions :=
  askConcession_adds_available art state endoxon
    (by simp [state, endoxon])
    (by
      refine ⟨RespondentKind.everyone_admits _, ?_⟩
      simp [acceptableTo, art, endoxon])

def humanAssignedDefinitionThesis : AssignedThesis :=
  { problem := Problem.definition humanTerm humanDialecticalDefinition
    standing := .unacceptable
    reference := .unqualified }

example :
    humanAssignedDefinitionThesis.expectedConclusionStanding = .acceptable := by
  rfl

def soulIdentityPremiss : CollectedPremiss :=
  { proposition := Aristotle.PriorAnalytics.Categorical.A soulTerm soulTerm
    origin := .direct .everyone
    domain := .logical }

def humanAnimalPremiss : CollectedPremiss :=
  { proposition := Aristotle.PriorAnalytics.Categorical.A humanTerm animalTerm
    origin := .direct .many
    domain := .logical }

def humanRationalPremiss : CollectedPremiss :=
  { proposition := Aristotle.PriorAnalytics.Categorical.A humanTerm rationalTerm
    origin := .fromWriting soulTerm
    domain := .scientific }

def premissTable : PremissTable :=
  { entries := [soulIdentityPremiss, humanAnimalPremiss, humanRationalPremiss] }

example :
    premissTable.aboutSubject humanTerm = [humanAnimalPremiss, humanRationalPremiss] := by
  rfl

example :
    premissTable.ofDomain .scientific = [humanRationalPremiss] := by
  simp [PremissTable.ofDomain, premissTable, soulIdentityPremiss,
    humanAnimalPremiss, humanRationalPremiss]

def humanAnimalQuestion : ArrangedQuestion :=
  { premiss := humanAnimalPremiss
    role := .necessary
    technique := .direct }

def soulIdentityConcealmentQuestion : ArrangedQuestion :=
  { premiss := soulIdentityPremiss
    role := .concealment
    technique := .interleaved }

def arrangedHumanDefinitionExchange : ArrangedExchange where
  thesis := humanAssignedDefinitionThesis
  target := Aristotle.PriorAnalytics.Categorical.O humanTerm rationalTerm
  questions := [humanAnimalQuestion, soulIdentityConcealmentQuestion]
  aligned := by
    have htargets :
        humanAssignedDefinitionThesis.problem.refutationTargets =
          [ Aristotle.PriorAnalytics.Categorical.O humanTerm animalTerm
          , Aristotle.PriorAnalytics.Categorical.O humanTerm rationalTerm ] := by
      rfl
    simp [htargets]
  conclusionNotAsked := by
    intro question hquestion
    have hquestion' :
        question = humanAnimalQuestion ∨ question = soulIdentityConcealmentQuestion := by
      simpa using hquestion
    rcases hquestion' with rfl | rfl
    · simp [humanAnimalQuestion, humanAnimalPremiss]
    · simp [soulIdentityConcealmentQuestion, soulIdentityPremiss]

example :
    arrangedHumanDefinitionExchange.necessaryQuestions = [humanAnimalQuestion] := by
  simp [ArrangedExchange.necessaryQuestions, arrangedHumanDefinitionExchange,
    humanAnimalQuestion, soulIdentityConcealmentQuestion]

example :
    arrangedHumanDefinitionExchange.additionalQuestions =
      [soulIdentityConcealmentQuestion] := by
  simp [ArrangedExchange.additionalQuestions, arrangedHumanDefinitionExchange,
    humanAnimalQuestion, soulIdentityConcealmentQuestion]

def pilotTerm : DemoTerm := mkTerm ["pilot"]
def charioteerTerm : DemoTerm := mkTerm ["charioteer"]
def knowerTerm : DemoTerm := mkTerm ["knower"]
def bestPilotTerm : DemoTerm := mkTerm ["best", "pilot"]
def bestCharioteerTerm : DemoTerm := mkTerm ["best", "charioteer"]
def bestCraftsmanTerm : DemoTerm := mkTerm ["best", "craftsman"]

def craftInduction : DialecticalInduction where
  cases :=
    [ Aristotle.PriorAnalytics.Categorical.A pilotTerm bestPilotTerm
    , Aristotle.PriorAnalytics.Categorical.A charioteerTerm bestCharioteerTerm ]
  universal := Aristotle.PriorAnalytics.Categorical.A knowerTerm bestCraftsmanTerm
  designation := .coined knowerTerm
  nonempty := by simp

example : craftInduction.mayAskForObjection := by
  exact craftInduction.nonempty

def freshCounterinstance : InductionObjection :=
  { kind := .freshCounterinstance (Aristotle.PriorAnalytics.Categorical.O soulTerm animalTerm) }

example : freshCounterinstance.properAgainst craftInduction := by
  simp [InductionObjection.properAgainst, craftInduction, freshCounterinstance]

def equivocalObjection : InductionObjection :=
  { kind := .equivocalCase humanTerm }

example : UniversalRepair.repairs (.distinction humanTerm) equivocalObjection := by
  simp [UniversalRepair.repairs, equivocalObjection]

def narrowedUniversalRepair : UniversalRepair :=
  .subtraction (Aristotle.PriorAnalytics.Categorical.A humanTerm animalTerm)
    [Aristotle.PriorAnalytics.Categorical.O soulTerm animalTerm]

example : narrowedUniversalRepair.repairs freshCounterinstance := by
  simp [UniversalRepair.repairs, narrowedUniversalRepair, freshCounterinstance]

example :
    adviseAnswerer .acceptable .relevant .clear =
      .concede (some .tooCloseToInitialThesis) := by
  rfl

example :
    adviseAnswerer .neither .irrelevant .unclear = .askClarification := by
  rfl

example : ¬ ObstructionMode.isSolution .time := by
  simp [ObstructionMode.isSolution]

end Aristotle.Examples.Dialectic
