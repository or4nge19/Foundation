import Philosophy.Aristotle.InquiryBoundary

namespace Aristotle.Examples.Demonstration

open Aristotle.Dialectic
open Aristotle.InquiryBoundary
open Aristotle.PriorAnalytics
open Aristotle.PosteriorAnalytics

abbrev DemoTerm := Aristotle.Categories.Term

def mkTerm (tokens : List String) : DemoTerm :=
  Philosophy.Aristotle.Core.Term.ofWords tokens

inductive Object
  | socrates
  | fido
  | stone
  deriving DecidableEq, Repr

structure ToyModel where
  marker : Unit := ()

def humanTerm : DemoTerm := mkTerm ["human"]
def animalTerm : DemoTerm := mkTerm ["animal"]
def mortalTerm : DemoTerm := mkTerm ["mortal"]
def stoneTerm : DemoTerm := mkTerm ["stone"]

def trackedTerm (term : DemoTerm) : Prop :=
  term = humanTerm ∨ term = animalTerm ∨ term = mortalTerm

instance trackedTermDecidable (term : DemoTerm) : Decidable (trackedTerm term) := by
  unfold trackedTerm
  infer_instance

def humanExtension : Set Object := { x | x = Object.socrates }

def animalExtension : Set Object := { x | x = Object.socrates ∨ x = Object.fido }

def mortalExtension : Set Object :=
  { x | x = Object.socrates ∨ x = Object.fido ∨ x = Object.stone }

def stoneExtension : Set Object := { x | x = Object.stone }

def extensionOfTerm (term : DemoTerm) : Set Object :=
  if term = humanTerm then
    humanExtension
  else if term = animalTerm then
    animalExtension
  else if term = mortalTerm then
    mortalExtension
  else if term = stoneTerm then
    stoneExtension
  else
    ∅

theorem human_ne_animal : humanTerm ≠ animalTerm := by
  decide

theorem human_ne_mortal : humanTerm ≠ mortalTerm := by
  decide

theorem animal_ne_mortal : animalTerm ≠ mortalTerm := by
  decide

theorem human_ne_stone : humanTerm ≠ stoneTerm := by
  decide

theorem animal_ne_stone : animalTerm ≠ stoneTerm := by
  decide

theorem mortal_ne_stone : mortalTerm ≠ stoneTerm := by
  decide

theorem animal_ne_human : animalTerm ≠ humanTerm := by
  intro h
  exact human_ne_animal h.symm

theorem mortal_ne_human : mortalTerm ≠ humanTerm := by
  intro h
  exact human_ne_mortal h.symm

theorem mortal_ne_animal : mortalTerm ≠ animalTerm := by
  intro h
  exact animal_ne_mortal h.symm

theorem stone_ne_human : stoneTerm ≠ humanTerm := by
  intro h
  exact human_ne_stone h.symm

theorem stone_ne_animal : stoneTerm ≠ animalTerm := by
  intro h
  exact animal_ne_stone h.symm

theorem stone_ne_mortal : stoneTerm ≠ mortalTerm := by
  intro h
  exact mortal_ne_stone h.symm

instance : Interpretation ToyModel where
  Subject := Object
  Moment := Unit
  extension _ term _ := extensionOfTerm term

def model : ToyModel := {}

@[simp] theorem mem_extension_human (x : Object) (t : Interpretation.Moment ToyModel) :
    x ∈ ExtensionAt model humanTerm t ↔ x = Object.socrates := by
  change x ∈ extensionOfTerm humanTerm ↔ x = Object.socrates
  simp [extensionOfTerm, humanExtension]

@[simp] theorem mem_extension_animal (x : Object) (t : Interpretation.Moment ToyModel) :
    x ∈ ExtensionAt model animalTerm t ↔ x = Object.socrates ∨ x = Object.fido := by
  change x ∈ extensionOfTerm animalTerm ↔ x = Object.socrates ∨ x = Object.fido
  rw [show extensionOfTerm animalTerm = animalExtension by
    simp [extensionOfTerm, animal_ne_human]]
  simp [animalExtension]

@[simp] theorem mem_extension_mortal (x : Object) (t : Interpretation.Moment ToyModel) :
    x ∈ ExtensionAt model mortalTerm t ↔
      x = Object.socrates ∨ x = Object.fido ∨ x = Object.stone := by
  change x ∈ extensionOfTerm mortalTerm ↔
      x = Object.socrates ∨ x = Object.fido ∨ x = Object.stone
  rw [show extensionOfTerm mortalTerm = mortalExtension by
    simp [extensionOfTerm, mortal_ne_human, mortal_ne_animal]]
  simp [mortalExtension]

@[simp] theorem mem_extension_stone (x : Object) (t : Interpretation.Moment ToyModel) :
    x ∈ ExtensionAt model stoneTerm t ↔ x = Object.stone := by
  change x ∈ extensionOfTerm stoneTerm ↔ x = Object.stone
  rw [show extensionOfTerm stoneTerm = stoneExtension by
    simp [extensionOfTerm, stone_ne_human, stone_ne_animal, stone_ne_mortal]]
  simp [stoneExtension]

def figured : FiguredSyllogism :=
  { minor := humanTerm
    middle := animalTerm
    major := mortalTerm
    mood := .barbara }

def majorPremise : Categorical := figured.majorPremise
def minorPremise : Categorical := figured.minorPremise
def conclusion : Categorical := figured.conclusion

def science : Science ToyModel model where
  subjectMatter := trackedTerm
  admits proposition := proposition = majorPremise ∨ proposition = minorPremise ∨ proposition = conclusion
  admits_subject := by
    intro proposition hadmits
    rcases hadmits with h | h | h
    · subst h
      change trackedTerm majorPremise.subject
      decide
    · subst h
      change trackedTerm minorPremise.subject
      decide
    · subst h
      change trackedTerm conclusion.subject
      decide
  admits_predicate := by
    intro proposition hadmits
    rcases hadmits with h | h | h
    · subst h
      change trackedTerm majorPremise.predicate
      decide
    · subst h
      change trackedTerm minorPremise.predicate
      decide
    · subst h
      change trackedTerm conclusion.predicate
      decide

theorem majorHoldsAt (t : Interpretation.Moment ToyModel) :
    HoldsAt model majorPremise t := by
  intro x hx
  refine (mem_extension_mortal x t).2 ?_
  rcases (mem_extension_animal x t).1 hx with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr <| Or.inl rfl

theorem minorHoldsAt (t : Interpretation.Moment ToyModel) :
    HoldsAt model minorPremise t := by
  intro x hx
  refine (mem_extension_animal x t).2 ?_
  rcases (mem_extension_human x t).1 hx with rfl
  exact Or.inl rfl

theorem conclusionHoldsAt (t : Interpretation.Moment ToyModel) :
    HoldsAt model conclusion t := by
  intro x hx
  refine (mem_extension_mortal x t).2 ?_
  rcases (mem_extension_human x t).1 hx with rfl
  exact Or.inl rfl

theorem majorTrueIn : science.TrueIn majorPremise := by
  constructor
  · exact Or.inl rfl
  · intro t
    exact majorHoldsAt t

theorem minorTrueIn : science.TrueIn minorPremise := by
  constructor
  · exact Or.inr <| Or.inl rfl
  · intro t
    exact minorHoldsAt t

theorem conclusionTrueIn : science.TrueIn conclusion := by
  constructor
  · exact Or.inr <| Or.inr rfl
  · intro t
    exact conclusionHoldsAt t

def TracksOnly (c : Categorical) : Prop :=
  trackedTerm c.subject ∧ trackedTerm c.predicate

instance tracksOnlyDecidable (c : Categorical) : Decidable (TracksOnly c) := by
  unfold TracksOnly
  infer_instance

theorem tracked_of_admitted {c : Categorical} (h : science.admits c) :
    TracksOnly c := by
  rcases h with h | h | h
  · subst h
    decide
  · subst h
    decide
  · subst h
    decide

theorem deduce_preserves_tracked
    {premises : List Categorical} {conclusion : Categorical}
    (hPremises : ∀ {premise : Categorical}, premise ∈ premises → TracksOnly premise)
    (h : Deduce premises conclusion) :
    TracksOnly conclusion := by
  cases h with
  | Assumption c =>
      exact hPremises (by simp)
  | ConvertE S P =>
      rcases hPremises (premise := Categorical.E S P) (by simp) with ⟨hS, hP⟩
      exact ⟨hP, hS⟩
  | ConvertI S P =>
      rcases hPremises (premise := Categorical.I S P) (by simp) with ⟨hS, hP⟩
      exact ⟨hP, hS⟩
  | Barbara S M P =>
      rcases hPremises (premise := Categorical.A M P) (by simp) with ⟨hM, hP⟩
      rcases hPremises (premise := Categorical.A S M) (by simp) with ⟨hS, _⟩
      exact ⟨hS, hP⟩
  | Celarent S M P =>
      rcases hPremises (premise := Categorical.E M P) (by simp) with ⟨hM, hP⟩
      rcases hPremises (premise := Categorical.A S M) (by simp) with ⟨hS, _⟩
      exact ⟨hS, hP⟩
  | Cesare S M P =>
      rcases hPremises (premise := Categorical.E P M) (by simp) with ⟨hP, hM⟩
      rcases hPremises (premise := Categorical.A S M) (by simp) with ⟨hS, _⟩
      exact ⟨hS, hP⟩
  | Camestres S M P =>
      rcases hPremises (premise := Categorical.A P M) (by simp) with ⟨hP, hM⟩
      rcases hPremises (premise := Categorical.E S M) (by simp) with ⟨hS, _⟩
      exact ⟨hS, hP⟩

theorem derives_preserves_tracked
    {premises : List Categorical} {conclusion : Categorical}
    (hPremises : PremisesTrueIn science premises)
    (h : Derives premises conclusion) :
    TracksOnly conclusion := by
  have htracked :
      ∀ {premise : Categorical}, premise ∈ premises → TracksOnly premise := by
    intro premise hmem
    exact tracked_of_admitted ((hPremises (premise := premise) hmem).left)
  induction h with
  | premise hmem =>
      exact htracked hmem
  | unary hmajor hstep ih =>
      rename_i major conclusion
      exact deduce_preserves_tracked
        (premises := [major])
        (conclusion := conclusion)
        (by
          intro premise hmem
          have hpremise : premise = major := by
            simpa using hmem
          subst hpremise
          exact ih)
        hstep
  | binary hmajor hminor hstep ihMajor ihMinor =>
      rename_i major minor conclusion
      exact deduce_preserves_tracked
        (premises := [major, minor])
        (conclusion := conclusion)
        (by
          intro premise hmem
          have hpair : premise = major ∨ premise = minor := by
            simpa [List.mem_cons] using hmem
          rcases hpair with rfl | rfl
          · exact ihMajor
          · exact ihMinor)
        hstep

theorem derives_omnitemporal
    {premises : List Categorical} {conclusion' : Categorical}
    (hPremises : PremisesTrueIn science premises)
    (h : Derives premises conclusion') :
    IsOmnitemporal model conclusion' := by
  apply omnitemporal_of_derives (premises := premises) (conclusion := conclusion') ?_ h
  intro premise hmem
  exact (hPremises (premise := premise) hmem).right

theorem not_holdsAt_animal_human (t : Interpretation.Moment ToyModel) :
    ¬ HoldsAt model (Categorical.A animalTerm humanTerm) t := by
  intro h
  have hfidoAnimal : Object.fido ∈ ExtensionAt model animalTerm t := by
    simp
  have hfidoHuman : Object.fido ∈ ExtensionAt model humanTerm t :=
    h Object.fido hfidoAnimal
  simp at hfidoHuman

theorem not_holdsAt_mortal_animal (t : Interpretation.Moment ToyModel) :
    ¬ HoldsAt model (Categorical.A mortalTerm animalTerm) t := by
  intro h
  have hstoneMortal : Object.stone ∈ ExtensionAt model mortalTerm t := by
    simp
  have hstoneAnimal : Object.stone ∈ ExtensionAt model animalTerm t :=
    h Object.stone hstoneMortal
  simp at hstoneAnimal

theorem not_holdsAt_mortal_human (t : Interpretation.Moment ToyModel) :
    ¬ HoldsAt model (Categorical.A mortalTerm humanTerm) t := by
  intro h
  have hstoneMortal : Object.stone ∈ ExtensionAt model mortalTerm t := by
    simp
  have hstoneHuman : Object.stone ∈ ExtensionAt model humanTerm t :=
    h Object.stone hstoneMortal
  simp at hstoneHuman

theorem not_holdsAt_stone_human (t : Interpretation.Moment ToyModel) :
    ¬ HoldsAt model (Categorical.A stoneTerm humanTerm) t := by
  intro h
  have hstoneStone : Object.stone ∈ ExtensionAt model stoneTerm t := by
    simp
  have hstoneHuman : Object.stone ∈ ExtensionAt model humanTerm t :=
    h Object.stone hstoneStone
  simp at hstoneHuman

theorem not_holdsAt_stone_animal (t : Interpretation.Moment ToyModel) :
    ¬ HoldsAt model (Categorical.A stoneTerm animalTerm) t := by
  intro h
  have hstoneStone : Object.stone ∈ ExtensionAt model stoneTerm t := by
    simp
  have hstoneAnimal : Object.stone ∈ ExtensionAt model animalTerm t :=
    h Object.stone hstoneStone
  simp at hstoneAnimal

theorem majorNoNontrivialMiddle :
    NoNontrivialBarbaraMiddle science animalTerm mortalTerm := by
  intro premises middle hPremises _ hminor
  have htrackedMiddle : trackedTerm middle :=
    (derives_preserves_tracked hPremises hminor).right
  have hholds : HoldsAt model (Categorical.A animalTerm middle) () :=
    derives_omnitemporal hPremises hminor ()
  rcases htrackedMiddle with rfl | rfl | rfl
  · exact False.elim (not_holdsAt_animal_human () hholds)
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem minorNoNontrivialMiddle :
    NoNontrivialBarbaraMiddle science humanTerm animalTerm := by
  intro premises middle hPremises hmajor _
  have htrackedMiddle : trackedTerm middle :=
    (derives_preserves_tracked hPremises hmajor).left
  have hholds : HoldsAt model (Categorical.A middle animalTerm) () :=
    derives_omnitemporal hPremises hmajor ()
  rcases htrackedMiddle with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim (not_holdsAt_mortal_animal () hholds)

theorem majorPremise_ne_conclusion : majorPremise ≠ conclusion := by
  decide

theorem minorPremise_ne_conclusion : minorPremise ≠ conclusion := by
  decide

def majorNous : Nous science majorPremise where
  immediate := immediateIn_of_noNontrivialBarbaraMiddle majorTrueIn majorNoNontrivialMiddle

def minorNous : Nous science minorPremise where
  immediate := immediateIn_of_noNontrivialBarbaraMiddle minorTrueIn minorNoNontrivialMiddle

def humanScientificDefinition : ScientificDefinition where
  phrase :=
    { genus := animalTerm
      differentiae := [animalTerm] }

def humanScientificDefinitionIn : ScientificDefinitionIn science humanTerm where
  definition := humanScientificDefinition
  nonempty := by
    simp [humanScientificDefinition, Philosophy.Aristotle.Core.Definition.IsNonempty,
      Philosophy.Aristotle.Core.DefinitionalPhrase.IsNonempty]
  first_principles := by
    intro premise hmem
    have hpremise : premise = minorPremise := by
      simpa
        [ScientificDefinitionStatements, humanScientificDefinition,
          Philosophy.Aristotle.Core.Definition.genus,
          Philosophy.Aristotle.Core.Definition.differentiae,
          minorPremise, figured] using hmem
    subst hpremise
    exact minorNous

def humanAnimalPerSe : PerSePredicationIn science humanTerm animalTerm :=
  .ofGenus humanScientificDefinitionIn

def animalHumanSecondPerSe : SecondPerSePredicationIn science animalTerm humanTerm :=
  .ofPredicateGenus humanScientificDefinitionIn rfl

example : animalTerm ∈ science.subjectMatter :=
  animalHumanSecondPerSe.subject_in_subject_matter

theorem conclusionSingletonTrue : PremisesTrueIn science [conclusion] := by
  intro premise hmem
  have hpremise : premise = conclusion := by
    simpa using hmem
  subst hpremise
  exact conclusionTrueIn

def middleExplains : MiddleExplainsIn science figured.minor figured.middle figured.major where
  middle_in_subject_matter := by
    change trackedTerm animalTerm
    decide
  minor_to_middle_true := minorTrueIn
  middle_to_major_true := majorTrueIn
  middle_distinct_from_minor := animal_ne_human
  middle_distinct_from_major := animal_ne_mortal

def mortalityWhy : WhyQuestion :=
  WhyQuestion.ofConclusion conclusion

example : mortalityWhy.aim = .dioti := by
  rfl

example : AnswersWhyIn science mortalityWhy := by
  refine ⟨figured, ?_, middleExplains.toExplanatorySyllogismIn⟩
  unfold mortalityWhy conclusion figured
  rfl

theorem only_tracked_middle_for_mortality
    {middle : DemoTerm}
    (hmiddle : middle ∈ science.subjectMatter)
    (hexplains : MiddleExplainsIn science humanTerm middle mortalTerm) :
    middle = animalTerm := by
  change trackedTerm middle at hmiddle
  rcases hmiddle with rfl | rfl | rfl
  · exact False.elim (hexplains.middle_distinct_from_minor rfl)
  · rfl
  · exact False.elim (hexplains.middle_distinct_from_major rfl)

def mortalityUniqueMiddle :
    UniqueMiddleIn science humanTerm animalTerm mortalTerm := by
  intro middle hexplains
  exact only_tracked_middle_for_mortality hexplains.middle_in_subject_matter hexplains

def mortalityUniqueExplanatory :
    UniqueExplanatoryMiddleIn science figured :=
  UniqueExplanatoryMiddleIn.of_barbara_uniqueMiddle mortalityUniqueMiddle

def mortalityUniqueCausal :
    UniqueCausalMiddleIn science figured :=
  UniqueCausalMiddleIn.of_barbara_uniqueMiddle mortalityUniqueMiddle

example {candidate : FiguredSyllogism}
    (hmood : candidate.mood = figured.mood)
    (hconclusion : candidate.conclusion = figured.conclusion)
    (hcausal : CausalExplanatorySyllogismIn science candidate) :
    candidate.middle = animalTerm := by
  simpa [figured] using
    UniqueCausalMiddleIn.unique mortalityUniqueCausal hmood hconclusion hcausal

example : ¬ MiddleExplainsIn science humanTerm humanTerm mortalTerm := by
  exact UniqueMiddleIn.not_middleExplains_of_ne mortalityUniqueMiddle (by
    intro h
    exact animal_ne_human h.symm)

theorem not_middleExplains_with_human_as_middle :
    ∀ {subject : DemoTerm}, ¬ MiddleExplainsIn science subject humanTerm mortalTerm := by
  intro subject hexplains
  have htracked : trackedTerm subject :=
    science.subject_mem_of_trueIn hexplains.minorPremise_true
  rcases htracked with rfl | rfl | rfl
  · exact hexplains.middle_distinct_from_minor rfl
  · exact not_holdsAt_animal_human () (hexplains.minorPremise_true.right ())
  · exact not_holdsAt_mortal_human () (hexplains.minorPremise_true.right ())

theorem not_middleExplains_with_mortal_as_middle :
    ∀ {major : DemoTerm}, ¬ MiddleExplainsIn science humanTerm mortalTerm major := by
  intro major hexplains
  have htracked : trackedTerm major :=
    science.predicate_mem_of_trueIn hexplains.majorPremise_true
  rcases htracked with rfl | rfl | rfl
  · exact not_holdsAt_mortal_human () (hexplains.majorPremise_true.right ())
  · exact not_holdsAt_mortal_animal () (hexplains.majorPremise_true.right ())
  · exact hexplains.middle_distinct_from_major rfl

example :
    ∃ next, majorPremise ∈ next ∧ PremiseExpansion [conclusion] next := by
  exact DemonstrativeExpansionIn.exists_premiseExpansion
    (.barbaraMajor middleExplains.toExplanatorySyllogismIn)

example :
    ∃ next, minorPremise ∈ next ∧ Relation.ReflTransGen PremiseExpansion [conclusion] next := by
  exact DemonstrativeExpansionIn.exists_premiseExpansionReachable
    (.barbaraMinor middleExplains.toExplanatorySyllogismIn)

theorem no_expansion_from_conclusion {target : Categorical} :
    ¬ DemonstrativeExpansionIn science conclusion target := by
  intro hexpand
  cases hexpand with
  | @barbaraMajor S M P hexplains =>
      have hmiddle : MiddleExplainsIn science S humanTerm mortalTerm := by
        simpa [figured, conclusion, FiguredSyllogism.majorPremise] using
          ExplanatorySyllogismIn.toMiddleExplains_of_barbara hexplains
      exact not_middleExplains_with_human_as_middle hmiddle
  | @barbaraMinor S M P hexplains =>
      have hmiddle : MiddleExplainsIn science humanTerm mortalTerm P := by
        simpa [figured, conclusion, FiguredSyllogism.minorPremise] using
          ExplanatorySyllogismIn.toMiddleExplains_of_barbara hexplains
      exact not_middleExplains_with_mortal_as_middle hmiddle
  | celarentMinor hexplains =>
      rcases hexplains.major_premise_true.left with h | h | h <;> cases h
  | cesareMinor hexplains =>
      rcases hexplains.major_premise_true.left with h | h | h <;> cases h
  | camestresMajor hexplains =>
      rcases hexplains.minor_premise_true.left with h | h | h <;> cases h

theorem no_return_to_major :
    ¬ ExpansionReachableIn science conclusion majorPremise := by
  intro hreach
  rcases expansionReachableIn_eq_or_step hreach with hEq | ⟨next, hstep, _⟩
  · exact majorPremise_ne_conclusion hEq.symm
  · exact no_expansion_from_conclusion hstep

theorem no_return_to_minor :
    ¬ ExpansionReachableIn science conclusion minorPremise := by
  intro hreach
  rcases expansionReachableIn_eq_or_step hreach with hEq | ⟨next, hstep, _⟩
  · exact minorPremise_ne_conclusion hEq.symm
  · exact no_expansion_from_conclusion hstep

theorem nonreciprocal :
    NonReciprocalIn science [majorPremise, minorPremise] conclusion := by
  refine ⟨conclusionTrueIn, ?_⟩
  intro premise hmem _ hreach
  have hpair : premise = majorPremise ∨ premise = minorPremise := by
    simpa [List.mem_cons] using hmem
  rcases hpair with rfl | rfl
  · exact no_return_to_major hreach
  · exact no_return_to_minor hreach

def causeOfMortality : IsCauseOf science figured where
  perfect := by
    simp [figured, FiguredSyllogism.isPerfect, FiguredSyllogism.figure,
      Mood.figure, Figure.IsPerfect]
  minor_per_se := humanAnimalPerSe
  major_principle := majorNous

def demo : Demonstration ToyModel science where
  figured := figured
  conclusion_admissible := conclusionTrueIn.left
  major_principle := majorNous
  minor_principle := minorNous
  nonreciprocal := nonreciprocal
  explains := middleExplains.toExplanatorySyllogismIn

def causalDemo : CausalDemonstration ToyModel science where
  toDemonstration := demo
  companion_cause := causeOfMortality

example : AnswersWhyThroughCauseIn science mortalityWhy := by
  simpa [CausalDemonstration.whyQuestion, mortalityWhy, demo, figured, conclusion] using
    (causalDemo.answersWhyThroughCause)

def conclusionArt : DialecticalArt where
  acceptedPremises _ := [conclusion]

example : DialecticalSyllogism conclusionArt .many [conclusion] conclusion := by
  constructor
  · intro premise hmem
    simpa [acceptableTo, conclusionArt] using hmem
  · exact Derives.premise (by simp)

theorem not_firstPrinciples_singletonConclusion :
    ¬ FirstPrinciples science [conclusion] := by
  intro hfirst
  have hconclusionNous : Nous science conclusion := hfirst (by simp)
  exact demo.conclusion_not_nous hconclusionNous

example :
    DialecticalSyllogism conclusionArt .many [conclusion] conclusion ∧
      ¬ DemonstrativeBasisIn science [conclusion] conclusion := by
  exact dialecticalSyllogism_without_demonstrativeBasis
    (science := science)
    (art := conclusionArt)
    (respondent := .many)
    (premises := [conclusion])
    (conclusion := conclusion)
    (by
      constructor
      · intro premise hmem
        simpa [acceptableTo, conclusionArt] using hmem
      · exact Derives.premise (by simp))
    not_firstPrinciples_singletonConclusion

theorem majorPremise_ne_minorPremise : majorPremise ≠ minorPremise := by
  decide

theorem no_binary_deduce_from_majorPremise_twice
    {candidate : Categorical} :
    ¬ Deduce [majorPremise, majorPremise] candidate := by
  suffices
      ∀ {premises : List Categorical} {candidate : Categorical},
        Deduce premises candidate → premises = [majorPremise, majorPremise] → False by
    intro h
    exact this h rfl
  intro premises candidate h
  cases h with
  | Assumption c =>
      intro hpremises
      simp at hpremises
  | ConvertE S P =>
      intro hpremises
      simp at hpremises
  | ConvertI S P =>
      intro hpremises
      simp at hpremises
  | Barbara S M P =>
      intro hpremises
      injection hpremises with hmajor htail
      injection htail with hminor hnil
      injection hmajor with hManimal hPmortal
      injection hminor with hSanimal hMmortal
      exact animal_ne_mortal (hManimal.symm.trans hMmortal)
  | Celarent S M P =>
      intro hpremises
      injection hpremises with hfirst htail
      cases hfirst
  | Cesare S M P =>
      intro hpremises
      injection hpremises with hfirst htail
      cases hfirst
  | Camestres S M P =>
      intro hpremises
      injection hpremises with hfirst htail
      injection htail with hsecond hnil
      cases hsecond

theorem no_binary_deduce_from_minorPremise_twice
    {candidate : Categorical} :
    ¬ Deduce [minorPremise, minorPremise] candidate := by
  suffices
      ∀ {premises : List Categorical} {candidate : Categorical},
        Deduce premises candidate → premises = [minorPremise, minorPremise] → False by
    intro h
    exact this h rfl
  intro premises candidate h
  cases h with
  | Assumption c =>
      intro hpremises
      simp at hpremises
  | ConvertE S P =>
      intro hpremises
      simp at hpremises
  | ConvertI S P =>
      intro hpremises
      simp at hpremises
  | Barbara S M P =>
      intro hpremises
      injection hpremises with hmajor htail
      injection htail with hminor hnil
      injection hmajor with hMhuman hPanimal
      injection hminor with hShuman hManimal
      exact human_ne_animal (hMhuman.symm.trans hManimal)
  | Celarent S M P =>
      intro hpremises
      injection hpremises with hfirst htail
      cases hfirst
  | Cesare S M P =>
      intro hpremises
      injection hpremises with hfirst htail
      cases hfirst
  | Camestres S M P =>
      intro hpremises
      injection hpremises with hfirst htail
      injection htail with hsecond hnil
      cases hsecond

theorem derives_from_majorPremise_alone_eq_major
    {candidate : Categorical}
    (h : Derives [majorPremise] candidate) :
    candidate = majorPremise := by
  induction h with
  | premise hmem =>
      simpa using hmem
  | unary hmajor hstep ih =>
      rename_i major conclusion
      have hmajorEq : major = majorPremise := ih
      subst hmajorEq
      cases hstep with
      | Assumption _ =>
          rfl
  | binary hmajor hminor hstep ihMajor ihMinor =>
      rename_i major minor conclusion
      have hmajorEq : major = majorPremise := ihMajor
      have hminorEq : minor = majorPremise := ihMinor
      subst hmajorEq
      subst hminorEq
      exact False.elim (no_binary_deduce_from_majorPremise_twice hstep)

theorem derives_from_minorPremise_alone_eq_minor
    {candidate : Categorical}
    (h : Derives [minorPremise] candidate) :
    candidate = minorPremise := by
  induction h with
  | premise hmem =>
      simpa using hmem
  | unary hmajor hstep ih =>
      rename_i major conclusion
      have hmajorEq : major = minorPremise := ih
      subst hmajorEq
      cases hstep with
      | Assumption _ =>
          rfl
  | binary hmajor hminor hstep ihMajor ihMinor =>
      rename_i major minor conclusion
      have hmajorEq : major = minorPremise := ihMajor
      have hminorEq : minor = minorPremise := ihMinor
      subst hmajorEq
      subst hminorEq
      exact False.elim (no_binary_deduce_from_minorPremise_twice hstep)

theorem not_derives_conclusion_from_majorPremise_alone :
    ¬ Derives [majorPremise] conclusion := by
  intro h
  exact majorPremise_ne_conclusion (derives_from_majorPremise_alone_eq_major h).symm

theorem not_derives_conclusion_from_minorPremise_alone :
    ¬ Derives [minorPremise] conclusion := by
  intro h
  exact minorPremise_ne_conclusion (derives_from_minorPremise_alone_eq_minor h).symm

def negativeTrackedTerm (term : DemoTerm) : Prop :=
  term = humanTerm ∨ term = animalTerm ∨ term = stoneTerm

instance negativeTrackedTermDecidable (term : DemoTerm) :
    Decidable (negativeTrackedTerm term) := by
  unfold negativeTrackedTerm
  infer_instance

def celarentFigured : FiguredSyllogism :=
  { minor := humanTerm
    middle := animalTerm
    major := stoneTerm
    mood := .celarent }

def celarentMajorPremise : Categorical := celarentFigured.majorPremise
def celarentMinorPremise : Categorical := celarentFigured.minorPremise
def celarentConclusion : Categorical := celarentFigured.conclusion

def celarentScience : Science ToyModel model where
  subjectMatter := negativeTrackedTerm
  admits proposition :=
    proposition = celarentMajorPremise ∨
      proposition = celarentMinorPremise ∨
        proposition = celarentConclusion
  admits_subject := by
    intro proposition hadmits
    rcases hadmits with h | h | h
    · subst h
      change negativeTrackedTerm celarentMajorPremise.subject
      decide
    · subst h
      change negativeTrackedTerm celarentMinorPremise.subject
      decide
    · subst h
      change negativeTrackedTerm celarentConclusion.subject
      decide
  admits_predicate := by
    intro proposition hadmits
    rcases hadmits with h | h | h
    · subst h
      change negativeTrackedTerm celarentMajorPremise.predicate
      decide
    · subst h
      change negativeTrackedTerm celarentMinorPremise.predicate
      decide
    · subst h
      change negativeTrackedTerm celarentConclusion.predicate
      decide

def NegativeTracksOnly (c : Categorical) : Prop :=
  negativeTrackedTerm c.subject ∧ negativeTrackedTerm c.predicate

instance negativeTracksOnlyDecidable (c : Categorical) : Decidable (NegativeTracksOnly c) := by
  unfold NegativeTracksOnly
  infer_instance

theorem negativeTracked_of_admitted {c : Categorical} (h : celarentScience.admits c) :
    NegativeTracksOnly c := by
  rcases h with h | h | h
  · subst h
    decide
  · subst h
    decide
  · subst h
    decide

theorem deduce_preserves_negativeTracked
    {premises : List Categorical} {conclusion : Categorical}
    (hPremises : ∀ {premise : Categorical}, premise ∈ premises → NegativeTracksOnly premise)
    (h : Deduce premises conclusion) :
    NegativeTracksOnly conclusion := by
  cases h with
  | Assumption c =>
      exact hPremises (by simp)
  | ConvertE S P =>
      rcases hPremises (premise := Categorical.E S P) (by simp) with ⟨hS, hP⟩
      exact ⟨hP, hS⟩
  | ConvertI S P =>
      rcases hPremises (premise := Categorical.I S P) (by simp) with ⟨hS, hP⟩
      exact ⟨hP, hS⟩
  | Barbara S M P =>
      rcases hPremises (premise := Categorical.A M P) (by simp) with ⟨hM, hP⟩
      rcases hPremises (premise := Categorical.A S M) (by simp) with ⟨hS, _⟩
      exact ⟨hS, hP⟩
  | Celarent S M P =>
      rcases hPremises (premise := Categorical.E M P) (by simp) with ⟨hM, hP⟩
      rcases hPremises (premise := Categorical.A S M) (by simp) with ⟨hS, _⟩
      exact ⟨hS, hP⟩
  | Cesare S M P =>
      rcases hPremises (premise := Categorical.E P M) (by simp) with ⟨hP, hM⟩
      rcases hPremises (premise := Categorical.A S M) (by simp) with ⟨hS, _⟩
      exact ⟨hS, hP⟩
  | Camestres S M P =>
      rcases hPremises (premise := Categorical.A P M) (by simp) with ⟨hP, hM⟩
      rcases hPremises (premise := Categorical.E S M) (by simp) with ⟨hS, _⟩
      exact ⟨hS, hP⟩

theorem derives_preserves_negativeTracked_of
    {science' : Science ToyModel model}
    (hTrackedOfAdmitted : ∀ {c : Categorical}, science'.admits c → NegativeTracksOnly c)
    {premises : List Categorical} {conclusion : Categorical}
    (hPremises : PremisesTrueIn science' premises)
    (h : Derives premises conclusion) :
    NegativeTracksOnly conclusion := by
  have htracked :
      ∀ {premise : Categorical}, premise ∈ premises → NegativeTracksOnly premise := by
    intro premise hmem
    exact hTrackedOfAdmitted ((hPremises (premise := premise) hmem).left)
  induction h with
  | premise hmem =>
      exact htracked hmem
  | unary hmajor hstep ih =>
      rename_i major conclusion
      exact deduce_preserves_negativeTracked
        (premises := [major])
        (conclusion := conclusion)
        (by
          intro premise hmem
          have hpremise : premise = major := by
            simpa using hmem
          subst hpremise
          exact ih)
        hstep
  | binary hmajor hminor hstep ihMajor ihMinor =>
      rename_i major minor conclusion
      exact deduce_preserves_negativeTracked
        (premises := [major, minor])
        (conclusion := conclusion)
        (by
          intro premise hmem
          have hpair : premise = major ∨ premise = minor := by
            simpa [List.mem_cons] using hmem
          rcases hpair with rfl | rfl
          · exact ihMajor
          · exact ihMinor)
        hstep

theorem derives_preserves_negativeTracked
    {premises : List Categorical} {conclusion : Categorical}
    (hPremises : PremisesTrueIn celarentScience premises)
    (h : Derives premises conclusion) :
    NegativeTracksOnly conclusion :=
  derives_preserves_negativeTracked_of
    (science' := celarentScience)
    (fun {_} h => negativeTracked_of_admitted h)
    hPremises
    h

theorem celarentMajorHoldsAt (t : Interpretation.Moment ToyModel) :
    HoldsAt model celarentMajorPremise t := by
  intro x hxAnimal hxStone
  rcases (mem_extension_animal x t).1 hxAnimal with rfl | rfl
  · have : Object.socrates = Object.stone := (mem_extension_stone Object.socrates t).1 hxStone
    cases this
  · have : Object.fido = Object.stone := (mem_extension_stone Object.fido t).1 hxStone
    cases this

theorem celarentMinorHoldsAt (t : Interpretation.Moment ToyModel) :
    HoldsAt model celarentMinorPremise t := by
  simpa [celarentMinorPremise, minorPremise] using minorHoldsAt t

theorem celarentConclusionHoldsAt (t : Interpretation.Moment ToyModel) :
    HoldsAt model celarentConclusion t := by
  intro x hxHuman hxStone
  rcases (mem_extension_human x t).1 hxHuman with rfl
  have : Object.socrates = Object.stone := (mem_extension_stone Object.socrates t).1 hxStone
  cases this

theorem celarentMajorTrueIn : celarentScience.TrueIn celarentMajorPremise := by
  constructor
  · exact Or.inl rfl
  · intro t
    exact celarentMajorHoldsAt t

theorem celarentMinorTrueIn : celarentScience.TrueIn celarentMinorPremise := by
  constructor
  · exact Or.inr <| Or.inl rfl
  · intro t
    exact celarentMinorHoldsAt t

theorem celarentConclusionTrueIn : celarentScience.TrueIn celarentConclusion := by
  constructor
  · exact Or.inr <| Or.inr rfl
  · intro t
    exact celarentConclusionHoldsAt t

theorem celarentMajorPremise_ne_conclusion : celarentMajorPremise ≠ celarentConclusion := by
  decide

theorem celarentMinorPremise_ne_conclusion : celarentMinorPremise ≠ celarentConclusion := by
  decide

def celarentExplains : ExplanatorySyllogismIn celarentScience celarentFigured where
  middle_in_subject_matter := by
    change negativeTrackedTerm animalTerm
    decide
  major_premise_true := celarentMajorTrueIn
  minor_premise_true := celarentMinorTrueIn
  middle_distinct_from_minor := animal_ne_human
  middle_distinct_from_major := animal_ne_stone

def humanityNotStoneWhy : WhyQuestion :=
  WhyQuestion.ofConclusion celarentConclusion

example : humanityNotStoneWhy.aim = .dioti := by
  rfl

example : humanityNotStoneWhy.conclusion = celarentConclusion := by
  unfold humanityNotStoneWhy celarentConclusion celarentFigured
  rfl

example : AnswersWhyIn celarentScience humanityNotStoneWhy := by
  refine ⟨celarentFigured, ?_, celarentExplains⟩
  unfold humanityNotStoneWhy celarentConclusion celarentFigured
  rfl

theorem no_expansion_from_celarentConclusion {target : Categorical} :
    ¬ DemonstrativeExpansionIn celarentScience celarentConclusion target := by
  intro hexpand
  cases hexpand with
  | celarentMajor hexplains =>
      rcases hexplains.minor_premise_true.left with h | h | h
      · cases h
      · injection h with hsubject hpredicate
        exact animal_ne_human hpredicate.symm
      · cases h
  | cesareMajor hexplains =>
      rcases hexplains.minor_premise_true.left with h | h | h
      · cases h
      · injection h with hsubject hpredicate
        exact animal_ne_stone hpredicate.symm
      · cases h
  | camestresMinor hexplains =>
      rcases hexplains.major_premise_true.left with h | h | h
      · cases h
      · injection h with hsubject hpredicate
        exact animal_ne_stone hpredicate.symm
      · cases h

theorem no_return_to_celarentMajor :
    ¬ ExpansionReachableIn celarentScience celarentConclusion celarentMajorPremise := by
  intro hreach
  rcases expansionReachableIn_eq_or_step hreach with hEq | ⟨next, hstep, _⟩
  · exact celarentMajorPremise_ne_conclusion hEq.symm
  · exact no_expansion_from_celarentConclusion hstep

theorem no_return_to_celarentMinor :
    ¬ ExpansionReachableIn celarentScience celarentConclusion celarentMinorPremise := by
  intro hreach
  rcases expansionReachableIn_eq_or_step hreach with hEq | ⟨next, hstep, _⟩
  · exact celarentMinorPremise_ne_conclusion hEq.symm
  · exact no_expansion_from_celarentConclusion hstep

theorem celarentNonreciprocal :
    NonReciprocalIn celarentScience
      [celarentMajorPremise, celarentMinorPremise] celarentConclusion := by
  refine ⟨celarentConclusionTrueIn, ?_⟩
  intro premise hmem _ hreach
  have hpair : premise = celarentMajorPremise ∨ premise = celarentMinorPremise := by
    simpa [List.mem_cons] using hmem
  rcases hpair with rfl | rfl
  · exact no_return_to_celarentMajor hreach
  · exact no_return_to_celarentMinor hreach

example :
    NonReciprocalIn celarentScience
      [celarentMajorPremise, celarentMinorPremise] celarentConclusion :=
  celarentNonreciprocal

theorem celarentMajorNoNontrivialCelarentMiddle :
    NoNontrivialCelarentMiddle celarentScience animalTerm stoneTerm := by
  intro premises middle hPremises _ hminor
  have htrackedMiddle : negativeTrackedTerm middle :=
    (derives_preserves_negativeTracked hPremises hminor).right
  have hholds : HoldsAt model (Categorical.A animalTerm middle) () :=
    (omnitemporal_of_derives
      (m := model)
      (premises := premises)
      (conclusion := Categorical.A animalTerm middle)
      (fun {_} hmem => (hPremises hmem).right)
      hminor) ()
  rcases htrackedMiddle with rfl | rfl | rfl
  · exact False.elim (not_holdsAt_animal_human () hholds)
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem celarentMajorNoNontrivialCesareMiddle :
    NoNontrivialCesareMiddle celarentScience animalTerm stoneTerm := by
  intro premises middle hPremises _ hminor
  have htrackedMiddle : negativeTrackedTerm middle :=
    (derives_preserves_negativeTracked hPremises hminor).right
  have hholds : HoldsAt model (Categorical.A animalTerm middle) () :=
    (omnitemporal_of_derives
      (m := model)
      (premises := premises)
      (conclusion := Categorical.A animalTerm middle)
      (fun {_} hmem => (hPremises hmem).right)
      hminor) ()
  rcases htrackedMiddle with rfl | rfl | rfl
  · exact False.elim (not_holdsAt_animal_human () hholds)
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem celarentMajorNoNontrivialCamestresMiddle :
    NoNontrivialCamestresMiddle celarentScience animalTerm stoneTerm := by
  intro premises middle hPremises hmajor _
  have htrackedMiddle : negativeTrackedTerm middle :=
    (derives_preserves_negativeTracked hPremises hmajor).right
  have hholds : HoldsAt model (Categorical.A stoneTerm middle) () :=
    (omnitemporal_of_derives
      (m := model)
      (premises := premises)
      (conclusion := Categorical.A stoneTerm middle)
      (fun {_} hmem => (hPremises hmem).right)
      hmajor) ()
  rcases htrackedMiddle with rfl | rfl | rfl
  · exact False.elim (not_holdsAt_stone_human () hholds)
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem celarentMinorNoNontrivialMiddle :
    NoNontrivialBarbaraMiddle celarentScience humanTerm animalTerm := by
  intro premises middle hPremises hmajor _
  have htrackedMiddle : negativeTrackedTerm middle :=
    (derives_preserves_negativeTracked hPremises hmajor).left
  have hholds : HoldsAt model (Categorical.A middle animalTerm) () :=
    (omnitemporal_of_derives
      (m := model)
      (premises := premises)
      (conclusion := Categorical.A middle animalTerm)
      (fun {_} hmem => (hPremises hmem).right)
      hmajor) ()
  rcases htrackedMiddle with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim (not_holdsAt_stone_animal () hholds)

def celarentMajorNous : Nous celarentScience celarentMajorPremise where
  immediate :=
    immediateIn_of_noNontrivialNegativeMiddle
      celarentMajorTrueIn
      celarentMajorNoNontrivialCelarentMiddle
      celarentMajorNoNontrivialCesareMiddle
      celarentMajorNoNontrivialCamestresMiddle

def celarentMinorNous : Nous celarentScience celarentMinorPremise where
  immediate :=
    immediateIn_of_noNontrivialBarbaraMiddle
      celarentMinorTrueIn
      celarentMinorNoNontrivialMiddle

def humanScientificDefinitionInCelarent :
    ScientificDefinitionIn celarentScience humanTerm where
  definition := humanScientificDefinition
  nonempty := by
    simp [humanScientificDefinition, Philosophy.Aristotle.Core.Definition.IsNonempty,
      Philosophy.Aristotle.Core.DefinitionalPhrase.IsNonempty]
  first_principles := by
    intro premise hmem
    have hpremise : premise = celarentMinorPremise := by
      simpa
        [ScientificDefinitionStatements, humanScientificDefinition,
          Philosophy.Aristotle.Core.Definition.genus,
          Philosophy.Aristotle.Core.Definition.differentiae,
          celarentMinorPremise, celarentFigured] using hmem
    subst hpremise
    exact celarentMinorNous

def humanAnimalPerSeInCelarent :
    PerSePredicationIn celarentScience humanTerm animalTerm :=
  .ofGenus humanScientificDefinitionInCelarent

def celarentDemo : Demonstration ToyModel celarentScience where
  figured := celarentFigured
  conclusion_admissible := celarentConclusionTrueIn.left
  major_principle := celarentMajorNous
  minor_principle := celarentMinorNous
  nonreciprocal := celarentNonreciprocal
  explains := celarentExplains

example :
    DemonstrativeBasisIn celarentScience
      [celarentMajorPremise, celarentMinorPremise] celarentConclusion :=
  celarentDemo.basis

def causeOfHumanityNotStone : IsCauseOf celarentScience celarentFigured where
  perfect := by
    simp [celarentFigured, FiguredSyllogism.isPerfect, FiguredSyllogism.figure,
      Mood.figure, Figure.IsPerfect]
  minor_per_se := humanAnimalPerSeInCelarent
  major_principle := celarentMajorNous

def causalCelarentDemo : CausalDemonstration ToyModel celarentScience where
  toDemonstration := celarentDemo
  companion_cause := causeOfHumanityNotStone

example : AnswersWhyThroughCauseIn celarentScience humanityNotStoneWhy := by
  simpa
      [CausalDemonstration.whyQuestion, humanityNotStoneWhy,
        celarentDemo, celarentFigured, celarentConclusion] using
    (causalCelarentDemo.answersWhyThroughCause)

def cesareFigured : FiguredSyllogism :=
  { minor := humanTerm
    middle := animalTerm
    major := stoneTerm
    mood := .cesare }

def cesareCompanion : FiguredSyllogism :=
  cesareFigured.firstFigureCompanion

def cesareCompanionMajorPremise : Categorical := cesareCompanion.majorPremise
def cesareMajorPremise : Categorical := cesareFigured.majorPremise
def cesareMinorPremise : Categorical := cesareFigured.minorPremise
def cesareConclusion : Categorical := cesareFigured.conclusion

def cesareScience : Science ToyModel model where
  subjectMatter := negativeTrackedTerm
  admits proposition :=
    proposition = cesareCompanionMajorPremise ∨
      proposition = cesareMajorPremise ∨
        proposition = cesareMinorPremise ∨ proposition = cesareConclusion
  admits_subject := by
    intro proposition hadmits
    rcases hadmits with h | h | h | h
    · subst h
      change negativeTrackedTerm cesareCompanionMajorPremise.subject
      decide
    · subst h
      change negativeTrackedTerm cesareMajorPremise.subject
      decide
    · subst h
      change negativeTrackedTerm cesareMinorPremise.subject
      decide
    · subst h
      change negativeTrackedTerm cesareConclusion.subject
      decide
  admits_predicate := by
    intro proposition hadmits
    rcases hadmits with h | h | h | h
    · subst h
      change negativeTrackedTerm cesareCompanionMajorPremise.predicate
      decide
    · subst h
      change negativeTrackedTerm cesareMajorPremise.predicate
      decide
    · subst h
      change negativeTrackedTerm cesareMinorPremise.predicate
      decide
    · subst h
      change negativeTrackedTerm cesareConclusion.predicate
      decide

theorem cesareCompanionMajorHoldsAt (t : Interpretation.Moment ToyModel) :
    HoldsAt model cesareCompanionMajorPremise t := by
  simpa [cesareCompanion, cesareCompanionMajorPremise, cesareFigured,
    celarentMajorPremise, celarentFigured] using celarentMajorHoldsAt t

theorem cesareMajorHoldsAt (t : Interpretation.Moment ToyModel) :
    HoldsAt model cesareMajorPremise t := by
  intro x hxStone hxAnimal
  rcases (mem_extension_stone x t).1 hxStone with rfl
  rcases (mem_extension_animal Object.stone t).1 hxAnimal with h | h <;> cases h

theorem cesareMinorHoldsAt (t : Interpretation.Moment ToyModel) :
    HoldsAt model cesareMinorPremise t := by
  simpa [cesareMinorPremise, cesareFigured, celarentMinorPremise, celarentFigured] using
    celarentMinorHoldsAt t

theorem cesareConclusionHoldsAt (t : Interpretation.Moment ToyModel) :
    HoldsAt model cesareConclusion t := by
  simpa [cesareConclusion, cesareFigured, celarentConclusion, celarentFigured] using
    celarentConclusionHoldsAt t

theorem cesareCompanionMajorTrueIn : cesareScience.TrueIn cesareCompanionMajorPremise := by
  constructor
  · exact Or.inl rfl
  · intro t
    exact cesareCompanionMajorHoldsAt t

theorem cesareMajorTrueIn : cesareScience.TrueIn cesareMajorPremise := by
  constructor
  · exact Or.inr <| Or.inl rfl
  · intro t
    exact cesareMajorHoldsAt t

theorem cesareMinorTrueIn : cesareScience.TrueIn cesareMinorPremise := by
  constructor
  · exact Or.inr <| Or.inr <| Or.inl rfl
  · intro t
    exact cesareMinorHoldsAt t

theorem cesareConclusionTrueIn : cesareScience.TrueIn cesareConclusion := by
  constructor
  · exact Or.inr <| Or.inr <| Or.inr rfl
  · intro t
    exact cesareConclusionHoldsAt t

theorem cesareNegativeTracked_of_admitted {c : Categorical} (h : cesareScience.admits c) :
    NegativeTracksOnly c := by
  rcases h with h | h | h | h
  · subst h
    decide
  · subst h
    decide
  · subst h
    decide
  · subst h
    decide

theorem cesareDerivesPreservesNegativeTracked
    {premises : List Categorical} {conclusion' : Categorical}
    (hPremises : PremisesTrueIn cesareScience premises)
    (h : Derives premises conclusion') :
    NegativeTracksOnly conclusion' :=
  derives_preserves_negativeTracked_of
    (science' := cesareScience)
    (fun {_} h => cesareNegativeTracked_of_admitted h)
    hPremises
    h

def cesareExplains : ExplanatorySyllogismIn cesareScience cesareFigured where
  middle_in_subject_matter := by
    change negativeTrackedTerm animalTerm
    decide
  major_premise_true := cesareMajorTrueIn
  minor_premise_true := cesareMinorTrueIn
  middle_distinct_from_minor := animal_ne_human
  middle_distinct_from_major := animal_ne_stone

def cesareWhy : WhyQuestion :=
  WhyQuestion.ofConclusion cesareConclusion

example : cesareWhy.conclusion = cesareConclusion := by
  unfold cesareWhy cesareConclusion cesareFigured
  rfl

theorem cesareCompanionMajorNoNontrivialCelarentMiddle :
    NoNontrivialCelarentMiddle cesareScience animalTerm stoneTerm := by
  intro premises middle hPremises _ hminor
  have htrackedMiddle : negativeTrackedTerm middle :=
    (cesareDerivesPreservesNegativeTracked hPremises hminor).right
  have hholds : HoldsAt model (Categorical.A animalTerm middle) () :=
    (omnitemporal_of_derives
      (m := model)
      (premises := premises)
      (conclusion := Categorical.A animalTerm middle)
      (fun {_} hmem => (hPremises hmem).right)
      hminor) ()
  rcases htrackedMiddle with rfl | rfl | rfl
  · exact False.elim (not_holdsAt_animal_human () hholds)
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem cesareCompanionMajorNoNontrivialCesareMiddle :
    NoNontrivialCesareMiddle cesareScience animalTerm stoneTerm := by
  intro premises middle hPremises _ hminor
  have htrackedMiddle : negativeTrackedTerm middle :=
    (cesareDerivesPreservesNegativeTracked hPremises hminor).right
  have hholds : HoldsAt model (Categorical.A animalTerm middle) () :=
    (omnitemporal_of_derives
      (m := model)
      (premises := premises)
      (conclusion := Categorical.A animalTerm middle)
      (fun {_} hmem => (hPremises hmem).right)
      hminor) ()
  rcases htrackedMiddle with rfl | rfl | rfl
  · exact False.elim (not_holdsAt_animal_human () hholds)
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem cesareCompanionMajorNoNontrivialCamestresMiddle :
    NoNontrivialCamestresMiddle cesareScience animalTerm stoneTerm := by
  intro premises middle hPremises hmajor _
  have htrackedMiddle : negativeTrackedTerm middle :=
    (cesareDerivesPreservesNegativeTracked hPremises hmajor).right
  have hholds : HoldsAt model (Categorical.A stoneTerm middle) () :=
    (omnitemporal_of_derives
      (m := model)
      (premises := premises)
      (conclusion := Categorical.A stoneTerm middle)
      (fun {_} hmem => (hPremises hmem).right)
      hmajor) ()
  rcases htrackedMiddle with rfl | rfl | rfl
  · exact False.elim (not_holdsAt_stone_human () hholds)
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem cesareMinorNoNontrivialMiddle :
    NoNontrivialBarbaraMiddle cesareScience humanTerm animalTerm := by
  intro premises middle hPremises hmajor _
  have htrackedMiddle : negativeTrackedTerm middle :=
    (cesareDerivesPreservesNegativeTracked hPremises hmajor).left
  have hholds : HoldsAt model (Categorical.A middle animalTerm) () :=
    (omnitemporal_of_derives
      (m := model)
      (premises := premises)
      (conclusion := Categorical.A middle animalTerm)
      (fun {_} hmem => (hPremises hmem).right)
      hmajor) ()
  rcases htrackedMiddle with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim (not_holdsAt_stone_animal () hholds)

def cesareCompanionMajorNous : Nous cesareScience cesareCompanionMajorPremise where
  immediate :=
    immediateIn_of_noNontrivialNegativeMiddle
      cesareCompanionMajorTrueIn
      cesareCompanionMajorNoNontrivialCelarentMiddle
      cesareCompanionMajorNoNontrivialCesareMiddle
      cesareCompanionMajorNoNontrivialCamestresMiddle

def cesareMinorNous : Nous cesareScience cesareMinorPremise where
  immediate :=
    immediateIn_of_noNontrivialBarbaraMiddle
      cesareMinorTrueIn
      cesareMinorNoNontrivialMiddle

def humanScientificDefinitionInCesare :
    ScientificDefinitionIn cesareScience humanTerm where
  definition := humanScientificDefinition
  nonempty := by
    simp [humanScientificDefinition, Philosophy.Aristotle.Core.Definition.IsNonempty,
      Philosophy.Aristotle.Core.DefinitionalPhrase.IsNonempty]
  first_principles := by
    intro premise hmem
    have hpremise : premise = cesareMinorPremise := by
      simpa
        [ScientificDefinitionStatements, humanScientificDefinition,
          Philosophy.Aristotle.Core.Definition.genus,
          Philosophy.Aristotle.Core.Definition.differentiae,
          cesareMinorPremise, cesareFigured] using hmem
    subst hpremise
    exact cesareMinorNous

def humanAnimalPerSeInCesare :
    PerSePredicationIn cesareScience humanTerm animalTerm :=
  .ofGenus humanScientificDefinitionInCesare

def animalHumanSecondPerSeInCesare :
    SecondPerSePredicationIn cesareScience animalTerm humanTerm :=
  .ofPredicateGenus humanScientificDefinitionInCesare rfl

def cesareCause : IsCauseOf cesareScience cesareFigured.firstFigureCompanion where
  perfect := firstFigureCompanion_isPerfect cesareFigured
  minor_per_se := humanAnimalPerSeInCesare
  major_principle := cesareCompanionMajorNous

def cesareCompanionRoute : CompanionCausalRouteIn cesareScience cesareFigured where
  second_per_se := animalHumanSecondPerSeInCesare
  companion_cause := cesareCause

example : cesareFigured.firstFigureCompanion.middle ∈ cesareScience.subjectMatter :=
  cesareCompanionRoute.middle_in_subject_matter

example : cesareFigured.firstFigureCompanion.minor ∈ cesareScience.subjectMatter :=
  cesareCompanionRoute.companionMinor_in_subject_matter

def cesareCausalExplanation :
    CausalExplanatorySyllogismIn cesareScience cesareFigured :=
  cesareCompanionRoute.toCausalExplanatorySyllogismIn cesareExplains

example :
    CompanionCausalRouteIn cesareScience cesareFigured :=
  CompanionCausalRouteIn.cesare_of_causalExplanatorySyllogismIn
    cesareCausalExplanation
    animalHumanSecondPerSeInCesare

example : AnswersWhyThroughCauseIn cesareScience cesareWhy := by
  simpa [cesareWhy, cesareConclusion] using
    CompanionCausalRouteIn.cesare_answersWhyThroughCompanionRoute
      (h := cesareCompanionRoute)
      cesareExplains

example : ¬ ImmediateIn celarentScience celarentConclusion :=
  celarentDemo.conclusion_not_immediate

example : ¬ Nous celarentScience celarentConclusion :=
  celarentDemo.conclusion_not_nous

def demoIrredundant :
    PremiseIrredundantIn science [majorPremise, minorPremise] conclusion := by
  intro premise hmem
  have hpair : premise = majorPremise ∨ premise = minorPremise := by
    simpa [List.mem_cons] using hmem
  rcases hpair with rfl | rfl
  · intro hsupport
    have hderives : Derives [minorPremise] conclusion := by
      simpa [majorPremise_ne_minorPremise] using hsupport.2
    exact not_derives_conclusion_from_minorPremise_alone hderives
  · intro hsupport
    have hderives : Derives [majorPremise] conclusion := by
      simpa [majorPremise_ne_minorPremise] using hsupport.2
    exact not_derives_conclusion_from_majorPremise_alone hderives

def demoMinimalBasis :
    MinimalDemonstrativeBasisIn science [majorPremise, minorPremise] conclusion :=
  demo.minimalBasis demoIrredundant

example : DemonstrativeBasisIn science [majorPremise, minorPremise] conclusion :=
  demo.basis

example : MinimalDemonstrativeBasisIn science [majorPremise, minorPremise] conclusion :=
  demoMinimalBasis

def trivialFigured : FiguredSyllogism :=
  { minor := humanTerm
    middle := animalTerm
    major := animalTerm
    mood := .barbara }

def trivialMajorPremise : Categorical := trivialFigured.majorPremise
def trivialMinorPremise : Categorical := trivialFigured.minorPremise
def trivialConclusion : Categorical := trivialFigured.conclusion

theorem not_explains_trivial :
    ¬ ExplanatorySyllogismIn science trivialFigured := by
  intro hexplains
  exact hexplains.middle_distinct_from_major rfl

example : IsOmnitemporal model demo.conclusion :=
  demo.conclusion_omnitemporal

example : ¬ Nous science demo.conclusion :=
  demo.conclusion_not_nous

example : Derives [trivialMajorPremise, trivialMinorPremise] trivialConclusion :=
  figuredSyllogism_derives trivialFigured

example :
    ¬ NonReciprocalIn science [trivialMajorPremise, trivialMinorPremise] trivialConclusion := by
  intro h
  have hnoncircular :
      NonCircular science [trivialMajorPremise, trivialMinorPremise] trivialConclusion :=
    NonReciprocalIn.noncircular h
  have hmem : trivialConclusion ∈ [trivialMajorPremise, trivialMinorPremise] := by
    have hsame : trivialConclusion = trivialMinorPremise := by
      rfl
    simp [hsame]
  exact hnoncircular.right hmem

example : ¬ ∃ d : Demonstration ToyModel science, d.figured = trivialFigured := by
  rintro ⟨d, hd⟩
  cases d with
  | mk figured conclusion_admissible major_principle minor_principle
      nonreciprocal explains =>
      dsimp at hd
      cases hd
      exact not_explains_trivial explains

end Aristotle.Examples.Demonstration
