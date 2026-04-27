import Philosophy.Aristotle.Core

namespace Philosophy.Aristotle

open Philosophy.Aristotle.Core

/-!
# Aristotle Prelude

`Basic` is now a lightweight compatibility layer over `Core`. The real
foundational definitions live in `Philosophy.Aristotle.Core`; this module keeps
older imports stable while exposing a few generic epistemic helpers.
-/

abbrev Token := Core.Token
abbrev Lexis := Core.Lexis
abbrev Logos := Core.Logos
abbrev Signified := Core.Signified
abbrev Term := Core.Term
abbrev Expression := Core.Expression
abbrev Predicable := Core.Predicable
abbrev Category := Core.Category
abbrev OppositionKind := Core.OppositionKind
abbrev SubjectRelation := Core.SubjectRelation
abbrev Accidentality := Core.Accidentality
abbrev ActualityStatus := Core.ActualityStatus
abbrev TruthStatus := Core.TruthStatus
abbrev InquiryAim := Core.InquiryAim

abbrev Signification := Core.Signification
abbrev Morphology := Core.Morphology
abbrev DialecticalHierarchy := Core.DialecticalHierarchy
abbrev Predication := Core.Predication
abbrev Essence := Core.Essence
abbrev Causality := Core.Causality
abbrev Physics := Core.Physics
abbrev FirstPhilosophy := Core.FirstPhilosophy

abbrev tokenize := Core.tokenize
abbrev signifiesAs := @Core.signifiesAs
abbrev signifies := @Core.signifies
abbrev AreSynonymous := @Core.AreSynonymous
abbrev AreHomonymous := @Core.AreHomonymous
abbrev IsParonymous := @Core.IsParonymous
abbrev isCategoryHead := @Core.isCategoryHead

abbrev is_universal_substance := @Core.is_universal_substance
abbrev is_particular_accident := @Core.is_particular_accident
abbrev is_universal_accident := @Core.is_universal_accident
abbrev is_particular_substance := @Core.is_particular_substance

namespace Lexis

abbrev singleton := Core.Lexis.singleton
abbrev ofWords := Core.Lexis.ofWords
abbrev ofString := Core.Lexis.ofString
abbrev render := Core.Lexis.render
abbrev WithoutCombination := Core.Lexis.WithoutCombination

end Lexis

namespace Logos

abbrev ofWords := Core.Logos.ofWords
abbrev ofString := Core.Logos.ofString
abbrev render := Core.Logos.render

end Logos

namespace Signified

abbrev ofWords := Core.Signified.ofWords
abbrev ofString := Core.Signified.ofString
abbrev render := Core.Signified.render

end Signified

namespace Term

abbrev ofWords := Core.Term.ofWords
abbrev ofString := Core.Term.ofString
abbrev words := Core.Term.words
abbrev name := Core.Term.name

end Term

structure Episteme (B : Type) [Causality B] (P : Prop) : Type where
  hoti : P
  cause : B
  dioti : Causality.explains cause P

def investigates_substance_causes {B : Type} [FirstPhilosophy B] (entity : B) : Prop :=
  ∃ form : B,
    Causality.formal_cause form entity ∧
      FirstPhilosophy.is_primary_ousia form ∧
        FirstPhilosophy.is_separate_in_formula form

def investigates_unmoved_mover {B : Type} [FirstPhilosophy B] (cosmos : B) : Prop :=
  ∃ nous : B,
    Causality.final_cause nous cosmos ∧
      FirstPhilosophy.is_separate_in_existence nous ∧
        ∀ b : B, ¬ Causality.efficient_cause b nous

def demonstrate_with_cause {B : Type} [Causality B]
    (cause : B) {P : Prop} (h : Causality.explains cause P) : Episteme B P :=
  { hoti := Causality.cause_guarantees_fact h
    cause := cause
    dioti := h }

end Philosophy.Aristotle
