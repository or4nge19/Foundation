import Mathlib

namespace Philosophy.Aristotle.Core

/-!
# Shared Aristotle Core

This module provides the single kernel for the Aristotle development. The key
distinctions are:

- `Lexis`: the spoken or written expression
- `Signified`: the item picked out by an expression
- `Logos`: the account under which it is signified

`Philosophy/Aristotle/Aristotle.md` supplies the general guide here: the same
materials must support dialectic, analytics, first philosophy, and physics
without being redefined separately in each discipline. So this file fixes the
shared vocabulary while remaining neutral between dialectical and scientific
uses that are distinguished only downstream.
-/

abbrev Token := String

def tokenize (text : String) : List Token :=
  (text.splitOn " ").filter fun token => token ≠ ""

structure Lexis where
  tokens : List Token
  deriving DecidableEq, Repr, Inhabited

namespace Lexis

@[simp] def singleton (token : Token) : Lexis :=
  ⟨[token]⟩

@[simp] def ofWords (tokens : List Token) : Lexis :=
  ⟨tokens⟩

def ofString (text : String) : Lexis :=
  ⟨tokenize text⟩

def render (lexis : Lexis) : String :=
  String.intercalate " " lexis.tokens

def WithoutCombination (lexis : Lexis) : Prop :=
  lexis.tokens.length ≤ 1

instance : ToString Lexis where
  toString := Lexis.render

end Lexis

structure Logos where
  tokens : List Token
  deriving DecidableEq, Repr, Inhabited

namespace Logos

@[simp] def ofWords (tokens : List Token) : Logos :=
  ⟨tokens⟩

def ofString (text : String) : Logos :=
  ⟨tokenize text⟩

def render (logos : Logos) : String :=
  String.intercalate " " logos.tokens

instance : ToString Logos where
  toString := Logos.render

end Logos

structure Signified where
  tokens : List Token
  deriving DecidableEq, Repr, Inhabited

namespace Signified

@[simp] def ofWords (tokens : List Token) : Signified :=
  ⟨tokens⟩

def ofString (text : String) : Signified :=
  ⟨tokenize text⟩

def render (signified : Signified) : String :=
  String.intercalate " " signified.tokens

instance : ToString Signified where
  toString := Signified.render

end Signified

structure Term where
  lexis : Lexis
  deriving DecidableEq, Repr, Inhabited

namespace Term

@[simp] def ofWords (tokens : List Token) : Term :=
  ⟨Lexis.ofWords tokens⟩

def ofString (text : String) : Term :=
  ⟨Lexis.ofString text⟩

def words (term : Term) : List Token :=
  term.lexis.tokens

def name (term : Term) : String :=
  term.lexis.render

end Term

inductive Expression
  | simple (term : Term)
  | combined (parts : List Lexis)
  deriving DecidableEq, Repr, Inhabited

namespace Expression

def IsSimple : Expression → Prop
  | .simple _ => True
  | .combined _ => False

def renderedText : Expression → String
  | .simple term => term.name
  | .combined parts => String.intercalate " " (parts.map Lexis.render)

end Expression

/--
`DefinitionalPhrase` keeps genus and differentiae structured rather than
collapsing a proposed definition into a single combined term.

Following Menn's general guide, dialectical definition-testing must come before
scientific completion. So this object is intentionally neutral between weaker
dialectical and stronger scientific uses. Downstream modules add the screening,
categorial, and explanatory conditions appropriate to each.
-/
structure DefinitionalPhrase where
  genus : Term
  differentiae : List Term
  lexicalForm : Option Lexis := none
  renderedAs : Option String := none
  deriving DecidableEq, Repr, Inhabited

namespace DefinitionalPhrase

def terms (phrase : DefinitionalPhrase) : List Term :=
  phrase.genus :: phrase.differentiae

def IsNonempty (phrase : DefinitionalPhrase) : Prop :=
  phrase.differentiae ≠ []

def lexicalParts (phrase : DefinitionalPhrase) : List Lexis :=
  match phrase.lexicalForm with
  | some lexis => [lexis]
  | none => phrase.terms.map Term.lexis

def renderedText (phrase : DefinitionalPhrase) : String :=
  match phrase.renderedAs with
  | some text => text
  | none =>
      match phrase.lexicalForm with
      | some lexis => lexis.render
      | none => String.intercalate " " (phrase.terms.map Term.name)

def asExpression (phrase : DefinitionalPhrase) : Expression :=
  .combined phrase.lexicalParts

def meaning {B : Type} [SemilatticeInf B]
    (interpret : Term → B) (phrase : DefinitionalPhrase) : B :=
  phrase.differentiae.foldl (fun acc differentia => acc ⊓ interpret differentia)
    (interpret phrase.genus)

theorem terms_ne_nil (phrase : DefinitionalPhrase) : phrase.terms ≠ [] := by
  simp [terms]

end DefinitionalPhrase

/--
`DefinitionKind` records the governing Aristotelian split:

- dialectical definition tests and orients inquiry
- scientific definition belongs to demonstration and explanatory science

The current codebase uses this first as a marker so later modules can separate
the two without collapsing them back together.
-/
inductive DefinitionKind
  | dialectical
  | scientific
  deriving DecidableEq, Repr, Inhabited

/--
`DefinitionalPhrase` is the shared raw material. `Definition kind` marks that
same articulated phrase as being used under a definite Aristotelian regime:

- dialectically, as a candidate account to be screened and tested
- scientifically, as a definition belonging to explanatory science

This lets downstream modules carry the split in their types without duplicating
the underlying genus-plus-differentiae syntax.
-/
structure Definition (kind : DefinitionKind) where
  phrase : DefinitionalPhrase
  deriving DecidableEq, Repr

abbrev DialecticalDefinition := Definition .dialectical
abbrev ScientificDefinition := Definition .scientific

namespace Definition

variable {kind : DefinitionKind}

def genus (definition : Definition kind) : Term :=
  definition.phrase.genus

def differentiae (definition : Definition kind) : List Term :=
  definition.phrase.differentiae

def lexicalForm (definition : Definition kind) : Option Lexis :=
  definition.phrase.lexicalForm

def renderedAs (definition : Definition kind) : Option String :=
  definition.phrase.renderedAs

def terms (definition : Definition kind) : List Term :=
  definition.phrase.terms

def IsNonempty (definition : Definition kind) : Prop :=
  definition.phrase.IsNonempty

def renderedText (definition : Definition kind) : String :=
  definition.phrase.renderedText

def asExpression (definition : Definition kind) : Expression :=
  definition.phrase.asExpression

def meaning {B : Type} [SemilatticeInf B]
    (interpret : Term → B) (definition : Definition kind) : B :=
  definition.phrase.meaning interpret

theorem terms_ne_nil (definition : Definition kind) : definition.terms ≠ [] := by
  simpa [terms] using DefinitionalPhrase.terms_ne_nil definition.phrase

theorem isNonempty_iff (definition : Definition kind) :
    definition.IsNonempty ↔ definition.differentiae ≠ [] := by
  rfl

end Definition

namespace DefinitionalPhrase

def asDefinition (phrase : DefinitionalPhrase) (kind : DefinitionKind) : Definition kind :=
  ⟨phrase⟩

def asDialecticalDefinition (phrase : DefinitionalPhrase) : DialecticalDefinition :=
  phrase.asDefinition .dialectical

def asScientificDefinition (phrase : DefinitionalPhrase) : ScientificDefinition :=
  phrase.asDefinition .scientific

@[simp] theorem asDefinition_phrase (phrase : DefinitionalPhrase) (kind : DefinitionKind) :
    (phrase.asDefinition kind).phrase = phrase := by
  rfl

@[simp] theorem asDialecticalDefinition_phrase (phrase : DefinitionalPhrase) :
    phrase.asDialecticalDefinition.phrase = phrase := by
  rfl

@[simp] theorem asScientificDefinition_phrase (phrase : DefinitionalPhrase) :
    phrase.asScientificDefinition.phrase = phrase := by
  rfl

end DefinitionalPhrase

inductive Predicable
  | definition
  | genus
  | proprium
  | accident
  deriving DecidableEq, Repr, Inhabited

namespace Predicable

abbrev idion : Predicable := .proprium

end Predicable

inductive Category
  | substance
  | quantity
  | quality
  | relation
  | place
  | time
  | position
  | state
  | action
  | affection
  deriving DecidableEq, Repr, Inhabited

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

inductive OppositionKind
  | relative
  | contrary
  | possessionPrivation
  | affirmationNegation
  deriving DecidableEq, Repr, Inhabited

inductive SubjectRelation
  | saidOf
  | inSubject
  deriving DecidableEq, Repr, Inhabited

namespace SubjectRelation

abbrev kathHupokeimenou : SubjectRelation := .saidOf
abbrev enHupokeimenōi : SubjectRelation := .inSubject

end SubjectRelation

inductive Accidentality
  | perAccidens
  | perSe
  deriving DecidableEq, Repr, Inhabited

inductive ActualityStatus
  | potential
  | actual
  deriving DecidableEq, Repr, Inhabited

inductive TruthStatus
  | worldly
  | affectionOfThought
  deriving DecidableEq, Repr, Inhabited

/--
`InquiryAim` marks the Aristotelian contrast between questions asking

- `hoti`: whether something is so
- `dioti`: why it is so

The dialectical layer will stay on the `hoti` side; explanatory science will
make the `dioti` side explicit.
-/
inductive InquiryAim
  | hoti
  | dioti
  deriving DecidableEq, Repr, Inhabited

class Signification (W B L : Type) where
  signifies_as : W → B → L → Prop

def signifiesAs {W B L : Type} [Signification W B L] : W → B → L → Prop :=
  Signification.signifies_as

def signifies {W B L : Type} [Signification W B L] (w : W) (b : B) : Prop :=
  ∃ l : L, signifiesAs w b l

def AreSynonymous {W B L : Type} [Signification W B L]
    (w : W) (b₁ b₂ : B) : Prop :=
  ∃ l : L, signifiesAs w b₁ l ∧ signifiesAs w b₂ l

def AreHomonymous {W B L : Type} [Signification W B L]
    (w : W) (b₁ b₂ : B) : Prop :=
  ∃ l₁ l₂ : L, signifiesAs w b₁ l₁ ∧ signifiesAs w b₂ l₂ ∧ l₁ ≠ l₂

class Morphology (W : Type) extends Quiver W where
  [thin : Quiver.IsThin W]

attribute [instance] Morphology.thin

def Morphology.derives_from {W : Type} [Morphology W] (derived root : W) : Prop :=
  Nonempty (derived ⟶ root)

def IsParonymous {W B L : Type} [Signification W B L] [Morphology W]
    (derived root : W) (bDerived bRoot : B) : Prop :=
  Morphology.derives_from derived root ∧
    ∃ lDerived lRoot : L,
      signifiesAs derived bDerived lDerived ∧
        signifiesAs root bRoot lRoot ∧
          lDerived ≠ lRoot

namespace Signification

variable {W B L : Type} [Signification W B L]

theorem synonyms_symm {w : W} {b₁ b₂ : B}
    (h : AreSynonymous (L := L) w b₁ b₂) :
    AreSynonymous (L := L) w b₂ b₁ := by
  rcases h with ⟨l, hb₁, hb₂⟩
  exact ⟨l, hb₂, hb₁⟩

theorem homonymous_symm {w : W} {b₁ b₂ : B}
    (h : AreHomonymous (L := L) w b₁ b₂) :
    AreHomonymous (L := L) w b₂ b₁ := by
  rcases h with ⟨l₁, l₂, hb₁, hb₂, hne⟩
  exact ⟨l₂, l₁, hb₂, hb₁, Ne.symm hne⟩

end Signification

class DialecticalHierarchy (B : Type) extends PartialOrder B

def isCategoryHead {B : Type} [DialecticalHierarchy B] (b : B) : Prop :=
  IsMax b

class Predication (B : Type) extends DialecticalHierarchy B where
  said_of : B → B → Prop
  in_subject : B → B → Prop
  genus_of : B → B → Prop := fun g s => s < g
  species_of : B → B → Prop := fun sp s => s < sp
  differentia_of : B → B → Prop
  proprium_of : B → B → Prop
  accident_of : B → B → Prop
  falls_under : B → Category → Prop
  genus_iff_lt : ∀ {g s : B}, genus_of g s ↔ s < g
  species_iff_lt : ∀ {sp s : B}, species_of sp s ↔ s < sp
  order_implies_said_of : ∀ {universal particular : B}, particular < universal → said_of universal particular
  differentia_implies_said_of : ∀ {d s : B}, differentia_of d s → said_of d s

def is_universal_substance {B : Type} [Predication B] (b : B) : Prop :=
  (∃ s, Predication.said_of b s) ∧ ¬ ∃ s, Predication.in_subject b s

def is_particular_accident {B : Type} [Predication B] (b : B) : Prop :=
  ¬ (∃ s, Predication.said_of b s) ∧ ∃ s, Predication.in_subject b s

def is_universal_accident {B : Type} [Predication B] (b : B) : Prop :=
  (∃ s, Predication.said_of b s) ∧ ∃ s, Predication.in_subject b s

def is_particular_substance {B : Type} [Predication B] (b : B) : Prop :=
  ¬ (∃ s, Predication.said_of b s) ∧ ¬ ∃ s, Predication.in_subject b s

namespace Predication

variable {B : Type} [Predication B]

theorem genus_implies_said_of {g s : B} (h : Predication.genus_of g s) :
    Predication.said_of g s := by
  exact Predication.order_implies_said_of ((Predication.genus_iff_lt).1 h)

theorem species_implies_said_of {sp s : B} (h : Predication.species_of sp s) :
    Predication.said_of sp s := by
  exact Predication.order_implies_said_of ((Predication.species_iff_lt).1 h)

theorem universalSubstance_not_particularAccident (b : B) :
    is_universal_substance b → ¬ is_particular_accident b := by
  rintro ⟨hsaid, _⟩ ⟨hnot, _⟩
  exact hnot hsaid

theorem universalAccident_not_particularSubstance (b : B) :
    is_universal_accident b → ¬ is_particular_substance b := by
  rintro ⟨hsaid, _⟩ ⟨hnot, _⟩
  exact hnot hsaid

theorem particularSubstance_not_particularAccident (b : B) :
    is_particular_substance b → ¬ is_particular_accident b := by
  rintro ⟨_, hnotIn⟩ ⟨_, hin⟩
  exact hnotIn hin

end Predication

class Essence (B L : Type) where
  essence_of : L → B → Prop
  per_se : B → B → Prop
  per_accidens : B → B → Prop

class Causality (B : Type) where
  material_cause : B → B → Prop
  formal_cause : B → B → Prop
  efficient_cause : B → B → Prop
  final_cause : B → B → Prop
  explains : B → Prop → Prop
  cause_guarantees_fact : ∀ {c : B} {P : Prop}, explains c P → P

class Physics (B : Type) extends Causality B where
  has_internal_principle_of_motion : B → Prop
  is_inseparable_from_matter : B → Prop

class FirstPhilosophy (B : Type) extends Causality B where
  is_primary_ousia : B → Prop
  is_separate_in_formula : B → Prop
  is_separate_in_existence : B → Prop

end Philosophy.Aristotle.Core
