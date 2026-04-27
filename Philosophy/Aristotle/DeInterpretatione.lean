import Philosophy.Aristotle.Categories

namespace Aristotle.DeInterpretatione

open Aristotle.Categories

/-!
# De Interpretatione: Assertoric Statements

`Philosophy/Aristotle/Aristotle.md` places `De Interpretatione` with the
background knowledge needed for dialectic rather than as a mere preface to
syllogistic. The Weidemann/Whitaker reconstruction in
`Philosophy/Aristotle/H. Weidemann - De Interpretationae.md` sharpens that
point: the treatise studies statement-making sentences as members of
contradictory pairs.

This first tranche does not attempt the whole treatise. It introduces the
assertoric statement layer that sits between `Categories` and the later
`PriorAnalytics` restriction to universal/particular categorical forms.
-/

abbrev Term := Aristotle.Categories.Term

inductive TemporalStatus
  | nonfuture
  | futureSettled
  | futureContingent
  deriving DecidableEq, Repr, Inhabited

/--
How a term is being used inside an assertion.

- `simple`: an ordinary term
- `negated`: a negated term, needed for `DI` 10
- `manyAsOne`: several things misleadingly taken as one unit, the `DI` 8 case
-/
inductive TermOccurrence
  | simple (term : Term)
  | negated (term : Term)
  | manyAsOne (first : Term) (rest : List Term) (renderedAs : Option String := none)
  deriving DecidableEq, Repr, Inhabited

instance : Coe Term TermOccurrence where
  coe := .simple

namespace TermOccurrence

def terms : TermOccurrence → List Term
  | .simple term => [term]
  | .negated term => [term]
  | .manyAsOne first rest _ => first :: rest

def IsNegated : TermOccurrence → Prop
  | .negated _ => True
  | _ => False

def IsManyAsOne : TermOccurrence → Prop
  | .manyAsOne .. => True
  | _ => False

@[simp] theorem isNegated_simple (term : Term) :
    ¬ (.simple term : TermOccurrence).IsNegated := by
  simp [IsNegated]

@[simp] theorem isNegated_manyAsOne (first : Term) (rest : List Term)
    (renderedAs : Option String) :
    ¬ (TermOccurrence.manyAsOne first rest renderedAs).IsNegated := by
  simp [IsNegated]

@[simp] theorem isManyAsOne_simple (term : Term) :
    ¬ (.simple term : TermOccurrence).IsManyAsOne := by
  simp [IsManyAsOne]

@[simp] theorem isManyAsOne_negated (term : Term) :
    ¬ (TermOccurrence.negated term).IsManyAsOne := by
  simp [IsManyAsOne]

instance instDecidableIsNegated (occurrence : TermOccurrence) :
    Decidable occurrence.IsNegated := by
  cases occurrence with
  | simple term =>
      exact isFalse (by simp [IsNegated])
  | negated term =>
      exact isTrue (by simp [IsNegated])
  | manyAsOne first rest renderedAs =>
      exact isFalse (by simp [IsNegated])

instance instDecidableIsManyAsOne (occurrence : TermOccurrence) :
    Decidable occurrence.IsManyAsOne := by
  cases occurrence with
  | simple term =>
      exact isFalse (by simp [IsManyAsOne])
  | negated term =>
      exact isFalse (by simp [IsManyAsOne])
  | manyAsOne first rest renderedAs =>
      exact isTrue (by simp [IsManyAsOne])

/--
No `TermOccurrence` is both negated in the *DI* 10 sense and “many as one” in
the *DI* 8 sense: the predicates are **disjoint** on the inductive family.
Weidemann/Whitaker treat these as different ways *statement* structure can
specialize; the formal `TermOccurrence` type keeps them in separate
constructors, so a joint classification is impossible.
-/
theorem not_isNegated_and_isManyAsOne (o : TermOccurrence) : ¬ (o.IsNegated ∧ o.IsManyAsOne) := by
  intro ⟨hneg, hmany⟩
  cases o <;> simp [IsNegated, IsManyAsOne] at hneg hmany

end TermOccurrence

inductive AssertionQuantity
  | singular
  | universal
  | particular
  | indefinite
  deriving DecidableEq, Repr, Inhabited

inductive CategoricalQuantity
  | universal
  | particular
  deriving DecidableEq, Repr, Inhabited

namespace CategoricalQuantity

def toAssertionQuantity : CategoricalQuantity → AssertionQuantity
  | .universal => .universal
  | .particular => .particular

end CategoricalQuantity

inductive Quality
  | affirmative
  | negative
  deriving DecidableEq, Repr, Inhabited

namespace Quality

def contradictory : Quality → Quality
  | .affirmative => .negative
  | .negative => .affirmative

@[simp] theorem contradictory_contradictory (quality : Quality) :
    quality.contradictory.contradictory = quality := by
  cases quality <;> rfl

end Quality

namespace AssertionQuantity

def contradictory : AssertionQuantity → AssertionQuantity
  | .singular => .singular
  | .universal => .particular
  | .particular => .universal
  | .indefinite => .indefinite

@[simp] theorem contradictory_contradictory (quantity : AssertionQuantity) :
    quantity.contradictory.contradictory = quantity := by
  cases quantity <;> rfl

end AssertionQuantity

structure Assertion where
  subject : TermOccurrence
  predicate : TermOccurrence
  quantity : AssertionQuantity
  quality : Quality
  temporalStatus : TemporalStatus := .nonfuture
  deriving DecidableEq, Repr, Inhabited

inductive RCPException
  | indefiniteCanBothBeTrue
  | subjectManyAsOne
  | predicateManyAsOne
  | futureContingentTruthValueGap
  deriving DecidableEq, Repr, Inhabited

inductive RCPExceptionEffect
  | bothTruePossible
  | chapter8Open
  | neitherTrueNorFalsePossible
  deriving DecidableEq, Repr, Inhabited

namespace RCPException

def effect : RCPException → RCPExceptionEffect
  | .indefiniteCanBothBeTrue => .bothTruePossible
  | .subjectManyAsOne => .chapter8Open
  | .predicateManyAsOne => .chapter8Open
  | .futureContingentTruthValueGap => .neitherTrueNorFalsePossible

end RCPException

namespace Assertion

def contradictory (statement : Assertion) : Assertion :=
  { statement with
    quantity := statement.quantity.contradictory
    quality := statement.quality.contradictory }

@[simp] theorem subject_contradictory (statement : Assertion) :
    statement.contradictory.subject = statement.subject := by
  rfl

@[simp] theorem predicate_contradictory (statement : Assertion) :
    statement.contradictory.predicate = statement.predicate := by
  rfl

@[simp] theorem quantity_contradictory (statement : Assertion) :
    statement.contradictory.quantity = statement.quantity.contradictory := by
  rfl

@[simp] theorem quality_contradictory (statement : Assertion) :
    statement.contradictory.quality = statement.quality.contradictory := by
  rfl

@[simp] theorem temporalStatus_contradictory (statement : Assertion) :
    statement.contradictory.temporalStatus = statement.temporalStatus := by
  rfl

@[simp] theorem contradictory_involutive (statement : Assertion) :
    statement.contradictory.contradictory = statement := by
  cases statement
  simp [contradictory]

/--
Current `DI` 7-10 exception-tracking:

- indefinite statements may have both members true
- chapter 8 many-as-one statements are outside ordinary simple assertion
- singular future contingents may lack truth-value

Modal `DI` 12-13 refinements still remain pending.
-/
def HasNegatedTerm (statement : Assertion) : Prop :=
  statement.subject.IsNegated ∨ statement.predicate.IsNegated

def UsesManyAsOne (statement : Assertion) : Prop :=
  statement.subject.IsManyAsOne ∨ statement.predicate.IsManyAsOne

def IsFutureContingentSingular (statement : Assertion) : Prop :=
  statement.quantity = .singular ∧ statement.temporalStatus = .futureContingent

instance instDecidableHasNegatedTerm (statement : Assertion) :
    Decidable statement.HasNegatedTerm := by
  unfold HasNegatedTerm
  infer_instance

instance instDecidableUsesManyAsOne (statement : Assertion) :
    Decidable statement.UsesManyAsOne := by
  unfold UsesManyAsOne
  infer_instance

instance instDecidableIsFutureContingentSingular (statement : Assertion) :
    Decidable statement.IsFutureContingentSingular := by
  unfold IsFutureContingentSingular
  infer_instance

def rcpExceptions (statement : Assertion) : List RCPException :=
  (if statement.subject.IsManyAsOne then [RCPException.subjectManyAsOne] else []) ++
    (if statement.predicate.IsManyAsOne then [RCPException.predicateManyAsOne] else []) ++
    (if statement.IsFutureContingentSingular then [RCPException.futureContingentTruthValueGap] else []) ++
    (if statement.quantity = .indefinite then [RCPException.indefiniteCanBothBeTrue] else [])

def IsRCPRegular (statement : Assertion) : Prop :=
  statement.rcpExceptions = []

instance instDecidableIsRCPRegular (statement : Assertion) :
    Decidable statement.IsRCPRegular := by
  unfold IsRCPRegular
  infer_instance

@[simp] theorem hasNegatedTerm_contradictory_iff (statement : Assertion) :
    statement.HasNegatedTerm ↔ statement.contradictory.HasNegatedTerm := by
  simp [HasNegatedTerm, contradictory]

@[simp] theorem usesManyAsOne_contradictory_iff (statement : Assertion) :
    statement.UsesManyAsOne ↔ statement.contradictory.UsesManyAsOne := by
  simp [UsesManyAsOne, contradictory]

theorem isFutureContingentSingular_contradictory_iff (statement : Assertion) :
    statement.IsFutureContingentSingular ↔ statement.contradictory.IsFutureContingentSingular := by
  cases statement with
  | mk subject predicate quantity quality temporalStatus =>
      cases quantity <;> cases temporalStatus <;>
        simp [IsFutureContingentSingular, contradictory, AssertionQuantity.contradictory]

@[simp] theorem rcpExceptions_contradictory (statement : Assertion) :
    statement.contradictory.rcpExceptions = statement.rcpExceptions := by
  cases statement with
  | mk subject predicate quantity quality temporalStatus =>
      cases quantity <;> cases subject <;> cases predicate <;> cases temporalStatus <;>
        simp [rcpExceptions, contradictory, IsFutureContingentSingular,
          AssertionQuantity.contradictory]

@[simp] theorem isRCPRegular_contradictory_iff (statement : Assertion) :
    statement.IsRCPRegular ↔ statement.contradictory.IsRCPRegular := by
  simp [IsRCPRegular]

def Contradicts (left right : Assertion) : Prop :=
  left.contradictory = right

theorem contradicts_symm {left right : Assertion} (h : left.Contradicts right) :
    right.Contradicts left := by
  unfold Contradicts at h ⊢
  have h' := congrArg contradictory h
  simpa [contradictory_involutive] using h'.symm

end Assertion

/--
The universal/particular assertoric fragment extracted by the later
syllogistic.
-/
inductive Categorical
  | A (S P : Term)
  | E (S P : Term)
  | I (S P : Term)
  | O (S P : Term)
  deriving DecidableEq, Repr, Inhabited

namespace Categorical

def subject : Categorical → Term
  | .A S _ => S
  | .E S _ => S
  | .I S _ => S
  | .O S _ => S

def predicate : Categorical → Term
  | .A _ P => P
  | .E _ P => P
  | .I _ P => P
  | .O _ P => P

def quantity : Categorical → CategoricalQuantity
  | .A _ _ => .universal
  | .E _ _ => .universal
  | .I _ _ => .particular
  | .O _ _ => .particular

def quality : Categorical → Quality
  | .A _ _ => .affirmative
  | .I _ _ => .affirmative
  | .E _ _ => .negative
  | .O _ _ => .negative

def toAssertion : Categorical → Assertion
  | .A S P =>
      { subject := .simple S
        predicate := .simple P
        quantity := .universal
        quality := .affirmative }
  | .E S P =>
      { subject := .simple S
        predicate := .simple P
        quantity := .universal
        quality := .negative }
  | .I S P =>
      { subject := .simple S
        predicate := .simple P
        quantity := .particular
        quality := .affirmative }
  | .O S P =>
      { subject := .simple S
        predicate := .simple P
        quantity := .particular
        quality := .negative }

def ofAssertion? : Assertion → Option Categorical
  | ⟨.simple S, .simple P, .universal, .affirmative, .nonfuture⟩ => some (.A S P)
  | ⟨.simple S, .simple P, .universal, .negative, .nonfuture⟩ => some (.E S P)
  | ⟨.simple S, .simple P, .particular, .affirmative, .nonfuture⟩ => some (.I S P)
  | ⟨.simple S, .simple P, .particular, .negative, .nonfuture⟩ => some (.O S P)
  | _ => none

@[simp] theorem ofAssertion?_toAssertion (statement : Categorical) :
    ofAssertion? statement.toAssertion = some statement := by
  cases statement <;> rfl

def contradictory : Categorical → Categorical
  | .A S P => .O S P
  | .E S P => .I S P
  | .I S P => .E S P
  | .O S P => .A S P

@[simp] theorem contradictory_involutive (statement : Categorical) :
    statement.contradictory.contradictory = statement := by
  cases statement <;> rfl

@[simp] theorem toAssertion_isRCPRegular (statement : Categorical) :
    statement.toAssertion.IsRCPRegular := by
  cases statement <;>
    simp [Assertion.IsRCPRegular, Assertion.rcpExceptions,
      Assertion.IsFutureContingentSingular, toAssertion]

theorem contradictory_toAssertion (statement : Categorical) :
    statement.contradictory.toAssertion = statement.toAssertion.contradictory := by
  cases statement <;> rfl

end Categorical

namespace Assertion

def toCategorical? : Assertion → Option Categorical :=
  Categorical.ofAssertion?

@[simp] theorem toCategorical?_toAssertion (statement : Categorical) :
    statement.toAssertion.toCategorical? = some statement := by
  exact Categorical.ofAssertion?_toAssertion statement

end Assertion

end Aristotle.DeInterpretatione
