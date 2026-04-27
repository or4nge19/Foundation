import Philosophy.Aristotle.DeInterpretatione

namespace Aristotle.Examples.DeInterpretatione

open Aristotle.DeInterpretatione

def socrates : Term := Philosophy.Aristotle.Core.Term.ofWords ["Socrates"]
def human : Term := Philosophy.Aristotle.Core.Term.ofWords ["human"]
def white : Term := Philosophy.Aristotle.Core.Term.ofWords ["white"]

def singularAffirmation : Assertion :=
  { subject := socrates
    predicate := white
    quantity := .singular
    quality := .affirmative }

def indefiniteAffirmation : Assertion :=
  { subject := human
    predicate := white
    quantity := .indefinite
    quality := .affirmative }

def notWhiteSingular : Assertion :=
  { subject := socrates
    predicate := TermOccurrence.negated white
    quantity := .singular
    quality := .affirmative }

def manyAsOneSubject : Assertion :=
  { subject := TermOccurrence.manyAsOne human [white] (some "white man")
    predicate := white
    quantity := .singular
    quality := .affirmative }

def futureContingentSingular : Assertion :=
  { subject := socrates
    predicate := white
    quantity := .singular
    quality := .affirmative
    temporalStatus := TemporalStatus.futureContingent }

example :
    singularAffirmation.contradictory =
      { subject := socrates
        predicate := white
        quantity := .singular
        quality := .negative } := by
  rfl

example : singularAffirmation.IsRCPRegular := by
  simp [Assertion.IsRCPRegular, Assertion.rcpExceptions,
    Assertion.IsFutureContingentSingular, singularAffirmation]

example : ¬ indefiniteAffirmation.IsRCPRegular := by
  simp [Assertion.IsRCPRegular, Assertion.rcpExceptions,
    Assertion.IsFutureContingentSingular, indefiniteAffirmation]

example :
    indefiniteAffirmation.rcpExceptions = [RCPException.indefiniteCanBothBeTrue] := by
  simp [Assertion.rcpExceptions, Assertion.IsFutureContingentSingular,
    indefiniteAffirmation]

example : notWhiteSingular.HasNegatedTerm := by
  simp [Assertion.HasNegatedTerm, notWhiteSingular, TermOccurrence.IsNegated]

example : notWhiteSingular.toCategorical? = none := by
  rfl

example : ¬ manyAsOneSubject.IsRCPRegular := by
  simp [Assertion.IsRCPRegular, Assertion.rcpExceptions,
    Assertion.IsFutureContingentSingular, manyAsOneSubject,
    TermOccurrence.IsManyAsOne]

example :
    manyAsOneSubject.rcpExceptions = [RCPException.subjectManyAsOne] := by
  simp [Assertion.rcpExceptions, Assertion.IsFutureContingentSingular,
    manyAsOneSubject, TermOccurrence.IsManyAsOne]

example :
    RCPException.effect RCPException.subjectManyAsOne =
      RCPExceptionEffect.chapter8Open := by
  rfl

example : ¬ futureContingentSingular.IsRCPRegular := by
  simp [Assertion.IsRCPRegular, Assertion.rcpExceptions,
    Assertion.IsFutureContingentSingular, futureContingentSingular]

example :
    futureContingentSingular.rcpExceptions =
      [RCPException.futureContingentTruthValueGap] := by
  simp [Assertion.rcpExceptions, Assertion.IsFutureContingentSingular,
    futureContingentSingular]

example :
    RCPException.effect RCPException.futureContingentTruthValueGap =
      RCPExceptionEffect.neitherTrueNorFalsePossible := by
  rfl

example :
    Categorical.ofAssertion? (Categorical.A human white).toAssertion =
      some (Categorical.A human white) := by
  simp

example :
    (Categorical.A human white).contradictory.toAssertion =
      (Categorical.A human white).toAssertion.contradictory := by
  rfl

end Aristotle.Examples.DeInterpretatione
