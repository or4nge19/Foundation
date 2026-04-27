import Philosophy.Aristotle.PriorAnalytics

namespace Aristotle.PosteriorAnalytics

open Aristotle.PriorAnalytics

/-!
# Term-Extensional Semantics

Truth for categorical propositions is derived from the extensions of their terms
across an interpretation-relative temporal index, rather than being assigned
proposition-by-proposition. This makes
the semantic layer suitable for Smith-style chain arguments.
-/

class Interpretation (Model : Type) where
  Subject : Type
  Moment : Type
  extension : Model → Term → Moment → Set Subject

def ExtensionAt {Model : Type} [Interpretation Model]
    (m : Model) (term : Term) (t : Interpretation.Moment Model) :
    Set (Interpretation.Subject Model) :=
  Interpretation.extension m term t

def HoldsAt {Model : Type} [Interpretation Model]
    (m : Model) (c : Categorical) (t : Interpretation.Moment Model) : Prop :=
  match c with
  | .A S P =>
      ∀ x, x ∈ ExtensionAt m S t → x ∈ ExtensionAt m P t
  | .E S P =>
      ∀ x, x ∈ ExtensionAt m S t → x ∉ ExtensionAt m P t
  | .I S P =>
      ∃ x, x ∈ ExtensionAt m S t ∧ x ∈ ExtensionAt m P t
  | .O S P =>
      ∃ x, x ∈ ExtensionAt m S t ∧ x ∉ ExtensionAt m P t

def IsOmnitemporal {Model : Type} [Interpretation Model]
    (m : Model) (c : Categorical) : Prop :=
  ∀ t : Interpretation.Moment Model, HoldsAt m c t

structure Science (Model : Type) [Interpretation Model] (m : Model) where
  subjectMatter : Set Term
  admits : Categorical → Prop
  admits_subject : ∀ {c : Categorical}, admits c → c.subject ∈ subjectMatter
  admits_predicate : ∀ {c : Categorical}, admits c → c.predicate ∈ subjectMatter

def Science.TrueIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m) (c : Categorical) : Prop :=
  science.admits c ∧ IsOmnitemporal m c

theorem Science.subject_mem_of_trueIn {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {c : Categorical}
    (h : science.TrueIn c) :
    c.subject ∈ science.subjectMatter :=
  science.admits_subject h.left

theorem Science.predicate_mem_of_trueIn {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m} {c : Categorical}
    (h : science.TrueIn c) :
    c.predicate ∈ science.subjectMatter :=
  science.admits_predicate h.left

def PremisesTrueIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m) (premises : List Categorical) : Prop :=
  ∀ ⦃premise : Categorical⦄, premise ∈ premises → science.TrueIn premise

theorem trueIn_of_mem_premises {Model : Type} [Interpretation Model]
    {m : Model} {science : Science Model m}
    {premises : List Categorical} {premise : Categorical}
    (h : PremisesTrueIn science premises) (hmem : premise ∈ premises) :
    science.TrueIn premise :=
  h hmem

def PremisesHoldAt {Model : Type} [Interpretation Model]
    (m : Model) (premises : List Categorical)
    (t : Interpretation.Moment Model) : Prop :=
  ∀ ⦃premise : Categorical⦄, premise ∈ premises → HoldsAt m premise t

theorem deduce_sound_at {Model : Type} [Interpretation Model]
    {m : Model} {premises : List Categorical} {conclusion : Categorical}
    (h : Deduce premises conclusion) :
    ∀ {t : Interpretation.Moment Model},
      PremisesHoldAt m premises t → HoldsAt m conclusion t := by
  intro t hpremises
  cases h with
  | Assumption c =>
      simpa using hpremises (premise := conclusion) (by simp)
  | ConvertE S P =>
      have hE : HoldsAt m (Categorical.E S P) t :=
        hpremises (premise := Categorical.E S P) (by simp)
      intro x hxP hxS
      exact (hE x hxS) hxP
  | ConvertI S P =>
      have hI : HoldsAt m (Categorical.I S P) t :=
        hpremises (premise := Categorical.I S P) (by simp)
      rcases hI with ⟨x, hxS, hxP⟩
      exact ⟨x, hxP, hxS⟩
  | Barbara S M P =>
      have hMajor : HoldsAt m (Categorical.A M P) t :=
        hpremises (premise := Categorical.A M P) (by simp)
      have hMinor : HoldsAt m (Categorical.A S M) t :=
        hpremises (premise := Categorical.A S M) (by simp)
      intro x hxS
      exact hMajor x (hMinor x hxS)
  | Celarent S M P =>
      have hMajor : HoldsAt m (Categorical.E M P) t :=
        hpremises (premise := Categorical.E M P) (by simp)
      have hMinor : HoldsAt m (Categorical.A S M) t :=
        hpremises (premise := Categorical.A S M) (by simp)
      intro x hxS hxP
      exact (hMajor x (hMinor x hxS)) hxP
  | Cesare S M P =>
      have hMajor : HoldsAt m (Categorical.E P M) t :=
        hpremises (premise := Categorical.E P M) (by simp)
      have hMinor : HoldsAt m (Categorical.A S M) t :=
        hpremises (premise := Categorical.A S M) (by simp)
      intro x hxS hxP
      exact (hMajor x hxP) (hMinor x hxS)
  | Camestres S M P =>
      have hMajor : HoldsAt m (Categorical.A P M) t :=
        hpremises (premise := Categorical.A P M) (by simp)
      have hMinor : HoldsAt m (Categorical.E S M) t :=
        hpremises (premise := Categorical.E S M) (by simp)
      intro x hxS hxP
      exact (hMinor x hxS) (hMajor x hxP)

theorem derives_sound_at {Model : Type} [Interpretation Model]
    {m : Model} {premises : List Categorical} {conclusion : Categorical}
    (h : Derives premises conclusion) :
    ∀ {t : Interpretation.Moment Model},
      PremisesHoldAt m premises t → HoldsAt m conclusion t := by
  intro t hpremises
  induction h with
  | premise hmem =>
      exact hpremises hmem
  | unary hmajor hstep ihMajor =>
      rename_i major conclusion
      have hMajorAt : HoldsAt m major t := ihMajor
      exact deduce_sound_at hstep (t := t) (by
        intro premise hmem
        have hpremise : premise = major := by
          simpa using hmem
        subst hpremise
        exact hMajorAt)
  | binary hmajor hminor hstep ihMajor ihMinor =>
      rename_i major minor conclusion
      have hMajorAt : HoldsAt m major t := ihMajor
      have hMinorAt : HoldsAt m minor t := ihMinor
      exact deduce_sound_at hstep (t := t) (by
        intro premise hmem
        have hpair : premise = major ∨ premise = minor := by
          simpa [List.mem_cons] using hmem
        rcases hpair with rfl | rfl
        · exact hMajorAt
        · exact hMinorAt)

theorem omnitemporal_of_derives {Model : Type} [Interpretation Model]
    {m : Model} {premises : List Categorical} {conclusion : Categorical}
    (hPremises : ∀ ⦃premise : Categorical⦄, premise ∈ premises → IsOmnitemporal m premise)
    (h : Derives premises conclusion) :
    IsOmnitemporal m conclusion := by
  intro t
  apply derives_sound_at h
  intro premise hmem
  exact hPremises hmem t

end Aristotle.PosteriorAnalytics
