import Philosophy.Aristotle.Basic

namespace Philosophy.Aristotle.Metaphysics

open Philosophy.Aristotle
open Philosophy.Aristotle.Core

/-!
# The Senses of Being

`Metaphysics` Δ7 does not present one flat enumeration. In this refactor:

- beings are classified by accidentality, categorial placement, and modal status
- being-as-truth is modeled on a separate type of thoughts

`Philosophy/Aristotle/Aristotle.md` gives the general disciplinary guide by
placing first philosophy beyond dialectic and physics. `AOMSB1.md` then governs
the local reconstruction used here: truth is an affection of thought, and
potentiality/actuality cross-cuts categorial being rather than forming one more
peer sense beside it. The point is not anti-realism about what thought is
about, but the correct formal location of truth.

`Menn_AimAndArgument_Map.md` (audit on D7) is explicit: the Lean slice here is
only a **non-collapse** of axes, not a model of the whole *Metaphysics*. The
*driver* is Menn’s separation of **categorial / modal / per-accidens
structure** of beings from the **where truth lives** (`thought`, not
conflated with ousia-in-the-same-sense as D7’s list). A concrete
mathlib-witness of that independence lives in
`Aristotle/Examples/Metaphysics.lean` (`categorial_being_underdetermines_truth_sense`).
-/

/--
`BeingProfile` packages the main Δ7 axes currently used in the formalization:
per-se/per-accidens, categorial placement, and actuality/potentiality.
-/
structure BeingProfile where
  accidentality : Accidentality
  categorial : Option Category
  modal : ActualityStatus
  perSe_has_category : accidentality = .perSe → ∃ category, categorial = some category
  deriving DecidableEq

namespace BeingProfile

theorem ext {p q : BeingProfile} (h₁ : p.accidentality = q.accidentality) (h₂ : p.categorial = q.categorial)
    (h₃ : p.modal = q.modal) : p = q := by
  /- The data fields fix the `Prop` field by proof irrelevance. -/
  cases p
  cases q
  case mk a₁ c₁ m₁ _p₄ a₂ c₂ m₂ _q₄ =>
    subst h₁; subst h₂; subst h₃; rfl

theorem ne_of_accidentality_ne {p q : BeingProfile} (h : p.accidentality ≠ q.accidentality) : p ≠ q := by
  intro heq; exact h (congrArg BeingProfile.accidentality heq)

theorem ne_of_modal_ne {p q : BeingProfile} (h : p.modal ≠ q.modal) : p ≠ q := by
  intro heq; exact h (congrArg BeingProfile.modal heq)

theorem ne_of_categorial_ne {p q : BeingProfile} (h : p.categorial ≠ q.categorial) : p ≠ q := by
  intro heq; exact h (congrArg BeingProfile.categorial heq)

theorem ext_iff (p q : BeingProfile) :
    p = q ↔
      p.accidentality = q.accidentality ∧ p.categorial = q.categorial ∧ p.modal = q.modal := by
  constructor
  · intro h; simp [h]
  · rintro ⟨h1, h2, h3⟩; exact ext h1 h2 h3

end BeingProfile

/--
`BeingSenses` separates the thought-side carrier of truth from the being-side
profiles it concerns. This encodes the D7 claim that truth belongs to thought
without forbidding true thought about separate beings.
-/
class BeingSenses (B Thought : Type) [FirstPhilosophy B] [Causality B] where
  profile : B → BeingProfile
  concerns : Thought → B → Prop
  trueThought : Thought → Prop
  truthStatus : Thought → TruthStatus
  no_cause_for_accidens : ∀ {b : B},
    (profile b).accidentality = .perAccidens →
      ¬ ∃ c : B, Causality.explains c ((profile b).accidentality = .perAccidens)
  truth_is_affection_of_thought : ∀ {thought : Thought},
    trueThought thought →
      truthStatus thought = .affectionOfThought

namespace BeingSenses

theorem perSe_has_category {B Thought : Type}
    [FirstPhilosophy B] [Causality B] [BeingSenses B Thought]
    {b : B}
    (h : (BeingSenses.profile (B := B) (Thought := Thought) b).accidentality =
      Accidentality.perSe) :
    ∃ category,
      (BeingSenses.profile (B := B) (Thought := Thought) b).categorial = some category :=
  (BeingSenses.profile (B := B) (Thought := Thought) b).perSe_has_category h

theorem dismiss_accidens_from_science {B Thought : Type}
    [FirstPhilosophy B] [Causality B] [BeingSenses B Thought]
    {b : B}
    (h : (BeingSenses.profile (B := B) (Thought := Thought) b).accidentality =
      Accidentality.perAccidens) :
    ¬ ∃ c : B,
      Causality.explains c
        ((BeingSenses.profile (B := B) (Thought := Thought) b).accidentality =
          Accidentality.perAccidens) :=
  BeingSenses.no_cause_for_accidens h

theorem trueThought_has_affection_status {B Thought : Type}
    [FirstPhilosophy B] [Causality B] [BeingSenses B Thought]
    {thought : Thought}
    (h : BeingSenses.trueThought (B := B) (Thought := Thought) thought) :
    BeingSenses.truthStatus (B := B) (Thought := Thought) thought =
      TruthStatus.affectionOfThought :=
  BeingSenses.truth_is_affection_of_thought h

theorem trueThought_can_concern_separate {B Thought : Type}
    [FirstPhilosophy B] [Causality B] [BeingSenses B Thought]
    {thought : Thought} {b : B}
    (_htrue : BeingSenses.trueThought (B := B) (Thought := Thought) thought)
    (hconcerns : BeingSenses.concerns (B := B) (Thought := Thought) thought b)
    (hseparate : FirstPhilosophy.is_separate_in_existence b) :
    ∃ b' : B,
      BeingSenses.concerns (B := B) (Thought := Thought) thought b' ∧
        FirstPhilosophy.is_separate_in_existence b' := by
  exact ⟨b, hconcerns, hseparate⟩

/-- In any `BeingSenses` model, `profile` is a function: different `BeingProfile` values
force different beings (contrapositive of `congrArg profile`). This is the formal
“axes distinguish items” fact behind using `profile` to index a Δ7-style split
without reifying a single *being* predicate. -/
theorem b_ne_of_profile_ne {B Thought : Type} [FirstPhilosophy B] [Causality B] [BeingSenses B Thought]
    {b b' : B}
    (h :
      BeingSenses.profile (B := B) (Thought := Thought) b ≠
        BeingSenses.profile (B := B) (Thought := Thought) b') :
    b ≠ b' := by
  intro heq; rw [heq] at h; exact h rfl

end BeingSenses

end Philosophy.Aristotle.Metaphysics
