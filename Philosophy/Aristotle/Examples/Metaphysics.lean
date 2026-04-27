import Philosophy.Aristotle.SensesOfBeing

namespace Aristotle.Examples.Metaphysics

open Philosophy.Aristotle.Metaphysics
open Philosophy.Aristotle.Core

/-!
Menn’s D7 *non-collapse* in one toy (see `Menn_AimAndArgument_Map` on truth vs
categorial ousia): the same `BeingProfile` data (per-se, categorial
substance, actual) is shared by two distinct `DemoBeing`s, while
`TruthStatus` still varies on the *thought* side. This is not a claim
that every substance must share a profile, only a **structural** witness
that the `BeingSenses` API keeps being-axes and truth-axes *separate*.

A second, minimal witness adds **per accidens** (same toy logic as
`dismiss_accidens_from_science` in `SensesOfBeing`): the profile’s
`accidentality` axis is not second-class *notation*; it is what the
`no_cause_for_accidens` field targets—without flattening *accidens* into
categorial *ousia* (AOMSB1 / Menn on D7 lists).

A third axis witness: **actuality / potentiality** is its own field (Menn: Θ
cross-cuts categorial structure in the full programme; here, only the profile
line is shown, not a `Dunamis` text layer).
-/

inductive DemoBeing
  | separateForm
  | separateFormPotential
  | embodiedThing
  | accidentalTrope
  deriving DecidableEq, Repr

inductive DemoThought
  | aboutSeparate
  | aboutEmbodied
  deriving DecidableEq, Repr

instance : Philosophy.Aristotle.Causality DemoBeing where
  material_cause _ _ := False
  formal_cause _ _ := False
  efficient_cause _ _ := False
  final_cause _ _ := False
  explains _ _ := False
  cause_guarantees_fact := by
    intro _ _ h
    cases h

instance : Philosophy.Aristotle.FirstPhilosophy DemoBeing where
  material_cause _ _ := False
  formal_cause _ _ := False
  efficient_cause _ _ := False
  final_cause _ _ := False
  explains _ _ := False
  cause_guarantees_fact := by
    intro _ _ h
    cases h
  is_primary_ousia b := b = .separateForm
  is_separate_in_formula b := b = .separateForm
  is_separate_in_existence b := b = .separateForm

def profileOf : DemoBeing → BeingProfile
  | .separateForm =>
      { accidentality := .perSe
        categorial := some .substance
        modal := .actual
        perSe_has_category := by
          intro _
          exact ⟨.substance, rfl⟩ }
  | .separateFormPotential =>
      { accidentality := .perSe
        categorial := some .substance
        modal := .potential
        perSe_has_category := by
          intro _
          exact ⟨.substance, rfl⟩ }
  | .embodiedThing =>
      { accidentality := .perSe
        categorial := some .substance
        modal := .actual
        perSe_has_category := by
          intro _
          exact ⟨.substance, rfl⟩ }
  | .accidentalTrope =>
      { accidentality := .perAccidens
        categorial := none
        modal := .actual
        perSe_has_category := by
          intro h
          cases h }

def concernsRel : DemoThought → DemoBeing → Prop
  | .aboutSeparate, .separateForm => True
  | .aboutEmbodied, .embodiedThing => True
  | _, _ => False

def trueThoughtRel : DemoThought → Prop
  | .aboutSeparate => True
  | .aboutEmbodied => False

def truthStatusOf : DemoThought → TruthStatus
  | .aboutSeparate => .affectionOfThought
  | .aboutEmbodied => .worldly

instance : BeingSenses DemoBeing DemoThought where
  profile := profileOf
  concerns := concernsRel
  trueThought := trueThoughtRel
  truthStatus := truthStatusOf
  no_cause_for_accidens := by
    intro _ _
    rintro ⟨_, h⟩
    cases h
  truth_is_affection_of_thought := by
    intro thought htrue
    cases thought <;> simp [trueThoughtRel, truthStatusOf] at htrue ⊢

theorem categorial_being_underdetermines_truth_sense :
    profileOf .separateForm = profileOf .embodiedThing ∧
      truthStatusOf .aboutSeparate ≠ truthStatusOf .aboutEmbodied := by
  refine And.intro ?hprof ?hne
  · decide
  · simp [truthStatusOf]

/-- The per se / per accidens **accidentality** axis is not cosmetic: it refutes profile
identity with any per-se `DemoBeing` (contrast the two per-se bodies that share a full
`BeingProfile`). -/
theorem per_se_ne_accidentalTrope :
    (profileOf .separateForm).accidentality ≠ (profileOf .accidentalTrope).accidentality := by
  simp [profileOf]

theorem profileOf_separateForm_ne_accidentalTrope : profileOf .separateForm ≠ profileOf .accidentalTrope :=
  BeingProfile.ne_of_accidentality_ne per_se_ne_accidentalTrope

/-- Same inequality of `DemoBeing`s, tracked along the **categorial** column of `BeingProfile`
(`some` substance vs `none` for the trope), matching `BeingProfile.ne_of_categorial_ne` on
D7’s category axis (Menn: categorial *ousia* is not the same *predicate* as per
accidens *being* in the list’s sense). -/
theorem categorial_substance_ne_none_on_accidentalTrope :
    (profileOf .separateForm).categorial ≠ (profileOf .accidentalTrope).categorial := by
  simp [profileOf]

theorem profileOf_separateForm_ne_accidentalTrope_via_categorial :
    profileOf .separateForm ≠ profileOf .accidentalTrope :=
  BeingProfile.ne_of_categorial_ne categorial_substance_ne_none_on_accidentalTrope

/-- `BeingSenses.b_ne_of_profile_ne`: distinct `BeingProfile` values on two **beings**
entail the beings are distinct (function extensionality on the `profile` field). -/
theorem separateForm_ne_accidentalTrope :
    DemoBeing.separateForm ≠ DemoBeing.accidentalTrope :=
  BeingSenses.b_ne_of_profile_ne (B := DemoBeing) (Thought := DemoThought)
    profileOf_separateForm_ne_accidentalTrope

/-- `BeingSenses.no_cause_for_accidens` for the toy: no `Causality.explains` answer to
“why is this *per accidens* line in the profile as it is?” (the class axiom is the
positive content; this is just the `DemoBeing` instance check). -/
theorem no_causal_science_of_accidental_profile :
    ¬ ∃ c : DemoBeing,
      Causality.explains c
        ((BeingSenses.profile (B := DemoBeing) (Thought := DemoThought) .accidentalTrope).accidentality =
          .perAccidens) :=
  BeingSenses.dismiss_accidens_from_science (B := DemoBeing) (Thought := DemoThought) (b := .accidentalTrope) rfl

theorem actual_ne_potential_separate_forms :
    (profileOf .separateForm).modal ≠ (profileOf .separateFormPotential).modal := by
  simp [profileOf]

theorem profileOf_separateForm_ne_separateFormPotential : profileOf .separateForm ≠ profileOf .separateFormPotential :=
  BeingProfile.ne_of_modal_ne actual_ne_potential_separate_forms

example : BeingSenses.trueThought (B := DemoBeing) (Thought := DemoThought) .aboutSeparate := by
  show trueThoughtRel .aboutSeparate
  simp [trueThoughtRel]

example :
    BeingSenses.truthStatus (B := DemoBeing) (Thought := DemoThought) .aboutSeparate =
      TruthStatus.affectionOfThought := by
  exact BeingSenses.trueThought_has_affection_status
    (B := DemoBeing)
    (Thought := DemoThought)
    (thought := .aboutSeparate)
    (by
      show trueThoughtRel .aboutSeparate
      simp [trueThoughtRel])

example :
    ∃ b : DemoBeing,
      BeingSenses.concerns (B := DemoBeing) (Thought := DemoThought) .aboutSeparate b ∧
        FirstPhilosophy.is_separate_in_existence b := by
  exact BeingSenses.trueThought_can_concern_separate
    (B := DemoBeing)
    (Thought := DemoThought)
    (thought := .aboutSeparate)
    (b := .separateForm)
    (by
      show trueThoughtRel .aboutSeparate
      simp [trueThoughtRel])
    (by
      show concernsRel .aboutSeparate .separateForm
      trivial)
    (by
      show DemoBeing.separateForm = DemoBeing.separateForm
      rfl)

end Aristotle.Examples.Metaphysics
