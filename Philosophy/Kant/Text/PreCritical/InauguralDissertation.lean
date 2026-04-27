import Mathlib

universe u v

namespace Philosophy.Kant.Text.PreCritical

/-- A text-level system for the Inaugural Dissertation: sensible vs intelligible world. -/
structure InauguralDissertationSystem where
  SensibleWorld : Type u
  IntelligibleWorld : Type v
  formOfSensibility : SensibleWorld → Prop
  formOfIntellect : IntelligibleWorld → Prop

def WorldWhole (K : InauguralDissertationSystem) : Prop :=
  ∀ s : K.SensibleWorld, K.formOfSensibility s

def PrinciplesOfFormOfWorld (K : InauguralDissertationSystem) : Prop :=
  ∀ i : K.IntelligibleWorld, K.formOfIntellect i

end Philosophy.Kant.Text.PreCritical
