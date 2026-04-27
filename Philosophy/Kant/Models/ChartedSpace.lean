import Philosophy.Kant.Laywine.Ekthesis
import Mathlib

universe u v

namespace Philosophy.Kant.Models

open TopologicalSpace

/-- A local perceptual sighting as a partial homeomorphism from sensible manifold to pure intuition. -/
abbrev PerceptualSighting (SensibleManifold : Type u) (PureIntuition : Type v)
    [TopologicalSpace SensibleManifold] [TopologicalSpace PureIntuition] :=
  OpenPartialHomeomorph SensibleManifold PureIntuition

/-- An empirical atlas is a charted space prior to global unification. -/
abbrev EmpiricalAtlas (PureIntuition : Type u) (SensibleManifold : Type v)
    [TopologicalSpace PureIntuition] [TopologicalSpace SensibleManifold] :=
  ChartedSpace PureIntuition SensibleManifold

theorem charted_space_supports_ekthesis
    (PureIntuition : Type u) (SensibleManifold : Type v)
    [TopologicalSpace PureIntuition] [TopologicalSpace SensibleManifold]
    [EmpiricalAtlas PureIntuition SensibleManifold] :
    Nonempty (EmpiricalAtlas PureIntuition SensibleManifold) :=
  ⟨inferInstance⟩

end Philosophy.Kant.Models
