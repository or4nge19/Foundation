import Mathlib

universe u v w

namespace Philosophy.Kant.Laywine

/-- Ekthesis abstracts the projection of sensible sightings into pure intuition. -/
structure EkthesisSystem where
  SensibleManifold : Type u
  PureIntuition : Type v
  TimeLine : Type w
  Sighting : Type (max u v w)
  locateInTime : Sighting → TimeLine
  projects : Sighting → SensibleManifold → PureIntuition → Prop

end Philosophy.Kant.Laywine
