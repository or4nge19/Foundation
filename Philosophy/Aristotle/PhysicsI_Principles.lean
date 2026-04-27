import Philosophy.Aristotle.PhysicsI

namespace Aristotle.PhysicsI

/-!
# Legacy Physics I Names

The canonical `PathToPrinciples` API now lives in `Aristotle.Physics` and is
explicitly Reading-B oriented. This module keeps the older file path stable
while re-exporting the shared implementation.
-/

abbrev DescriptionLevel := Aristotle.Physics.DescriptionStage
abbrev PrincipleDescription := Aristotle.Physics.PrincipleDescription
abbrev PathToPrinciples := Aristotle.Physics.PathToPrinciples
abbrev HylomorphicPrinciples := Aristotle.Physics.HylomorphicPrinciples
abbrev Genesis := Aristotle.Physics.Generation

end Aristotle.PhysicsI
