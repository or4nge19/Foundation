import Philosophy.Aristotle.PhysicsI

namespace Aristotle.Physics

/-!
# Local Coincidence of Causes

Aristotle sometimes allows one and the same thing to be formal, final, and even
efficient cause in a given domain. What should not be built into the library is
a global reduction of every efficient or final cause to a formal cause.

This module therefore records *local* alignments between causal roles.
-/

inductive Cause
  | material
  | formal
  | efficient
  | final
  deriving DecidableEq, Repr, Inhabited

class CausalRoles (Entity : Type) where
  material : Type
  formal : Type
  efficient : Type
  final : Type
  efficientCoincidesWithFormal : efficient → formal → Prop
  finalCoincidesWithFormal : final → formal → Prop

def EfficientCoincidesLocally [CausalRoles Entity]
    (efficient : CausalRoles.efficient (Entity := Entity)) : Prop :=
  ∃ formal : CausalRoles.formal (Entity := Entity),
    CausalRoles.efficientCoincidesWithFormal efficient formal

def FinalCoincidesLocally [CausalRoles Entity]
    (final : CausalRoles.final (Entity := Entity)) : Prop :=
  ∃ formal : CausalRoles.formal (Entity := Entity),
    CausalRoles.finalCoincidesWithFormal final formal

structure LocalCausalAlignment (Entity : Type) [CausalRoles Entity] where
  formal : CausalRoles.formal (Entity := Entity)
  efficient? : Option (CausalRoles.efficient (Entity := Entity)) := none
  final? : Option (CausalRoles.final (Entity := Entity)) := none
  efficient_aligns :
    ∀ {efficient : CausalRoles.efficient (Entity := Entity)},
      efficient? = some efficient →
        CausalRoles.efficientCoincidesWithFormal efficient formal
  final_aligns :
    ∀ {final : CausalRoles.final (Entity := Entity)},
      final? = some final →
        CausalRoles.finalCoincidesWithFormal final formal

end Aristotle.Physics
