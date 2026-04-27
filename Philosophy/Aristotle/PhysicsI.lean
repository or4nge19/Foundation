import Philosophy.Aristotle.PosteriorAnalytics

namespace Aristotle.Physics

/-!
# The Path to the Principles

This module follows Menn's preferred Reading B of `Physics` I.1:

- the principles are not first reached by decomposing a whole into alien parts
- they are already obscurely present under confused universal descriptions
- progress consists in articulating those same principles under sharper and more
  particular descriptions
-/

inductive DescriptionStage
  | confusedUniversal
  | articulatedParticular
  deriving DecidableEq, Repr, Inhabited

structure PrincipleDescription (Item : Type) where
  principle : Item
  label : String
  stage : DescriptionStage

class PathToPrinciples (Item : Type) where
  confusedDescription : Item → PrincipleDescription Item
  articulate : PrincipleDescription Item → PrincipleDescription Item
  preserves_principle :
    ∀ description : PrincipleDescription Item,
      (articulate description).principle = description.principle
  starts_confused :
    ∀ principle : Item,
      (confusedDescription principle).stage = .confusedUniversal
  articulate_sharpens :
    ∀ description : PrincipleDescription Item,
      description.stage = .confusedUniversal →
        (articulate description).stage = .articulatedParticular

structure HylomorphicPrinciples (Item : Type) where
  subject : Item
  matter : PrincipleDescription Item
  form : PrincipleDescription Item
  privation : PrincipleDescription Item

structure Generation (Item : Type) where
  principles : HylomorphicPrinciples Item
  form_is_articulated :
    principles.form.stage = .articulatedParticular
  privation_is_articulated :
    principles.privation.stage = .articulatedParticular

theorem articulate_preserves_principle {Item : Type} [PathToPrinciples Item]
    (description : PrincipleDescription Item) :
    (PathToPrinciples.articulate description).principle = description.principle :=
  PathToPrinciples.preserves_principle description

/--
Iterated articulation: `0` is the identity on `PrincipleDescription`, `n + 1` prepends
one `PathToPrinciples.articulate` step. Menn’s Reading B treats progress as
sharper *description* of the same principles, not a swap of which item is in play; the
`principle` field is therefore fixed at every finite iteration (`articulateNTimes_principle`).
-/
def articulateNTimes {Item : Type} [PathToPrinciples Item] (n : ℕ) (d : PrincipleDescription Item) :
    PrincipleDescription Item :=
  n.rec d (fun _ d' => PathToPrinciples.articulate d')

theorem articulateNTimes_principle {Item : Type} [PathToPrinciples Item] (n : ℕ)
    (d : PrincipleDescription Item) : (articulateNTimes n d).principle = d.principle := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (PathToPrinciples.articulate (articulateNTimes n d)).principle = d.principle
    rw [PathToPrinciples.preserves_principle, ih]

end Aristotle.Physics
