import Philosophy.Aristotle.Core
import Philosophy.Aristotle.Basic
import Philosophy.Aristotle.Categories
import Philosophy.Aristotle.DeInterpretatione
import Philosophy.Aristotle.PriorAnalytics
import Philosophy.Aristotle.DialecticStaged
import Philosophy.Aristotle.PosteriorAnalytics
import Philosophy.Aristotle.InquiryBoundary
import Philosophy.Aristotle.MennAlignment
import Philosophy.Aristotle.SensesOfBeing
import Philosophy.Aristotle.PhysicsI
import Philosophy.Aristotle.PhysicsI_Principles
import Philosophy.Aristotle.PhysicsII_Causes
import Philosophy.Aristotle.Examples.DeInterpretatione
import Philosophy.Aristotle.Examples.Dialectic
import Philosophy.Aristotle.Examples.Demonstration
import Philosophy.Aristotle.Examples.Metaphysics

/-!
# Aristotle Public Root

This root module exposes the Aristotle subsystem as one ordered development.

`Philosophy/Aristotle/Aristotle.md` supplies the general Menn-guided map:
dialectic is preliminary and test-oriented, `De Interpretatione` and the
analytics articulate the statement and syllogistic layers without collapsing
them into one another, and first philosophy and physics come only after those
materials are in place. The current core now reflects that map with tokenized
lexical carriers, quiver-backed morphology, and an order-backed genus/species
layer that still leaves `said_of`, `in_subject`, and causal science distinct.
The more detailed Menn, Smith, and Whitaker-through-Weidemann reconstructions
are then dispersed throughout the individual modules and examples.

`Philosophy/Aristotle/MennAlignment.lean` wires a few **cross-layer** facts
(Reading B as a mathlib `OrderIso` to `Fin 2`, dually `OrderHom`s from the
chain, precomposition as an `Equiv` of those `OrderHom` spaces with `Fin 2 →o _`,
the `ℕ` rank as a concrete `OrderHom` (with the same `OrderHom` on
`InquiryAim` built as `descriptionStageRankHom` after the shape `OrderIso`, and
pointwise agreement of the two `ℕ` encodings along that bridge), **uniqueness**
of those `OrderIso` charts to `Fin 2` and of `InquiryAim ≃o DescriptionStage`
(bounded endpoints are forced by `OrderIso.map_bot` / `map_top`), and *rigidity*:
any `OrderIso` on
`DescriptionStage` is the identity; the same 2-point *skeleton* for
`Core.InquiryAim` and an `OrderIso` to `DescriptionStage` via `Fin 2` (not a
content identification with Reading B or with dialectical *roles*; inquiry
boundary);
`Philosophy/Aristotle/Menn_AimAndArgument_Map.md`
locates the in-repo *Aim and Argument* PDFs and states what the Lean does **not**
over-claim about the *Metaphysics* programme.
-/
