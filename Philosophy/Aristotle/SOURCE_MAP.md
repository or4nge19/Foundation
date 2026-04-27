# Aristotle Source Map

## General Guide

| Source text in repo | Lean module | Status |
| --- | --- | --- |
| `Philosophy/Aristotle/Aristotle.md` | `Philosophy/Aristotle.lean`, `Philosophy/Aristotle/ARCHITECTURE.md`, and the headers of the major Aristotle modules | General guide only: it fixes the disciplinary order of dialectic, analytics, first philosophy, and physics; the more detailed Menn/Smith reconstructions then determine the local APIs |

## Menn-Facing Modules

| Source text in repo | Lean module | Status |
| --- | --- | --- |
| `Philosophy/Aristotle/MDC_Menn.md` | `Philosophy/Aristotle/Categories.lean` and `Philosophy/Aristotle/DialecticStaged.lean` | Implemented as staged screening, placement, Menn dossiers, and explicit provisional/refuted diagnoses for genus, dialectical-definition, and proprium problems; the current refactor also tokenizes lexical carriers, makes paronymy quiver-backed, makes genus/species location order-backed, marks dialectical `Problem`s as explicitly `hoti` rather than `dioti`, adds a generalized `SurfaceTrap` layer whose current source-led core case is the `SE` 22 active-appearance / affection-reality mismatch, gives `diagnoseDefinition` a priority-sensitive admissible/refuted characterization API, and now lets both figure-of-speech and broader surface-trap defeat block dossier-style admissibility rather than being flattened into a generic `categoryMismatch` |
| `Philosophy/Aristotle/AOMSB1.md` | `Philosophy/Aristotle/SensesOfBeing.lean` | Implemented as orthogonal axes plus a distinct thought layer; the current refactor tightens the thought/being interface so truth remains in thought without forbidding true thought about separate beings |
| `Philosophy/Aristotle/Path to Principles.md` | `Philosophy/Aristotle/PhysicsI.lean` | Implemented in Reading-B form |
| `Path to Principles.md` + `AOMSB1.md` + `InquiryBoundary` (conceptual) | `Philosophy/Aristotle/MennAlignment.lean` | **Cross-map only (Lean):** mathlib `PartialOrder`/`BoundedOrder` on `DescriptionStage`, `descriptionStage_le_total`, `readingB_stages_and_samePrinciple` (⊥→⊤ on stages plus `preserves_principle` in one bundle), bridges from `PathToPrinciples` / `InquiryBoundary`, and docs that keep the Physics-path, ὅτι/διότι, and D7/being axes *explicitly distinct*; PDFs `Ia1*.pdf`–`IIIa2.pdf` / `I*`–`III*` are human references, not extracted into Lean |
| Menn, *The Aim and the Argument of Aristotle’s Metaphysics* (PDFs `I*`, `II*`, `IIIa2`) + `AOMSB1.md` | `Philosophy/Aristotle/Menn_AimAndArgument_Map.md` | **Human integration note only:** maps internal PDF filenames to Menn’s book cross-references (e.g. Ig1b), lists non-conflation rules (physics Reading B vs causes of being qua being, D7 vs single predicate, dialectic vs first philosophy, Δ *stoiceion*/*arche*), and audits what Lean implements vs what would overclaim |

## De Interpretatione Via Whitaker and Weidemann

| Source text in repo | Lean module | Status |
| --- | --- | --- |
| `Philosophy/Aristotle/H. Weidemann - De Interpretationae.md` | `Philosophy/Aristotle/DeInterpretatione.lean` and `Philosophy/Aristotle/PriorAnalytics/Syntax.lean` | Implemented as a statement-side layer with assertoric assertions, contradictory pairing, negated-term and many-as-one carriers, singular future-contingent exception-typing, and the bridge by which the later syllogistic narrows to universal/particular categorical forms; `DI` 11-13 refinements remain pending |

## Topics Reconstruction Via Smith

| Source text in repo | Lean module | Status |
| --- | --- | --- |
| `Philosophy/Aristotle/Topics-I.1.md` and `Topics-I.2,3.md` | `Philosophy/Aristotle/ARCHITECTURE.md` and `Philosophy/Aristotle/DialecticStaged.lean` | Governs the practical but non-scientific role of dialectic, its uses, and its examinational relation to first principles |
| `Philosophy/Aristotle/Topics-I.4,5,6.md` and `Topics-I.7,8.md` | `Philosophy/Aristotle/Categories.lean` and `Philosophy/Aristotle/DialecticStaged.lean` | Governs predicables, sameness/difference, and the non-collapse of definition into a flat predicate |
| `Philosophy/Aristotle/Topics-I.9,10,11.md` | `Philosophy/Aristotle/Categories.lean` and `Philosophy/Aristotle/DialecticStaged.lean` | Governs categories, dialectical premiss, dialectical problem, and thesis; partially implemented, with richer source-guided refinement still pending |
| `Philosophy/Aristotle/Topics-I.12,13.md`, `Topics-I.14.md`, `Topics-I.15.md`, and `Topics-I.16,17,18.md` | `Philosophy/Aristotle/Categories.lean`, `Philosophy/Aristotle/DialecticStaged.lean`, and future dialectical utilities | Governs induction/deduction, premiss-collection, many-ways-said, differences, likenesses, and locations; currently only partially dispersed, with a dedicated tranche still pending |
| `Philosophy/Aristotle/Topics-VIII.1.md` through `Topics-VIII.14.md` | `Philosophy/Aristotle/DialecticStaged.lean` and `Philosophy/Aristotle/Examples/Dialectic.lean` | Governs arrangement, concealment, answerer norms, objections, criticism, and training; current staging/session APIs are only a first approximation |

## Smith-Facing Modules

| Source text in repo | Lean module | Status |
| --- | --- | --- |
| `Philosophy/Aristotle/R.Smith - Aristotle's Regress Argument.md` | `Philosophy/Aristotle/PriorAnalytics/Chains.lean`, `Philosophy/Aristotle/PriorAnalytics/Regress.lean`, and `Philosophy/Aristotle/PosteriorAnalytics/Core.lean` | Semantic chains separated from proof-search routes; stronger regress scaffolding added; the current frontier now bridges demonstrative one-step expansion back to singleton-stock `PremiseExpansion` witnesses and lifts minimal demonstrative basis construction into Posterior Analytics core |
| `Philosophy/Aristotle/R.Smith - Immediate Propositions and aristotle's Proof theory.md` | `Philosophy/Aristotle/PosteriorAnalytics/Core.lean` | Immediacy and first principles made science-relative; demonstrative support is now tracked through an explicit basis layer, and universal negatives now have their own figure-sensitive immediacy form rather than only a flat underivability fallback |
| `Philosophy/Aristotle/R.Smith - Aristotle's theory of demonstration.md` | `Philosophy/Aristotle/PosteriorAnalytics/Semantics.lean` and `Philosophy/Aristotle/PosteriorAnalytics/Core.lean` | Demonstration rebuilt over term-extensional truth conditions; the current refactor strengthens explanatory middle and non-reciprocity so demonstration does not collapse into validity alone, adds an explicit `WhyQuestion` API plus figured explanatory syllogisms for the `dioti` side of science, extends that layer through the currently modeled universal negative moods, and now replaces the old vacuous causal tag with a definition-grounded `PerSePredicationIn` / `SecondPerSePredicationIn` / `IsCauseOf` / `CausalDemonstration` layer in which second-figure causal answers are routed through their perfected first-figure companion. That companion story is now explicit rather than merely example-local via `UniqueMiddleIn`, `UniqueExplanatoryMiddleIn`, `UniqueCausalMiddleIn`, `CompanionCausalRouteIn`, factor-through Cesare/Camestres companion-route theorems, and the new regress/demonstration bridge plus core minimal-basis constructor |

## Shared Infrastructure

| Concern | Lean module | Status |
| --- | --- | --- |
| Shared Aristotle kernel | `Philosophy/Aristotle/Core.lean` | Canonical; lexical carriers are tokenized, morphology is quiver-backed, and genus/species hierarchy is order-backed |
| Compatibility prelude | `Philosophy/Aristotle/Basic.lean` | Thin facade only |
| Public Aristotle import surface | `Philosophy/Aristotle.lean` | Canonical |
| Whether/why boundary API | `Philosophy/Aristotle/InquiryBoundary.lean` | Implemented: makes the `Problem`/`WhyQuestion` aim split explicit, bridges same-content re-asking via `Problem.statement?` and `WhyQuestion.ofConclusion`, and now exposes the full anti-promotion family by which every staged definition-refutation arm, together with the broader surface-trap generalization, blocks naive scientific promotion |

## Examples

Worked examples live under `Philosophy/Aristotle/Examples/` and are intended to
serve as regression tests for the public APIs rather than as one-off sketches.
The `DeInterpretatione` example now covers singular, indefinite, negated-term,
many-as-one, and future-contingent assertoric cases together with the
categorical bridge. The dialectic example now covers a failed genus proposal, a
successful genus bridge via `Predication.genus_of`, a dialectical-definition
diagnosis, a definition-specific elenchus target, a proprium diagnosis, the
explicit `hoti` orientation of dialectical `Problem`s, and now a Menn-style
`SE` 22 case where `seeing` looks active but is categorically resolved as
affection and diagnosed as a distinct figure-of-speech refutation for both a
genus proposal and a definition proposal, together with the boundary theorem
showing that such a refuted definition cannot be naively promoted into a
scientific-definition style success. It now also witnesses the generalized
`SurfaceTrap` layer: the same case yields surface-trap refutations that block
provisional genus screening, admissible definition diagnosis, and naive
scientific promotion even at the more general API level. The demonstration
example now separates a merely valid syllogism from a genuine demonstration
with a non-vacuous explanatory witness, an explicit `WhyQuestion`, positive and
negative causal `why`-answer cases, a negative non-reciprocity case, a full
negative demonstration, causal refinements of both the positive and negative
demonstrations grounded in scientific definition / per-se structure, an
explicit second-kind per-se example, reusable middle-selectivity and
companion-route APIs, a `Cesare` causal answer routed through its perfected
`Celarent` companion by those APIs, the new figured explanatory/causal
uniqueness layer, an explicit regress/demonstration bridge witness, and a
minimal first-principle basis now rebuilt through the core `minimalBasis`
constructor. The metaphysics example now witnesses the repaired D7 claim that
true thought may still concern a separate being while truth remains an
affection of thought.

## Evaluation Note

The heavier post-phase-3 candidates, a `Science`-extension relation and a
global priority / well-founded support layer, have now been evaluated and
deferred. The current Menn/Smith frontier tranches landed cleanly with
boundary, diagnosis, middle-selectivity, regress-bridge, and surface-trap APIs
alone, so adding heavier infrastructure now would outrun the present
source-grounded examples.
