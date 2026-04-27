---
name: Menn principled refactor tranches
overview: Concrete phased refactor plan for the remaining Aristotle work after the completed Menn dialectic tranche, with Menn governing the admissible materials of dialectic, Smith governing explanatory demonstration and regress, and mathlib governing interface discipline.
todos:
  - id: docs-constitution
    content: Write the non-collapse design rules into architecture, source-map, and glossary docs so the documented API matches the intended Menn and Smith distinctions.
    status: pending
  - id: definitional-phrase
    content: Replace bare-term definition problems with structured definitional phrases and a screened path for combined expressions.
    status: pending
  - id: substance-rank-split
    content: Split primary and secondary substance recognition so only primary substance carries the this-something criterion.
    status: pending
  - id: dialectic-definition-upgrade
    content: Rebuild dialectical definition dossiers and thesis stages around genus-plus-differentia rather than flat positioned candidates.
    status: pending
  - id: explanatory-middle
    content: Replace the vacuous causal middle marker in PosteriorAnalytics with a structured explanatory witness tied to a science.
    status: pending
  - id: smith-reciprocity
    content: Strengthen immediacy and non-reciprocity from one-step derivability to expansion-sensitive, cycle-aware demonstrative dependence.
    status: pending
  - id: truth-in-thought
    content: Recast D7 so ontological being and truth-in-thought are distinct layers without banning true thought about separate beings.
    status: pending
  - id: example-regressions
    content: Upgrade the dialectic and demonstration examples into regression suites for the new Menn and Smith APIs.
    status: pending
isProject: false
---

# Menn Principled Refactor Tranches

## Relation To Existing Plans

- `menn_dialectic_tranche_74c3ead2.plan.md` completed the workflow side of the Menn layer: dossiers, diagnoses, thesis stages, examples, and docs.
- `aristotle_refactor_review_2c219f4a.plan.md` established the architectural direction of the unified Aristotle subsystem.
- The remaining pressure is no longer the existence of staged workflows. It is the adequacy of the objects flowing through them: definitions are still too flat, secondary substance is still typed too much like primary substance, and demonstration still lacks a non-vacuous explanatory middle.

## Governing Rules

1. Menn leads first.
   The admissible materials of inquiry are fixed in `Categories` and `DialecticStaged` before `PosteriorAnalytics` is allowed to speak about science, immediacy, or demonstration.

2. Smith leads second.
   Once the materials are right, `PosteriorAnalytics` must distinguish valid deduction from explanatory demonstration and underivability from immediacy without a middle.

3. mathlib discipline governs throughout.
   Historical distinctions should be encoded as type or predicate splits, not only as comments. Keep syntax, semantics, and explanatory structure in separate modules.

4. Preserve the completed tranche.
   Do not reopen the already completed dossier-and-diagnosis work except where the new typed objects require migration.

## Non-Collapse Constitution

- Do not collapse simple term and combined definiens.
- Do not collapse dialectical definition and scientific definition.
- Do not collapse primary substance and secondary substance.
- Do not collapse valid syllogism and explanatory demonstration.
- Do not collapse ontological being and truth-in-thought.

## Tranche A: Menn Material Adequacy

### Focus

- Rebuild the objects of dialectical inquiry so the completed staging machinery operates over historically faithful materials rather than over flattened placeholders.

### File Targets

- `Philosophy/Aristotle/ARCHITECTURE.md`
- `Philosophy/Aristotle/SOURCE_MAP.md`
- `Philosophy/Aristotle/GLOSSARY.md`
- `Philosophy/Aristotle/Core.lean`
- `Philosophy/Aristotle/Categories.lean`
- `Philosophy/Aristotle/DialecticStaged.lean`
- `Philosophy/Aristotle/Examples/Dialectic.lean`

### Required Changes

1. Document the design constitution.

- Update the docs so they explicitly distinguish:
  `Term`, `Expression`, `DefinitionalPhrase`, `DialecticalDefinition`, `ScientificDefinition`, `PrimarySubstance`, `SecondarySubstance`, `Demonstration`, and `TruthInThought`.
- Make the docs describe definition and substance as still under principled refinement, rather than as already complete.

2. Introduce structured definitional phrases.

- Add a definition-side object such as `DefinitionalPhrase` or `DialecticalDefiniens`.
- Preserve genus and differentiae as distinct fields rather than folding them into one term like `"rational animal"`.
- Add a screened version over `CategorialCandidate` so combined definitional material can enter the dialectical pipeline.

3. Refactor the definition problem path.

- Change `Problem.definition` in `DialecticStaged.lean` to carry a structured definitional phrase.
- Add definition-specific blocked and refuted outcomes, such as:
  malformed phrase, empty differentiae, missing genus anchor, differentia not predicated, differentia in subject.

4. Split substance ranks.

- Replace the shared `SubstanceIdia` bundle with distinct primary and secondary substance marks.
- Keep `signifiesThis` only for primary substance.
- Require `saidOf` and `¬ inSubject` for secondary substance, without forcing secondary substances to count as this-somethings.

5. Rebuild dialectical definition dossiers.

- Make dialectical definition a weaker, orienting, test-oriented structure in the Menn sense.
- Require explicit genus anchoring and differentia predication.
- Leave scientific definition as a stricter downstream layer rather than strengthening dialectical definition by a boolean flag.

### Acceptance Criteria

- `Expression.combined` is no longer dead for definition work.
- `Problem.definition` no longer takes a bare `Term`.
- `RecognizedSecondarySubstance` no longer inherits `signifiesThis`.
- `Examples/Dialectic.lean` contains separate regression cases for:
  failed genus, successful genus, dialectical definition, failed definition, primary substance, and secondary substance.

### Target Signatures For Tranche A

These are target shapes, not yet binding line-by-line implementations. They are
meant to stabilize names, directions of dependency, and the distinction between
orienting dialectical work and stronger scientific work.

```lean
structure DefinitionalPhrase where
  genus : Term
  differentiae : List Term
  lexicalForm : Option String := none
  nonempty : differentiae ≠ []
```

```lean
structure ScreenedDefinitionalPhrase [AntepredicamentalManual] where
  genus : CategorialCandidate
  differentiae : List CategorialCandidate
  nonempty : differentiae ≠ []
```

```lean
structure PositionedDefinitionalPhrase [Manual] where
  genus : PositionedCandidate
  differentiae : List PositionedCandidate
  nonempty : differentiae ≠ []
```

```lean
structure PrimarySubstanceMarks [Manual] (candidate : PositionedCandidate) : Prop where
  isSubstance : candidate.placement.category = Category.substance
  signifiesThis : signifiesThis candidate.candidate
  notSaidOf : ¬ isSaidOf candidate.candidate
  notInSubject : ¬ isInSubject candidate.candidate
```

```lean
structure SecondarySubstanceMarks [Manual] (candidate : PositionedCandidate) : Prop where
  isSubstance : candidate.placement.category = Category.substance
  saidOf : isSaidOf candidate.candidate
  notInSubject : ¬ isInSubject candidate.candidate
```

```lean
inductive SubstanceRank
  | primary
  | secondary
  deriving DecidableEq, Repr
```

```lean
inductive Problem
  | predication (subject predicate : DialecticalTerm)
  | genus (subject genusTerm : DialecticalTerm)
  | definition (subject : DialecticalTerm) (phrase : DefinitionalPhrase)
  | proprium (subject property : DialecticalTerm)
  deriving DecidableEq, Repr
```

```lean
structure DialecticalDefinitionDossier [PredicationalManual]
    (subject : PositionedCandidate)
    (phrase : PositionedDefinitionalPhrase) : Prop where
  genus_same_category : sameCategory subject phrase.genus
  genus_said_of : genusOfSubject phrase.genus.candidate subject.candidate
  differentiae_said_of :
    ∀ d, d ∈ phrase.differentiae -> differentiaOfSubject d.candidate subject.candidate
  differentiae_not_in_subject :
    ∀ d, d ∈ phrase.differentiae -> ¬ isInSubject d.candidate
```

### Theorem Inventory For Tranche A

The first implementation should aim at theorem coverage at least strong enough
to support the current examples plus one new secondary-substance example.

1. Screening and transport theorems.

- `screenedDefinitionalPhrase_genus_has_reference`
- `screenedDefinitionalPhrase_differentiae_have_reference`
- `positionedDefinitionalPhrase_genus_positioned`
- `positionedDefinitionalPhrase_nonempty`

2. Substance rank separation theorems.

- `PrimarySubstanceMarks.not_saidOf`
- `SecondarySubstanceMarks.not_inSubject`
- `primary_not_secondary`
- `secondary_not_primary_of_saidOf`

3. Dialectical definition dossier theorems.

- `DialecticalDefinitionDossier.genus_is_said_of`
- `DialecticalDefinitionDossier.differentia_is_said_of`
- `DialecticalDefinitionDossier.differentia_not_in_subject`
- `DialecticalDefinitionDossier.no_in_subject_differentia`

4. Migration lemmas for compatibility.

- `RecognizedPrimarySubstance.of_marks`
- `RecognizedSecondarySubstance.of_marks`
- thin compatibility theorems for existing example names, if needed, until the
  examples are fully rewritten to the new API.

### Staged Diagnosis Inventory For Tranche A

The refactor should make the definition path as explicit as the genus path is
now. The minimum useful split is:

```lean
inductive DefinitionScreeningFailure
  | genusBlocked
  | someDifferentiaBlocked
  | emptyDifferentiae
```

```lean
inductive DefinitionDiagnosis [Manual] (problem : PositionedDefinitionProblem) where
  | admissible (dossier : DialecticalDefinitionDossier problem.subject problem.phrase)
  | genusCategoryMismatch ...
  | genusNotSaidOf ...
  | someDifferentiaNotSaidOf ...
  | someDifferentiaInSubject ...
```

The point is not only extra constructors. It is that the stage records the
Menn-style reason why a proposal survives or fails.

### Migration Sequence For Tranche A

1. Add the new phrase and substance-rank structures without deleting the old
   ones.
2. Migrate `Problem.definition`, `ScreenedProblem`, and `PositionedProblem`.
3. Add dossiers and theorem helpers for the new definition path.
4. Move `Examples/Dialectic.lean` to the new API.
5. Remove or alias the old flat definition objects only after the examples and
   docs read cleanly again.

## Tranche B: Smith Demonstration Adequacy

### Focus

- Rebuild the Posterior Analytics layer so demonstration requires explanatory force and immediacy is stronger than mere underivability from arbitrary premise lists.

### File Targets

- `Philosophy/Aristotle/PriorAnalytics/Chains.lean`
- `Philosophy/Aristotle/PriorAnalytics/Regress.lean`
- `Philosophy/Aristotle/PosteriorAnalytics/Semantics.lean`
- `Philosophy/Aristotle/PosteriorAnalytics/Core.lean`
- `Philosophy/Aristotle/Examples/Demonstration.lean`

### Required Changes

1. Replace the vacuous causal middle marker.

- Remove the empty `IsCauseOf` role as the final explanatory criterion.
- Introduce a structured witness such as `MiddleExplainsIn`.
- Tie that witness to a `Science`, the admissibility of the middle, and the truth of the premises it is meant to explain.

2. Distinguish deduction from demonstration.

- Preserve `Deduce`, `Derives`, and the existing soundness results as the proof-theoretic base.
- Require more for `Demonstration`: first principles, explanatory middle, and strengthened anti-reciprocity.
- Ensure the demonstration example can no longer discharge causality with an empty instance.

3. Strengthen immediacy.

- For A-propositions, define immediacy in explicitly middle-sensitive terms.
- For negative conclusions, extend the notion through the route-expansion framework already present in `Chains` and `Regress`.
- Keep science-relativity throughout.

4. Strengthen non-reciprocity.

- Replace the current one-step prohibition `¬ Derives [conclusion] premise` with an expansion-sensitive notion that blocks reciprocal and circular return through admissible demonstrative development.
- Use cycle-aware or reachability-style structure rather than only singleton-premise derivability.

### Acceptance Criteria

- `Examples/Demonstration.lean` contains one valid syllogism that is not yet a demonstration.
- `Demonstration` requires a non-vacuous explanatory witness.
- `ImmediateIn` and `NonReciprocal` talk about demonstrative structure, not only arbitrary derivability.

### Target Signatures For Tranche B

The Smith layer should preserve the current proof-theoretic and semantic work
where it is already honest, but strengthen the explanatory layer so
demonstration is not merely validity plus labels.

```lean
structure MiddleExplainsIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m)
    (minor middle major : Term) : Prop where
  middle_in_subject_matter : middle ∈ science.subjectMatter
  minor_to_middle_true : science.TrueIn (Categorical.A minor middle)
  middle_to_major_true : science.TrueIn (Categorical.A middle major)
  explanatory_priority : Prop
  nonaccidental_connection : Prop
```

```lean
inductive ImmediateAIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m) :
    Term -> Term -> Prop
  | mk :
      science.TrueIn (Categorical.A lower upper) ->
      (forall middle : Term,
        middle ∈ science.subjectMatter ->
        science.TrueIn (Categorical.A lower middle) ->
        science.TrueIn (Categorical.A middle upper) ->
        middle = lower \/ middle = upper) ->
      ImmediateAIn science lower upper
```

```lean
def ImmediateIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m) (prop : Categorical) : Prop :=
  match prop with
  | .A lower upper => ImmediateAIn science lower upper
  | .E _ _ => NegativeImmediateIn science prop
  | .I _ _ => False
  | .O _ _ => False
```

```lean
inductive DemonstrativeExpansionIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m) :
    Categorical -> Categorical -> Prop
  | barbaraMajor ...
  | barbaraMinor ...
  | celarentMajor ...
  | cesareMajor ...
  | camestresMinor ...
```

```lean
def ExpansionReachableIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m) :
    Categorical -> Categorical -> Prop :=
  Relation.TransGen (DemonstrativeExpansionIn science)
```

```lean
def NonReciprocalIn {Model : Type} [Interpretation Model]
    {m : Model} (science : Science Model m)
    (premises : List Categorical) (conclusion : Categorical) : Prop :=
  science.TrueIn conclusion /\
    forall premise : Categorical,
      premise ∈ premises ->
      science.TrueIn premise ->
      ¬ ExpansionReachableIn science conclusion premise
```

```lean
structure Demonstration (Model : Type) [Interpretation Model]
    {m : Model} (science : Science Model m) where
  figured : FiguredSyllogism
  conclusion_admissible : science.admits figured.conclusion
  major_principle : Nous science figured.majorPremise
  minor_principle : Nous science figured.minorPremise
  nonreciprocal :
    NonReciprocalIn science [figured.majorPremise, figured.minorPremise] figured.conclusion
  middle_explains :
    MiddleExplainsIn science figured.minor figured.middle figured.major
```

These signatures intentionally do not settle every historical detail. They do
settle three architectural points:

- demonstration talks about explanation, not only derivability
- immediacy is primarily middle-sensitive
- reciprocity is blocked at the level of demonstrative expansion, not only
  singleton-premise derivation

### Theorem Inventory For Tranche B

1. Explanatory middle interface theorems.

- `MiddleExplainsIn.middle_in_science`
- `MiddleExplainsIn.minor_premise_true`
- `MiddleExplainsIn.major_premise_true`
- `MiddleExplainsIn.not_vacuous`

2. A-immediacy theorems.

- `ImmediateAIn.trueIn`
- `ImmediateAIn.no_distinct_middle`
- `immediateAIn_of_no_nontrivial_middle`
- `not_immediateAIn_of_distinct_middle`

3. Expansion and reciprocity theorems.

- `expansionReachableIn.refl_or_step`
- `nonreciprocalIn_noncircular`
- `nonreciprocalIn_blocks_premise_return`
- `not_nonreciprocalIn_of_expansion_cycle`

4. Demonstration theorems.

- `Demonstration.premisesTrueIn`
- `Demonstration.firstPrinciples`
- `Demonstration.noncircular`
- `Demonstration.conclusion_trueIn`
- `Demonstration.conclusion_not_immediate`
- `Demonstration.valid_but_not_demonstrative` for an example-level separation

5. Negative-route bridge theorems.

- `negativeImmediateIn_of_no_admissible_negative_route`
- `negativeRoute_expansion_sound`
- `negative_route_reciprocity_blocked`

The route theorems can be added in a second pass if the first pass lands only
the A-proposition case. The plan should still state them now so the shape of the
Smith layer does not quietly regress into proposition-atomic underivability.

### Migration Sequence For Tranche B

1. Add `MiddleExplainsIn` and `NonReciprocalIn` alongside the current
   `IsCauseOf` and `NonReciprocal`.
2. Refactor `Demonstration` to use the stronger interfaces while preserving
   theorem names through aliases where practical.
3. Rebuild `Examples/Demonstration.lean` so one example is merely a valid
   syllogism and one is a genuine demonstration.
4. Replace or deprecate the old one-step `NonReciprocal`.
5. Extend immediacy from the A-case to the negative-route case over
   `Chains.lean` and `Regress.lean`.

### Explicit Non-Goals For Tranche B

- Do not expand the proof theory beyond the four universal moods merely to make
  the demonstration layer look richer.
- Do not define explanatory priority by a trivial inhabited field or an empty
  class instance.
- Do not identify immediacy with generic underivability from arbitrary lists of
  premises.
- Do not force the route-expansion machinery to prove more than the current
  source reconstruction supports.

## Tranche C: Truth In Thought And Downstream Repair

### Focus

- Repair the D7 layer and keep downstream metaphysics and physics from reintroducing collapsed distinctions.

### File Targets

- `Philosophy/Aristotle/SensesOfBeing.lean`
- `Philosophy/Aristotle/PhysicsI.lean`
- `Philosophy/Aristotle/PhysicsII_Causes.lean`

### Required Changes

1. Split ontological being from truth-in-thought.

- Keep `BeingProfile` for categorial, accidental, and modal being.
- Introduce a thought-side layer for truth and falsity.
- Replace the current anti-realistic-looking condition with a claim that truth belongs to thought without forbidding true thought about separate beings.

2. Keep Reading B stable.

- Do not let the definition refactor leak into a Reading A decomposition of `Physics I`.
- Preserve the current articulation model in `PhysicsI.lean`.

3. Preserve local causal coincidence only.

- Keep `PhysicsII_Causes.lean` local and non-reductive.
- If the new explanatory middle layer suggests stronger causal interfaces, expose them only as optional bridges.

### Acceptance Criteria

- `SensesOfBeing.lean` no longer encodes truth-as-thought by banning true thought of separate beings.
- No new global cause-reduction infrastructure is introduced.

### Target Signatures For Tranche C

The D7 repair should separate ontological profiling from truth-bearing thought
without losing the existing cross-cutting modal and accidental axes.

```lean
structure BeingProfile where
  accidentality : Accidentality
  categorial : Option Category
  modal : ActualityStatus
  perSe_has_category :
    accidentality = Accidentality.perSe -> exists category, categorial = some category
```

```lean
class OntologicalBeing (B : Type) [FirstPhilosophy B] [Causality B] where
  profile : B -> BeingProfile
  no_cause_for_accidens :
    forall {b : B},
      (profile b).accidentality = Accidentality.perAccidens ->
        ¬ exists c : B, Causality.explains c ((profile b).accidentality = Accidentality.perAccidens)
```

```lean
class ThoughtReference (B Thought : Type) where
  concerns : Thought -> B -> Prop
```

```lean
class TruthInThought (Thought : Type) where
  trueThought : Thought -> Prop
  falseThought : Thought -> Prop
  not_both : forall {thought : Thought}, ¬ (trueThought thought /\ falseThought thought)
```

```lean
structure TrueThoughtAbout (B Thought : Type)
    [ThoughtReference B Thought] [TruthInThought Thought] where
  thought : Thought
  object : B
  concerns_object : ThoughtReference.concerns thought object
  is_true : TruthInThought.trueThought thought
```

```lean
class PathToPrinciples (Item : Type) where
  confusedDescription : Item -> PrincipleDescription Item
  articulate : PrincipleDescription Item -> PrincipleDescription Item
  preserves_principle : ...
  starts_confused : ...
  articulate_sharpens : ...
```

```lean
structure LocalCausalAlignment (Entity : Type) [CausalRoles Entity] where
  formal : CausalRoles.formal (Entity := Entity)
  efficient? : Option (CausalRoles.efficient (Entity := Entity)) := none
  final? : Option (CausalRoles.final (Entity := Entity)) := none
  efficient_aligns : ...
  final_aligns : ...
```

These target shapes keep the current Reading B and local-cause work intact while
removing the misleading implication that true thought cannot concern separate
beings.

### Theorem Inventory For Tranche C

1. Ontological being theorems.

- `OntologicalBeing.perSe_has_category`
- `OntologicalBeing.dismiss_accidens_from_science`
- `perSe_not_flat_enum`

2. Truth-in-thought theorems.

- `TruthInThought.not_both_true_false`
- `TrueThoughtAbout.concerns_object`
- `TrueThoughtAbout.is_true`
- `trueThought_can_concern_separate_being`

3. Bridge theorems between the two layers.

- `truth_is_not_a_categorial_mode`
- `truth_is_not_a_modal_status`
- `truth_in_thought_preserves_real_reference`

4. Reading B stability theorems.

- `articulate_preserves_principle`
- `confused_description_starts_confused`
- `articulation_not_decomposition`

5. Local causal alignment theorems.

- `efficientCoincidesLocally_of_alignment`
- `finalCoincidesLocally_of_alignment`
- `local_alignment_not_global_reduction`

The goal is not to prove every philosophical thesis in one pass. The goal is to
make it impossible for the infrastructure itself to encode the wrong thesis.

### Migration Sequence For Tranche C

1. Introduce `OntologicalBeing`, `ThoughtReference`, and `TruthInThought`
   alongside the current `BeingSenses`.
2. Refactor `SensesOfBeing.lean` theorem statements to target the split classes.
3. Replace the current `dismiss_truth_from_first_philosophy` theorem with a
   theorem stating that truth belongs to thought while still permitting
   `TrueThoughtAbout` separate beings.
4. Keep `PhysicsI.lean` unchanged except for compatibility or comments unless
   the D7 refactor exposes a genuine interface mismatch.
5. Preserve `PhysicsII_Causes.lean` as local coincidence only; add bridge lemmas
   rather than stronger global classes if explanatory-middle work requests them.

### Explicit Non-Goals For Tranche C

- Do not rebuild `SensesOfBeing.lean` as a flat enumeration of “senses”.
- Do not encode truth-in-thought by denying that thought can concern real
  separate beings.
- Do not let `PhysicsI.lean` drift back toward Reading A decomposition APIs.
- Do not turn local cause coincidence into a global reduction theorem.

## Compatibility And Migration Rules

- Keep `Philosophy/Aristotle.lean` as the public root import.
- Introduce new canonical names before removing old ones.
- Use thin compatibility facades only after the new API is stable.
- Do not push Mennian distinctions down into `PriorAnalytics/Syntax.lean`.
- Do not use examples as the only home of structure needed by the library.

## Validation

- Rebuild `Philosophy.Aristotle`.
- Rebuild `Philosophy`.
- Treat `Examples/Dialectic.lean` and `Examples/Demonstration.lean` as regression tests over the public API.
- Prefer theorem-backed examples over one-off witnesses.

## Order Of Execution

1. `docs-constitution`
2. `definitional-phrase`
3. `substance-rank-split`
4. `dialectic-definition-upgrade`
5. `explanatory-middle`
6. `smith-reciprocity`
7. `truth-in-thought`
8. `example-regressions`

## First Implementation Sprint

The first actual coding pass should stay entirely inside Tranche A and should be
small enough to keep the library buildable after each step.

### Sprint 1

- Update `ARCHITECTURE.md`, `SOURCE_MAP.md`, and `GLOSSARY.md` with the
  non-collapse constitution.
- Add `DefinitionalPhrase` and `ScreenedDefinitionalPhrase`.
- Do not yet rewrite every example.

Success condition:
- the docs no longer overstate definition completeness
- the new definition-side objects exist in the core API
- the build still passes

### Sprint 2

- Add `PrimarySubstanceMarks`, `SecondarySubstanceMarks`, and `SubstanceRank`.
- Provide compatibility lemmas from the old recognition predicates.
- Add one secondary-substance regression example.

Success condition:
- secondaries no longer inherit `signifiesThis`
- existing code still imports through the public root

### Sprint 3

- Change `Problem.definition` to use `DefinitionalPhrase`
- add the new definition diagnoses
- migrate `Examples/Dialectic.lean` to the structured definition path

Success condition:
- `Expression.combined` or equivalent structured definitional content has a live
  path through the staged dialectic
- at least one genus-plus-differentia example is checked by theorem

Only after these three sprints should the refactor move into `PosteriorAnalytics`.

## Done Condition

- A definition is a structured object, not a disguised term.
- Dialectical and scientific definition are distinct.
- Secondary substance is formalized without inherited thisness.
- Demonstration requires explanatory middle, not just validity.
- Immediacy and non-reciprocity are stronger than singleton-premise underivability.
- D7 truth is placed on the thought side without anti-realist drift.
