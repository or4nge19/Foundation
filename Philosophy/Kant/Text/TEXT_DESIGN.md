# Text Layer Design Principles

## Sentence-to-Formalization

Each sentence or claim made by Kant in the source texts maps to **one** formal proposition. No duplication.

- **One definition per Kantian concept**: e.g. `CategoryOfRelation` and `relationFormToCategory` live in `Categories.lean`; `MetaphysicalDeduction` imports and extends.
- **One predicate per Kantian claim**: e.g. `AllAppearancesAreInTime` (A34/B50); `AllSchemataAreTemporal` (B177).
- **Avoid redundant aliases**: if two predicates are provably equivalent, keep one and cite the Kant passage in its docstring.

## Canonical Sources

| Kant content | Canonical file |
|--------------|----------------|
| Relation categories, relationFormToCategory | `Categories.lean` |
| Full category table (Quantity, Quality, Relation, Modality) | `MetaphysicalDeduction.lean` |
| Unity of apperception, lawful synthesis | `Apperception.lean`, `Synthesis.lean` |
| Objective validity, conditions of possible experience | `Objectivity.lean` |
| Space/time as forms of sensibility | `CPR/Aesthetic.lean` |
| Three syntheses | `CPR/Analytic/TranscendentalDeductionA.lean` |
| Objective unity of apperception | `CPR/Analytic/TranscendentalDeductionB.lean` |
| Schemata as time-determinations | `CPR/Analytic/Schematism.lean` |
| System of Principles | `CPR/Analytic/Principles.lean` |
| Phenomena and noumena | `CPR/Analytic/PhenomenaNoumena.lean` |
| Introduction (synthetic a priori) | `CPR/Introduction.lean` |

## Docstrings

Each definition carries a docstring citing the relevant Kant passage (e.g. A20/B34, B131, B177) so that the formalization is traceable to the text.
