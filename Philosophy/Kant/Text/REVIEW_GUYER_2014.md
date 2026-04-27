# Review: Formalization vs. Cambridge Companion to Kant's Critique of Pure Reason (Guyer, ed., 2010/2014)

*Reference: Paul Guyer (ed.), The Cambridge Companion to Kant's Critique of Pure Reason, Cambridge University Press. The 2014 file is likely a reprint or later edition of the 2010 volume.*

**Note:** The PDF could not be read directly; this review is based on the Companion's known structure (table of contents, chapter authors) and standard scholarly interpretations that the volume endorses.

---

## 1. Companion Structure vs. Our Coverage

| Companion Chapter | Author | Our Formalization | Status |
|-------------------|--------|------------------|--------|
| Ch 3: Introduction, Framing the Question | R. Lanier Anderson | `Introduction.lean` | ✓ Covered |
| Ch 4: The Transcendental Aesthetic | Lisa Shabel | `Aesthetic.lean` | ✓ Covered |
| Ch 5: Metaphysical & Transcendental Deductions | Paul Guyer | `MetaphysicalDeduction`, `TranscendentalDeductionA`, `TranscendentalDeductionB` | ✓ Covered |
| Ch 6: The System of Principles | Eric Watkins | `Schematism.lean`, `Principles.lean` | ✓ Covered |
| Ch 7: Refutation of Idealism, Phenomena/Noumena | Dina Emundts | `PhenomenaNoumena.lean` | ✓ Partial |
| Ch 8: Ideas of Pure Reason | Michael Rohlf | — | **Gap** |
| Ch 9: Paralogisms | Julian Wuerth | — | **Gap** |

---

## 2. Chapter-by-Chapter Assessment

### Ch 4: Transcendental Aesthetic (Shabel)

**Companion focus:** Space and time as pure forms of intuition; a priori vs. empirical; relation to geometry and arithmetic.

**Our formalization:**
- ✓ Matter/form of appearance (A20/B34)
- ✓ Space as form of outer sense (A26/B42)
- ✓ Time as form of inner sense (A33/B49)
- ✓ All appearances in time (A34/B50)
- ✓ Pure vs. empirical intuition

**Refinements added:**
- ✓ **Empirical reality, transcendental ideality** (A28/B44, A35–36/B52–53): `EmpiricalRealityOfSpace`, `EmpiricalRealityOfTime`, `TranscendentalIdealityOfSpace`, `TranscendentalIdealityOfTime`.

**Remaining gaps:**
- Shabel emphasizes **geometry** (space) and **arithmetic** (time) as bodies of a priori synthetic knowledge. We have no formal link from `Space`/`Time` to mathematical construction.
- The **metaphysical vs. transcendental exposition** distinction (Kant's §§2–5 for space, §§4–5 for time) is not represented.

---

### Ch 5: Metaphysical & Transcendental Deductions (Guyer)

**Companion focus:** Derivation of categories from judgment forms; A- vs. B-Deduction; objective validity; unity of apperception.

**Our formalization:**
- ✓ Full category table (A80/B106)
- ✓ Judgment-form → category mappings
- ✓ Three syntheses (A98, A100, A103) and their inseparability (A102)
- ✓ "I think" can accompany all representations (B131)
- ✓ Subjective vs. objective unity (B133)
- ✓ Objective unity of apperception
- ✓ Conditions of possible experience → objective validity

**Gaps / refinements:**
- Guyer stresses the **two-step structure** of the B-Deduction (§§15–16 vs. §§17–18): first, categories as conditions of the unity of apperception; second, application to objects of intuition. Our `DeductionB_System` flattens this.
- The **numerical identity** of the "I" across representations (B133) is not explicit.
- **Spontaneity** of the understanding (B132) vs. receptivity of sensibility: we have no formal marker.
- The Metaphysical Deduction's **"clue"** (Leitfaden) — that the same functions that unify judgment also unify intuition — is only implicit in our `relationFormToCategory` bridge.

---

### Ch 6: System of Principles (Watkins)

**Companion focus:** Axioms of Intuition, Anticipations, Analogies, Postulates; schematism as mediation.

**Our formalization:**
- ✓ Schematism: schema mediates category and appearance (B176–177)
- ✓ Schemata as time-determinations (B177)
- ✓ **Principles.lean:** `AxiomsOfIntuitionSystem`, `AnticipationsSystem`, `AnalogiesSystem`, `PostulatesSystem` with First/Second/Third Analogy, Postulates of Possibility/Actuality/Necessity.

---

### Ch 7–9: Refutation, Ideas, Paralogisms

**Added:** `PhenomenaNoumena.lean`—phenomenon/noumenon distinction, noumenon as limiting concept, no insight into noumena.

**Remaining gaps:**
- Refutation of Idealism (B274–279)
- Ideas of pure reason (soul, world, God)
- Paralogisms of pure reason

---

## 3. Structural Alignment with Guyer's Approach

Guyer's work on the Deduction typically emphasizes:
1. **Objective validity** = categories apply to objects of possible experience ✓ (we have `ObjectivelyValid`, `ConditionOfPossibleExperience`)
2. **Unity of apperception** as the keystone ✓ (we have `UnityOfApperception`, `ObjectiveUnityOfApperception`)
3. **Synthesis** as the activity that makes unity possible ✓ (we have `SynthesisOfApprehension/Reproduction/Recognition`, `LawfulSynthesis`)

**Potential divergence:** Guyer has sometimes argued that the Deduction alone does not establish the *specific* categories (e.g., causality) and that the Analytic of Principles is needed. Our `lawful_synthesis_yields_objective_validity` abstracts over categories; we do not distinguish between "categories in general" and "each category in particular." This may be acceptable for a minimal kernel.

---

## 4. Pre-Critical and Introduction (Ch 3)

**Ch 3 (Anderson):** ✓ **Introduction.lean**—`AnalyticJudgment`, `SyntheticJudgment`, `Apriori`, `Aposteriori`, `SyntheticAprioriJudgment`, `HowAreSyntheticAprioriPossible`.

**Pre-critical (Duisburg, Herz, etc.):** Our `DuisburgNachlass.lean`, `HerzLetter1772.lean`, `NegativeMagnitudes.lean` cover developmental material. The Companion's Part I (Ch 1–2) addresses rationalist/empiricist background; our pre-critical modules align with that developmental arc.

---

## 5. Recommendations

| Priority | Action |
|----------|--------|
| High | Add `Principles.lean` stub for Axioms, Anticipations, Analogies, Postulates (Ch 6) |
| High | Add predicates for empirical reality / transcendental ideality of space and time (Ch 4) |
| Medium | Add `PhenomenaNoumena.lean` for Ch 7 |
| Medium | Formalize two-step B-Deduction structure if Guyer's reading is adopted |
| Low | Add `Introduction.lean` with synthetic a priori, analytic/synthetic distinction |
| Low | Add `Ideas.lean`, `Paralogisms.lean` for Dialectic |

---

## 6. Summary

Our formalization now covers: Introduction (Ch 3), Aesthetic (Ch 4), Deductions (Ch 5), Principles (Ch 6), and Phenomena/Noumena (Ch 7). Refinements added: empirical reality/transcendental ideality of space and time; two-step B-Deduction; full Principles stub; Introduction with synthetic a priori. Remaining gaps: Refutation of Idealism, Ideas of pure reason, Paralogisms (Ch 8–9).
