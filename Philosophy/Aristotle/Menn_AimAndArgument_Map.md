# Menn: *Aim and Argument* (manuscript) and this repository

This note is the **integration anchor** for Stephen Menn’s book-length study *The Aim
and the Argument of Aristotle’s Metaphysics* (cited throughout `AOMSB1.md` and
related Menn texts as e.g. “Ig1b”, “IIg1b”). The repository holds **PDF segments**
named by Menn’s internal chapter codes (not Aristotle’s books), for example:

| PDF pattern (in `Philosophy/Aristotle/`) | Role in Menn’s cross-references (typical) |
| --- | --- |
| `Ia*.pdf`, `Ia*App*.pdf` | Part I: Physics / path to principles (e.g. Physics I.1 “Reading B”) — **see also** `Path to Principles.md` |
| `Ib*.pdf` | Part I: further Aristotelian background used in the book’s argument |
| `Ig*.pdf` | Part I: Metaphysics-centred threads (D, causes, *stoiceia*, etc.); **AOMSB1** footnotes *Aim and Argument* “Ig1b” for the status and aims of **Book D** |
| `IIa*.pdf`, `IIb*.pdf`, `IId.pdf`, `IIg*.pdf` | Part II of the book (larger continuous argument; the `g` segments track *Metaphysics* “leads” in Menn’s layout) |
| `IIIa2.pdf` | Part III segment present in-repo |

The **Lean development does not** reproduce Menn’s whole book, the disputed order
of **ABΓΔ**…**Ν**, or a line-by-line walk of **EZHQ**. It **does** try to respect
Menn’s **separation of problems** in the *places the code touches*.

---

## What Menn requires one *not* to conflate (non-negotiable)

1. **Causes of being qua being (Γ, E) vs physics’ natural *archai* (Physics I, etc.)**  
   The science of *being qua being* and *causes to things of their being* (AOMSB1 /
   Γ1–2 / E1 style motivation) is **not** the same project as the confused→articulate
   **principle-descriptions** of Physics I.1 “Reading B” (Menn, *Path to
   Principles*). The repo enforces the split by putting Reading B in
   `PhysicsI.lean` and any **cross-tie only** in `MennAlignment.lean` **as
   pointer and order on `DescriptionStage`**, not as a reduction of metaphysics
   to physics.

2. **D7’s four “senses of being” vs a single `being` predicate**  
   Menn reads D7 as the **scaffolding for EZHQ**: peel per-accidens and (one kind
   of) truth, then categorial *ousia* (Z/H), then *dunamis* / *energeia* (Θ), then
   truth of simples (Θ10). The code’s **non-collapse** of axes is in
   `SensesOfBeing.lean` (`BeingProfile` + `BeingSenses` + truth in *thought*).
   That is **one honest fragment** of that programme—not a model of the whole
   *Metaphysics*.

3. **Dialectic / *Categories* vs first philosophy**  
   Menn (“Metaphysics, Dialectic, and the Categories” line of thought, cited in
   AOMSB1) resists running **causal, first-philosophical** machinery on what the
   *Categories* and *Topics* are doing. Here, **dialectic** and **staged
   `Problem`s** live in `DialecticStaged.lean` / `Categories.lean` with
   `InquiryBoundary.lean` keeping **whether**-inquiry and **why**-science apart.

4. **ἀρχή* / *aition* / *stoiceion* (Δ1 / Δ3)**  
   AOMSB1 stresses that *stoiceion*-as-constituent and *arche* in the wider
   **cause**-sense must not be merged or one will “discover” the wrong
   *archai* of *all* beings. The **Physics** hylomorphic *Generation* + principle
   descriptions in `PhysicsI.lean` are a **toy hylomorphism layer**, not a
   full Δ1–3 lexicon in Lean; treating them as a complete “Metaphysics Δ” layer
   would be a **false friend**.

5. **Posterior Analytics: existence vs what-it-is, and demonstration**  
   Menn’s *Path to Principles* and AOMSB1’s use of APo. **II** and **I 13** (*hoti*
   / *dioti*) are only partially mirrored: `InquiryBoundary.lean` and
   `PosteriorAnalytics` carry **Smith**-governed *WhyQuestion* / *Demonstrative*
   structure; this is **parallel in role**, not a duplicate of
   *DescriptionStage* or D7 *being*.

---

## Audit: what is **adequately** Menn-respecting in the Lean

| Menn thread | Main Lean home | Verdict |
| --- | --- | --- |
| Physics I.1 Reading B; *same* *arche* under confused vs articulate | `PathToPrinciples` + `MennAlignment` order + bot/top lemmas | **Good fit** (explicit axioms, no spurious decomposion into “parts”) |
| Do not conflate *hoti* problem with *dioti* / re-asked *why* | `InquiryBoundary.lean` | **Good fit** (aim-typed) |
| D7 multi-axis being; truth as affection of *thought*; incomposite being not flattened | `SensesOfBeing.lean` + `Examples/Metaphysics.lean` | **Partial**—schema + demo only; no full *per accidens* or *Dunamis* text layer |
| Dialectic / surface traps / genus-definition dossiers (Menn-Topics line) | `DialecticStaged.lean` / `Categories.lean` | **Strong** relative to the Topics commentary sources |
| *Stoiceion* / *arche* distinction (Δ) as live structural constraint | **Not** a dedicated **Δ-lexicon** module; only informal pointers | **Gap** (acceptable only if not claimed) |

---

## Harsh lessons (if one claimed “Menn is done in Lean”)

- **“We formalized the *Metaphysics*”** — false. The repo has **patches** (D7
  *senses*, examples, boundary theorems) aligned with Menn’s *reading* of
  *passages*, not the whole moving **argument* of ABΓE…Ν** in Menn’s sense.
- **“Reading B = the path to the causes of being qua being”** — false. That
  conflates the Physics **methodological** *hodos* with Γ/E **science
  of being** (see *Aim* programme + AOMSB1 on causes *to* beings *of* their
  *being*).
- **Conflating `DescriptionStage` with an `InquiryAim` or a `BeingSenses` axis** —
  would be exactly the sort of flattening Menn and Aristotle in D7 are trying
  to *avoid*.

---

## Suggested use

- **Human reading**: work through the `I*`, `II*`, `IIIa2` PDFs alongside
  `AOMSB1.md` and *Path to Principles*; use this file to see which **formal
  modules** correspond to which **Menn theses**—and where the formalization is
  silent.
- **Lean work**: add **new** Menn-interpretive *content* in the **module
  that already holds the right Aristotelian *role***, and use `MennAlignment.lean`
  only for *explicit cross-wires* and documentation, not a second metaphysics.
