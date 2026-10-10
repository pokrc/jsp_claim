# Justin Sun Prize — first-formalization opportunity audit (2026-10-10)

**Status:** preliminary, evidence-backed target selection. **No qualifying complete Lean formalization is produced by this audit.** It is not an award submission and does not assert worldwide originality, eligibility, or verified priority.

## The selection gate

The current official [contribution requirements](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md) and [award process](https://github.com/TheJustinSunPrize/awards/blob/main/docs/award-process.md) require the *whole original problem* to have a reviewed mathematical solution and a *matching complete* Lean proof. The formalization must be attributable to the applicant, fixed at an original 40-hex Git commit, kernel checked without `sorry` or unproved assumptions, and independently verified by the maintainers. An earlier verified complete proof may have priority even if the official catalog still says `Lean proof: No`. The PR opening time does not decide precedence. A merged PR is not by itself a prize.

## Best presently identified gap — JSP-000900 (candidate, NOT claimed)

**Question:** For every integer d ≥ 3, does every n-point set in real d-space determine at least c_d n^(2/d) different distances, for a constant c_d > 0 independent of n and the particular point set?

- [Official JSP-000900 entry](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000900): `Solved`, `Lean proof: No`, `Eligible to claim: No` at inspection.
- [Source paper, OpenAI, 2026-09-23](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-higher-dimensional-Erdos-distinct-distances-conjecture-September-23-2026/paper.pdf); [exact introduction/Theorem 1 statement in LaTeX](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-higher-dimensional-Erdos-distinct-distances-conjecture-September-23-2026/build/sections/introduction.tex). The source asserts a solution for each fixed d ≥ 3 and every n ≥ 2, without extra geometric hypotheses. The catalog explicitly says **independent mathematical review has not been performed**. This is a material uncertainty, not a technicality.
- GitHub official repository history: [#3371](https://github.com/TheJustinSunPrize/awards/pull/3371) was **closed, unmerged**, and points at `plby/lean-proofs/Erdos900.lean`. On direct source inspection, the file actually proves **Ajtai–Komlós–Szemerédi's random-graph long-path problem** (Erdős problem #900 on erdosproblems.com); it is **not** a higher-dimensional Euclidean distinct-distance proof. The official JSP number and the original Erdős website problem number are **not interchangeable**.
- [#2502](https://github.com/TheJustinSunPrize/awards/pull/2502) was **closed, unmerged**, and explicitly labels its proposed theorem a small-case scoped component, **not** the complete original theorem.
- Searches of the exact official JSP number, target/topic PR wording, relevant GitHub repositories and public code did not identify a *qualifying* complete prior Lean solution **at the time checked**. This is **absence of evidence within searched sources**, not proof of worldwide absence or first priority.
- **Technical difficulty: extreme.** The paper's main argument includes multiscale algebraic concentration, higher-dimensional rigidity/motion counting, Hilbert functions, sparse cones, polynomial geometry, and real incidence estimates. It is substantially beyond a short Lean exercise; a one-line theorem, finite examples, a lemma-only repo, or importing the target as an axiom does not qualify.

**Exact mathematical target (review specification, not a compiled Lean declaration):**

For all natural d ≥ 3, there exists a positive real c such that for all finite sets P ⊆ (Fin d → ℝ) with 2 ≤ |P|, if Δ(P) := {dist(x,y) : x,y ∈ P and x ≠ y}, then

`c * (|P| : ℝ) ^ ((2 : ℝ) / (d : ℝ)) ≤ (|Δ(P)| : ℝ).`

The intended distance is Euclidean (not sup norm), distinct **nonzero distances** are counted exactly once, P has distinct points, and c can depend on d but on neither |P| nor P. Do not allow 0 cardinality / an empty index type / a false hypothesis to make the problem vacuous.

Before submitting anything official: have the **whole source mathematics independently reviewed**; build a Lean statement matching this exact target; prove all required auxiliary results; verify all transitive axioms; audit every parameter, distance definition, and comparator; search external proof archives *again* immediately before the selected commit and PR.

## Rejected or highly contested targets

| JSP | Official status may be `Solved / Lean No` | Reason *not* to prioritize |
| --- | --- | --- |
| [000027](https://github.com/TheJustinSunPrize/awards/pull/4970) | Solved / No | Earlier specifically named complete formalization claim by @cadamcat, PR #4970, with public pinned repository/commit; math preprint also awaits independent review |
| [000168](https://github.com/TheJustinSunPrize/awards/pull/4966) | Solved / No | Earlier specifically named complete finite sums-and-products formalization claim by @cadamcat, PR #4966, with public pinned repository/commit |
| [000175](https://github.com/TheJustinSunPrize/awards/pull/4967) | Solved / No | Earlier specifically named complete hypercube Ramsey formalization claim by @cadamcat, PR #4967, with public pinned repository/commit |
| [000208](https://github.com/TheJustinSunPrize/awards/pull/3918) | Solved / No | Earlier substantial full-source Hooley-gap Lean proof in `plby/lean-proofs/src/latest/ErdosProblems/Erdos235.lean` (exact theorem `Erdos235.erdos_235`), 4278 lines, direct source inspection |
| [000267](https://github.com/TheJustinSunPrize/awards/pull/1267) | Solved / No | Earlier complete asymptotic Lean proof `plby/lean-proofs/src/latest/ErdosProblems/Erdos321.lean` importing `FinalAsymptotic`, directly checked |
| [000402](https://github.com/TheJustinSunPrize/awards/pull/3962) | Solved / No | Earlier complete independence formalization `elliotglazer/erdos501`, re-exported by `plby/lean-proofs/Erdos501.lean`; direct file inspection |
| [000419](https://github.com/TheJustinSunPrize/awards/pull/3969) | Solved / No | Earlier substantial Lean proof of random-sign polynomial maximum `Erdos523.erdos_523` (6417 lines) in `plby/lean-proofs`, direct file inspection |
| [000690](https://github.com/TheJustinSunPrize/awards/pull/1947) | Solved / No | Many separate earlier exact finite-chromatic-critical hypergraph certificates, including #1947, #4703, #747, #1895; 9-vertex/22-edge construction already formalized |
| [000698](https://github.com/TheJustinSunPrize/awards/pull/484) | Solved / No | Earlier purported **complete** cycle-plus-triangles 3-coloring Lean proof; multiple competitor entries; need independent audit before any priority claim |
| [001018](https://github.com/TheJustinSunPrize/awards/pull/723) | Solved / No | Earlier proposed complete bounded-gap equal-block-sums theorem; substantial competition |
| [000514](https://github.com/TheJustinSunPrize/awards/pull/4006) | Solved / No | Published classification, but much earlier disputed and source-backed formalization activity; even obvious `sorry` scaffolds are not qualifying, though other entrants claim more; expensive to establish priority |

The linked third-party sources are **evidence of prior claims and substantial prior work**. Their complete correspondence, trust audit and priority have **not all been independently reproduced here**. Therefore this list distinguishes "too risky to invest given earlier public evidence" from a formal referee finding of an already accepted valid first proof.

## Research plan if pursuing #000900

1. Obtain independent mathematical review of the precise 2026-09-23 paper, including all cited analytic/algebraic lemmas and hidden hypotheses. Mark issues with exact theorem/section/page references.
2. Check Mathlib's metric, Euclidean-space, polynomial, incidence/variety and finite-set APIs; inventory missing libraries and prove an exact statement equivalence to the published theorem. Review pathological edge cases.
3. Formalize the paper in a **new, original proof library** in independent modules. No `sorry`, `admit`, `axiom` used to assert unresolved mathematical content, or importing the final theorem from a competitor's proof under a new name.
4. Prove the full theorem without swapping to exponent `2/d - ε`, finite dimensions only, generic-position assumptions, or an `n`-dependent c.
5. Exact-SHA `lake build`, `#print axioms`, structural audit, independent check, authorship evidence, and public immutable priority timestamp; run renewed prior-source searches before claiming first priority.
6. Only after the full proof and source are demonstrably complete: propose catalog-only official PR with mathematics, exact Lean theorem name, full original proof SHA and reproduction evidence. Claim issue follows the official merged-PR process.

## Distinction between open targets and prize-winning strategy

"First viable-looking gap" is **not** "first successfully verified formalizer." The source proof of #900 itself is under independent mathematical review and its Lean formalization is extremely difficult. A quick speculative official PR with only a statement would **not** improve priority and could misrepresent the project. Continue screening for smaller solved theorems with a defensible attribution trail and no earlier complete proof.

**Authoring attribution:** Screening notes and source comparison prepared for `pokrc`; citations remain owned by their respective authors. No award, solution, or original-formalizer authorship claim is made here.


## Verified kernel development (new research branch, 2026-10-10)

The following statements are proven **as specifically scoped** (not equivalent to the full conjecture). GitHub Actions `lake build` and the extended `ProofAudit.lean` must both succeed at the selected source SHA to count them as kernel verified.

| Source | Concrete statement |
| --- | --- |
| `JspClaim/JSP000900_Statement.lean` | Exact main proposition represented as **definition only**; no theorem of type `OriginalQuestion` |
| `JspClaim/JSP000900_Radial.lean` | For distance-injective anchor p, `|Δ(P)| ≥ |P|-1`; two distinct points determine a distance |
| `JspClaim/JSP000900_OneDimensional.lean` | Complete and unconditional **one-dimensional** result `|Δ(P)| ≥ |P|-1` for finite nonempty `P⊆ℝ` |
| `JspClaim/JSP000900_ConditionalRate.lean` | All d≥3: `|Δ(P)| ≥ (1/2)|P|^(2/d)` **assuming an anchor with injective radial distances** |
| `JspClaim/JSP000900_DistanceProfiles.lean` | Theorem `|P| ≤ (|Δ(P)|+1)^k` if k anchors in P **separate all points by distance profiles**; distinct-distance monotonicity for subsets; exclusion of zero |

### Actual full-proof dependencies still open

The [source paper's reduction section](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-higher-dimensional-Erdos-distinct-distances-conjecture-September-23-2026/build/sections/reduction.tex) explicitly derives its final contradiction from three non-elementary results: the **sparse-cones theorem**, a **rich-motion theorem**, and a **uniform algebraic concentration theorem**. The source also contains substantial auxiliary arguments:

- [Polynomial interpolation and multiplicity](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-higher-dimensional-Erdos-distinct-distances-conjecture-September-23-2026/build/sections/polynomial.tex): Hilbert-function ranks, regular component equations, interpolation at isolated points, intersection multiplicities and projection bounds
- [Secants and terminal curves](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-higher-dimensional-Erdos-distinct-distances-conjecture-September-23-2026/build/sections/secants.tex): finite and generic secant/projection statements
- [Multiscale profiles](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-higher-dimensional-Erdos-distinct-distances-conjecture-September-23-2026/build/sections/profiles.tex): scale-window partitioning and polynomial rank propagation
- [Sparse-cones proof](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-higher-dimensional-Erdos-distinct-distances-conjecture-September-23-2026/build/sections/sparse-cones.tex): contradiction to sparse directional coverings
- [Incidence estimates](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-higher-dimensional-Erdos-distinct-distances-conjecture-September-23-2026/build/sections/classical-incidence.tex): real and complex polynomial geometry tools

No Lean files in this research branch prove those three top-level inputs or the main unconditional statement. Importing these as fresh `axiom` declarations, stipulating a general-position hypothesis, or replacing the exponent by a weaker bound would not meet contest rules. Independent review of the source paper remains outstanding.
