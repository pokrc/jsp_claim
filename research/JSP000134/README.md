# JSP-000134 / Erdős #128 — finite-case research

**Status: research / partial mathematical coverage. NOT a prize-ready proof.**

Original question: [Erdős problem 128](https://www.erdosproblems.com/128).
Official catalog: [JSP-000134](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000134).

## Exact question and quantifiers

Given a finite simple undirected graph on `n` vertices, assume that **every
induced subgraph on at least half the vertices**, represented by the
Formal Conjectures threshold `2 * |S| + 1 >= n`, has strictly more than
`n² / 50` edges. Must the graph contain a triangle?

The unrestricted question is OPEN. Neither the present source nor its author
claims to settle that question. In particular, the 2025 public attempt at
Erdős 128 that used `2 * |S| >= n` instead of `2 * |S| + 1 >= n`
encountered an artificial 5-cycle counterexample caused by that changed
rounding. The distinction matters for odd `n`.

## What this repository adds

- `Erdos128Finite.lean` gives a **15-bit encoding of all labelled simple
  graphs on six vertices**, a certified symmetry and unique-pair-index audit,
  a symbolic Lean proof of the finite Ramsey statement `R(3,3) <= 6`, and
  an unconditional six-vertex theorem: if every triple spans more than `36/50`
  edges, the graph contains a triangle.
- `check.py` independently enumerates all labelled graphs on 3, 4, 5
  and 6 vertices. It directly checks the correct strict local induced-edge
  inequality using *integer arithmetic* on every minimum permitted-size
  vertex subset. This logically implies the condition on larger subsets,
  since adding vertices cannot remove edges.
- `.github/workflows/jsp000134-research.yml` runs a Lean source check and
  the Python regression; passing CI is evidence for these *bounded* results
  only, not the original unrestricted theorem.

## Exhaustive Python results

| Vertices | Labelled graphs | Triangle-free | Satisfy original local density | Both |
| --- | ---: | ---: | ---: | ---: |
| 3 | 8 | 7 | 0 | 0 |
| 4 | 64 | 41 | 1 | 0 |
| 5 | 1,024 | 388 | 1 | 0 |
| 6 | 32,768 | 5,789 | 5,789 | 0 |

For six vertices, the density hypothesis means each three-vertex subset
contains at least one edge. The classical Ramsey theorem `R(3,3) = 6`
implies either a triangle or an independent triple, eliminating the latter.

## Verification

```sh
python3 research/JSP000134/check.py
lake exe cache get
lake env lean research/JSP000134/Erdos128Finite.lean
```

The outcome is supported only after the complete research workflow
has passed for the current commit (an unrelated root library build alone is
not sufficient). The `#print axioms` commands at the end of the Lean source report
the theorem's assumptions. Do not replace the finite decision with
`native_decide`, `sorry`, `admit` or a custom mathematical axiom.

## Scope / contribution / priority

This is a narrowly scoped research and verification package
prepared with AI assistance for GitHub account **pokrc**. The elementary
Ramsey mathematics is classical and is not claimed as a new mathematical
discovery. The symbolic `ramsey_six` proof is adapted from the MIT-licensed
`DesignExamples/Ramsey.lean` in `egison/egison-prover` (see
`THIRD_PARTY_NOTICE.txt`). The six-vertex graph encoding, statement
connection and independent Python regression form this research package. The research is **not** a complete Lean formalization of the
original all-`n` problem, does **not** establish award eligibility or
priority, and must not be submitted as a complete award claim.

A prize-eligible continuation would require a mathematically valid full
proof or counterexample for the unrestricted Erdős 128 statement, an exact
Lean representation of that original statement, clean proof replay and
a fully evidenced original-publication/priority review.

## Sources

- https://www.erdosproblems.com/128
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/128.lean
- https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md
- https://github.com/kavanaghpatrick/aristotle-math-problems/blob/main/docs/ERDOS128_ANALYSIS.md
