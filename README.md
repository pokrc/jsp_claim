# jsp_claim

Lean 4 + Mathlib formalizations for problems in the
[Justin Sun Prize problem bank](https://github.com/TheJustinSunPrize/awards).

Owned and authored by **Yao Siqi** (GitHub: [pokrc](https://github.com/pokrc); email: yaosiqi777@163.com).

Every retained module is a **complete Lean proof**: no `sorry`, no `admit`, no `native_decide`,
and no added axioms. Axiom audit for each main theorem reports only the standard mathlib
axioms `propext`, `Classical.choice`, `Quot.sound`. Toolchain: `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0`.

```bash
lake exe cache get && lake build JspClaim
```

## Retained modules

| Module | JSP | What it proves | Submission status |
| --- | --- | --- | --- |
| [`JspClaim/JSP000301.lean`](JspClaim/JSP000301.lean) | JSP-000301 | `12167 = 23^3` and `12168 = 2^3*3^2*13^2` are consecutive powerful numbers, neither a square (Golomb's counterexample) | **submitted** — PR #1960 |
| [`JspClaim/JSP000689.lean`](JspClaim/JSP000689.lean) | JSP-000689 | Erdős–Lovász: a non-2-colourable `r`-uniform hypergraph has a vertex of degree `≥ 2^(r-1)/(4r)` (finite vertex sets), plus the Fano-plane verification example | **submitted** — PR #2054 |
| [`JspClaim/JSP000546.lean`](JspClaim/JSP000546.lean) | JSP-000546 | counterexample for products of consecutive terms of a coprime-difference AP being a perfect power | not submitted |
| [`JspClaim/JSP000554.lean`](JspClaim/JSP000554.lean) | JSP-000554 | `(7, 11)` is a pair of consecutive primes with no integer of least prime factor `≥ 4` strictly between them | **withdrawn** — the bank's source for this entry (Erdős #682) asks the *almost all n* question answered affirmatively by Gafni–Tao; the universal reading proved here is not the recorded solution |

`JspClaim/JSP000689_helpers.lean` holds the Lovász Local Lemma development used by JSP-000689.

## Removed modules

Earlier commits contained further modules (JSP-000183, 243, 307, 558, 598, 625, 876, 947). They were
removed for one of three reasons, recorded here so the history is not mistaken for a live result:

* **withdrawn as a port** — JSP-000183 followed `ekalvi/erdos-193` (the authors' own proof, earlier),
  JSP-000625 followed `plby/lean-proofs` `Erdos763.lean` almost name-for-name. Neither was an
  independent formalization, and neither may be registered as mine.
* **not the recorded solution** — JSP-000243 (Croot's asymptotic interval law), JSP-000307 (Balog's
  infinitude theorem), JSP-000598 (GPT Pro / Price infinitude theorem), JSP-000554 (Gafni–Tao
  almost-all result): in each case the bank's description paraphrases away a quantifier, and the
  module answers the paraphrase rather than the problem.
* **not a solution at all** — JSP-000876 (the construction used non-adjacent intervals; Erdős #1056
  requires contiguous ones) and JSP-000947 (`n = 45` is one of the six known values of Erdős #1142).

Corrections for the underlying description defects were filed with the bank: #3263 (JSP-000876),
#3264 (JSP-000947), #3342 (JSP-000554).
