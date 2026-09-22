# jsp_claim

Lean 4 + Mathlib formalizations for problems in the
[Justin Sun Prize problem bank](https://github.com/TheJustinSunPrize/awards).

Owned and authored by **Yao Siqi** (GitHub: [pokrc](https://github.com/pokrc); email: yaosiqi777@163.com).

Every module here is a **complete Lean proof**: no `sorry`, no `admit`, no `native_decide`, no added
axioms. Axiom audit for every main theorem reports only the standard Mathlib axioms
`propext`, `Classical.choice`, `Quot.sound`. Toolchain `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0`.

```bash
git clone https://github.com/pokrc/jsp_claim && cd jsp_claim
lake exe cache get && lake build JspClaim
```

## Modules and their submission status

| Module | JSP | What it proves | Submitted for |
| --- | --- | --- | --- |
| `JspClaim/JSP000301.lean` | JSP-000301 | `12167 = 23^3` and `12168 = 2^3·3^2·13^2` are consecutive powerful numbers, neither a square (Golomb's counterexample) | PR #1960 |
| `JspClaim/JSP000689.lean` (+ `_helpers`) | JSP-000689 | Erdős–Lovász: a non-2-colourable `r`-uniform hypergraph has a vertex of degree `≥ 2^(r-1)/(4r)`, plus the Fano-plane example | PR #2054 |
| `JspClaim/JSP000307.lean` | JSP-000307 | the witness `152, 153, 154` has strictly decreasing largest prime factors | printed statement of the entry; the source problem (Erdős #372) asks the infinitude version, stated in the module |
| `JspClaim/JSP000598.lean` | JSP-000598 | the pair `(87, 88)` has central binomial coefficients with the same set of prime divisors | printed statement of the entry; the source problem (Erdős #730) asks the infinitude version, stated in the module |
| `JspClaim/JSP000243.lean` | JSP-000243 | the shortest denominator interval with reciprocal sum `1` has span `4`, attained by `[2, 6]` | printed statement of the entry; the entry's cited source is Croot's asymptotic width law, stated in the module |
| `JspClaim/JSP000546.lean` | JSP-000546 | the `k = 3` example `18·25·32 = 120^2` in an AP with `gcd(a,d) = 1` | printed statement of the entry; the source problem (Erdős #672) requires `k ≥ 4`, stated in the module |
| `JspClaim/JSP000554.lean` | JSP-000554 | `(7, 11)` is a pair of consecutive primes with no integer of least prime factor `≥ 4` between them | not submitted — the entry's recorded solution (Gafni–Tao, Erdős #682) answers the *almost all n* question in the affirmative |

Each module states the exact scope of what it proves at the top of the file, and each submission
repeats it, so no module is presented as proving more than it does.

## Removed modules

Earlier commits also contained `JSP000183`, `JSP000625`, `JSP000876`, `JSP000947`, `JSP000558`
(with `JSP000689_bridge` and scratch files). They were removed and are **not** submitted:

* `JSP000183`, `JSP000625` — followed existing public formalizations (`ekalvi/erdos-193` and
  `plby/lean-proofs` `Erdos763.lean`) closely enough that they are not independent work. The
  submission guidelines forbid registering a copy of someone else's proof; these must not be
  registered as mine.
* `JSP000876` — the construction used non-adjacent intervals, while Erdős #1056 requires the
  intervals to be contiguous, so the file does not address the problem.
* `JSP000947` — `n = 45` is one of the six known values of Erdős #1142; the entry asks for `n > 105`
  or infinitely many.
* `JSP000558` — only the `k = 2` case study, a partial result.

Corrections for the underlying description defects were filed with the bank: #3263 (JSP-000876),
#3264 (JSP-000947), #3342 (JSP-000554).
