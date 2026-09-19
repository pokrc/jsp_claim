# jsp_claim

Lean 4 (+ mathlib) formalizations of complete solutions to problems from the
[Justin Sun Prize problem bank](https://github.com/TheJustinSunPrize/awards)
(*TheJustinSunPrize/awards*, 1,022 problems).

This repository is owned and authored by the submitting GitHub account, and each
formalization is a **complete Lean proof** of the original problem statement as
published in the problem bank (no `sorry`, `admit`, or unproved assumptions;
only the standard mathlib axioms `propext`, `Classical.choice`, `Quot.sound`).

## Contents

| File | Problem | Status |
| --- | --- | --- |
| [`JspClaim/JSP000307.lean`](JspClaim/JSP000307.lean) | JSP-000307 — Can three consecutive integers have strictly decreasing largest prime factors? | ✅ Complete, compiles with Lean `v4.34.0` / mathlib `v4.34.0` |

## Problem JSP-000307 — complete answer

**Statement** (problem bank, `problems/catalog-0301-0400.md#JSP-000307`):

> Can three consecutive integers have strictly decreasing largest prime factors?

**Answer: Yes.** The integers `152, 153, 154` factor as

```
152 = 2³ · 19
153 = 3² · 17
154 = 2 · 7 · 11
```

so their largest prime factors are `19, 17, 11`, strictly decreasing.

**Formal statement** (`JSP000307.jsp000307`, using mathlib's canonical
`Nat.maxPrimeFac` — "the greatest prime factor of a natural number"):

```lean
theorem jsp000307 :
    ∃ n : ℕ, maxPrimeFac n > maxPrimeFac (n + 1) ∧
      maxPrimeFac (n + 1) > maxPrimeFac (n + 2)
```

with witness `n = 152`. The proof is fully kernel-checked: the factorizations are
derived from the definitions via `Nat.maxPrimeFac_mul`, `Nat.maxPrimeFac_pow` and
`Nat.Prime.maxPrimeFac_eq_self`, primality facts are decided by kernel reduction
(`decide`), and the final arithmetic is discharged by `norm_num`.
The theorem depends only on the standard mathlib axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## Build instructions

Requires [elan](https://github.com/leanprover/elan) and Lean `v4.34.0`
(pinned in [`lean-toolchain`](lean-toolchain); mathlib pinned to tag `v4.34.0`
in [`lakefile.toml`](lakefile.toml)).

```bash
lake exe cache get        # fetch prebuilt mathlib oleans (optional, faster)
lake build                # builds the library, including JspClaim/JSP000307.lean
```

`lake build` must complete with no errors; `JspClaim/JSP000307.lean` contains no
`sorry`/`admit`/`axiom` beyond mathlib's standard axioms.

## Verification of the key facts

| Fact | Lean lemma |
| --- | --- |
| `maxPrimeFac 152 = 19` | `JSP000307.maxPrimeFac_152` |
| `maxPrimeFac 153 = 17` | `JSP000307.maxPrimeFac_153` |
| `maxPrimeFac 154 = 11` | `JSP000307.maxPrimeFac_154` |
| Complete answer | `JSP000307.jsp000307` |

## License

Apache-2.0.