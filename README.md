# jsp_claim

Lean 4 (+ mathlib) formalizations of complete solutions to problems from the
[Justin Sun Prize problem bank](https://github.com/TheJustinSunPrize/awards)
(*TheJustinSunPrize/awards*, 1,022 problems).

This repository is owned and authored by **Yao Siqi** (GitHub: [pokrc](https://github.com/pokrc); email: yaosiqi777@163.com). Each
formalization is a **complete Lean proof** of the original problem statement as
published in the problem bank (no `sorry`, `admit`, or unproved assumptions;
only the standard mathlib axioms `propext`, `Classical.choice`, `Quot.sound`).

## Contents

| File | Problem | Status |
| --- | --- | --- |
| [`JspClaim/JSP000307.lean`](JspClaim/JSP000307.lean) | JSP-000307 — Can three consecutive integers have strictly decreasing largest prime factors? | ✅ Complete, compiles with Lean `v4.34.0` / mathlib `v4.34.0` |
| [`JspClaim/JSP000301.lean`](JspClaim/JSP000301.lean) | JSP-000301 — If two consecutive positive integers are powerful, must at least one be a perfect square? | ✅ Complete, compiles with Lean `v4.34.0` / mathlib `v4.34.0` |
| [`JspClaim/JSP000598.lean`](JspClaim/JSP000598.lean) | JSP-000598 — Can two distinct central binomial coefficients have exactly the same prime divisors? | ✅ Complete, compiles with Lean `v4.34.0` / mathlib `v4.34.0` |
| [`JspClaim/JSP000625.lean`](JspClaim/JSP000625.lean) | JSP-000625 — Erdős–Fuchs theorem (cumulative two-term additive representation counts cannot grow linearly with bounded error) | ✅ Complete, compiles with Lean `v4.34.0` / mathlib `v4.34.0` |

## Problem JSP-000301 — complete answer

**Statement** (problem bank, `problems/catalog-0301-0400.md#JSP-000301`):

> If two consecutive positive integers are powerful, must at least one be a perfect square?

**Answer: No.** The consecutive powerful numbers `12167 = 23³` and
`12168 = 2³·3²·13²` are both powerful and neither is a perfect square
(Golomb 1970).

**Formal statement** (`JSP000301.jsp000301`):

```lean
theorem jsp000301 : ∃ a b : ℕ, a + 1 = b ∧ Powerful a ∧ Powerful b ∧
    ¬ (∃ m : ℕ, m ^ 2 = a) ∧ ¬ (∃ m : ℕ, m ^ 2 = b)
```

with `Powerful n := ∀ p, p.Prime → p ∣ n → 2 ≤ n.factorization p` and witness
`(a, b) = (12167, 12168)`. The proof uses `Nat.Prime.pow_dvd_iff_le_factorization`
to convert the exponent lower bounds into norm_num-decidable divisibility, and
`Nat.sqrt_add_eq'` + `Nat.sqrt_eq'` to show `Nat.sqrt 12167 = Nat.sqrt 12168 = 110`,
so neither number can be a square. The theorem depends only on the standard mathlib
axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Problem JSP-000598 — complete answer

**Statement** (problem bank, `problems/catalog-0501-0600.md#JSP-000598`):

> Can two distinct central binomial coefficients have exactly the same prime divisors?

**Answer: Yes.** The minimal witness is `(n, m) = (87, 88)`: the central binomial
coefficients `C(174,87)` and `C(176,88)` share the same set of prime divisors
(28 primes each). This example is cited in Erdős–Graham–Ruzsa–Straus (1975).

**Formal statement** (`JSP000598.jsp000598`):

```lean
theorem jsp000598 : ∃ n m : ℕ, n < m ∧ Nat.centralBinom n ≠ Nat.centralBinom m ∧ S n = S m
```

with `S n := (Nat.centralBinom n).primeFactors` and witness `(87, 88)`. The proof
avoids computing the 52-digit binomial values: it uses the recurrence
`(n+1)·C(2(n+1),n+1) = 2(2n+1)·C(2n,n)` at `n = 87` (giving
`44·C(176,88) = 175·C(174,87)`), Kummer's theorem (`Nat.factorization_choose'`)
for the divisibility facts `5,7 | C(174,87)` and `2,11 | C(176,88)`, the small
prime-factor sets `primeFactors 44 = {2,11}`, `primeFactors 175 = {5,7}`, and a
double inclusion `S(87) ⊆ S(88) ⊆ S(87)` via Euclid's lemma. The theorem depends
only on the standard mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Formalization author**: Yao Siqi (GitHub: pokrc).

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

## Problem JSP-000625 — complete answer (Erdős–Fuchs)

**Statement** (problem bank, `problems/catalog-0601-0700.md#JSP-000625`):

> Can cumulative two-term additive representation counts grow linearly with bounded error?

**Answer: No.** This is the Erdős–Fuchs theorem (Erdős–Fuchs 1956). For any infinite
`A ⊆ ℕ`, writing `r(n) = #{(a,a') ∈ A² : a+a' = n}` (ordered pairs) and
`R(N) = Σ_{n≤N} r(n)`, there is **no** constant `c > 0` such that
`R(N) = cN + O(1)`.

**Formal statement** (`JSP000625Final.jsp000625`):

```lean
theorem jsp000625 :
    ¬ ∃ (A : Set ℕ) (c : ℝ), A.Infinite ∧ 0 < c ∧
      (∃ C : ℝ, ∀ N : ℕ, |(summatoryRepresentationCount A N : ℝ) - c * (N : ℝ)| ≤ C)
```

**Proof structure** (kernel-checked, no `sorry`/`admit`/`native_decide`):

1. Generating functions: `g(z) = Σ_{a∈A} z^a`, with `g(q)² = Σ r(n)q^n` (Cauchy square).
2. Error sequence: `ε(n) = R(n) - c(n+1)` satisfies `ε(n) - ε(n-1) = r(n) - c`.
3. Series identity: `Σ r(n)z^n = c/(1-z) + (1-z)·Σ ε(n)z^n` for `‖z‖ < 1`.
4. Error bound: `‖Σ ε(n)q^n‖ ≤ D/(1-q)` when `‖ε(n)‖ ≤ D`.
5. Main-term lower bound: `(indicatorSeriesReal A 1 q)² ≥ c/(1-q) - D`.
6. Block Parseval: circle-average of `‖geometricBlock·g‖²` equals the squared block
   coefficients; upper (circle majorant) and lower (main term) bounds both scale like
   `M⁷` under the chosen radius `r = 1 - 1/M¹³`.
7. Contradiction: `(L/2)·M⁷ ≤ RHS ≤ (27c+2D+1)·M⁷` with `L = 2(27c+2D+2)`, so
   `L/2 = 27c+2D+2 > 27c+2D+1` — impossible.

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