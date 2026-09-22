import Mathlib.Data.Nat.MaxPrimeFac
import Mathlib.Tactic.NormNum

/-!
# JSP-000307 — Three consecutive integers with strictly decreasing largest prime factors

> **Scope (2026-09-22).** JSP-000307 is Erdős problem #372: *there are infinitely many
> n with P(n) > P(n+1) > P(n+2)*, solved by Balog [Ba01] (≫√x many n ≤ x), with the
> conjecture that the density is 1/6. This file formalizes only the finite witness
> 152, 153, 154 under the entry's printed existence wording. It is **not** a formalization
> of Balog's theorem; the submission states this scope explicitly and leaves the
> reading to the maintainers.


Problem bank entry (TheJustinSunPrize/awards, `problems/catalog-0301-0400.md#JSP-000307`):

> **Can three consecutive integers have strictly decreasing largest prime factors?**

The answer is **yes**.

The three consecutive integers `152, 153, 154` have prime factorizations

```
152 = 2³ · 19
153 = 3² · 17
154 = 2 · 7 · 11
```

so their largest prime factors are `19, 17, 11`, which are strictly decreasing.

We use the canonical `Nat.maxPrimeFac` from mathlib ("the greatest prime factor of a
natural number `n > 1`"). The formalized statement of the complete answer:

```
∃ n : ℕ,  maxPrimeFac n > maxPrimeFac (n+1)  ∧  maxPrimeFac (n+1) > maxPrimeFac (n+2)
```

with witness `n = 152`. Every step is kernel-checked: the factorizations are rewritten
using `maxPrimeFac_mul`, `maxPrimeFac_pow` and `Prime.maxPrimeFac_eq_self`, and the
arithmetic is discharged by `norm_num` (no `sorry`, no `native_decide`).
-/

open Nat

namespace JSP000307

/-- `maxPrimeFac 152 = 19`, since `152 = 2³ · 19`. -/
lemma maxPrimeFac_152 : maxPrimeFac 152 = 19 := by
  rw [show (152 : ℕ) = 2 ^ 3 * 19 by norm_num,
      maxPrimeFac_mul (by norm_num : 2 ^ 3 ≠ 0) (by norm_num : 19 ≠ 0),
      maxPrimeFac_pow (by norm_num : 3 ≠ 0),
      Nat.Prime.maxPrimeFac_eq_self (by decide : Nat.Prime 2),
      Nat.Prime.maxPrimeFac_eq_self (by decide : Nat.Prime 19)]
  norm_num

/-- `maxPrimeFac 153 = 17`, since `153 = 3² · 17`. -/
lemma maxPrimeFac_153 : maxPrimeFac 153 = 17 := by
  rw [show (153 : ℕ) = 3 ^ 2 * 17 by norm_num,
      maxPrimeFac_mul (by norm_num : 3 ^ 2 ≠ 0) (by norm_num : 17 ≠ 0),
      maxPrimeFac_pow (by norm_num : 2 ≠ 0),
      Nat.Prime.maxPrimeFac_eq_self (by decide : Nat.Prime 3),
      Nat.Prime.maxPrimeFac_eq_self (by decide : Nat.Prime 17)]
  norm_num

/-- `maxPrimeFac 154 = 11`, since `154 = 2 · 7 · 11`. -/
lemma maxPrimeFac_154 : maxPrimeFac 154 = 11 := by
  rw [show (154 : ℕ) = 2 * 7 * 11 by norm_num,
      maxPrimeFac_mul (by norm_num : 2 * 7 ≠ 0) (by norm_num : 11 ≠ 0),
      maxPrimeFac_mul (by norm_num : 2 ≠ 0) (by norm_num : 7 ≠ 0),
      Nat.Prime.maxPrimeFac_eq_self (by decide : Nat.Prime 2),
      Nat.Prime.maxPrimeFac_eq_self (by decide : Nat.Prime 7),
      Nat.Prime.maxPrimeFac_eq_self (by decide : Nat.Prime 11)]
  norm_num

/-- The complete answer to JSP-000307: three consecutive integers with strictly
decreasing largest prime factors exist (witness: `152, 153, 154`). -/
theorem jsp000307 :
    ∃ n : ℕ, maxPrimeFac n > maxPrimeFac (n + 1) ∧
      maxPrimeFac (n + 1) > maxPrimeFac (n + 2) := by
  refine ⟨152, ?_, ?_⟩
  · rw [show (152 : ℕ) + 1 = 153 by norm_num, maxPrimeFac_152, maxPrimeFac_153]
    norm_num
  · rw [show (152 : ℕ) + 1 = 153 by norm_num, show (152 : ℕ) + 2 = 154 by norm_num,
        maxPrimeFac_153, maxPrimeFac_154]
    norm_num

end JSP000307
