import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.NormNum

/-!
# JSP-000301 — Two consecutive powerful numbers, neither a perfect square

Problem bank entry (TheJustinSunPrize/awards, `problems/catalog-0301-0400.md#JSP-000301`):

> **If two consecutive positive integers are powerful, must at least one be a
> perfect square?**

The answer is **no** (Golomb 1970).  A counterexample is the consecutive pair

```
12167 = 23³            and    12168 = 2³ · 3² · 13²
```

* `12167 = 23³` is powerful: its only prime divisor `23` occurs with exponent `3 ≥ 2`.
* `12168 = 2³ · 3² · 13²` is powerful: each prime divisor (`2, 3, 13`) occurs with
  exponent `≥ 2`.
* Neither is a perfect square: `12167` and `12168` both lie strictly between the
  consecutive squares `110² = 12100` and `111² = 12321`; more precisely
  `Nat.sqrt 12167 = 110` and `Nat.sqrt 12168 = 110`, so a square equal to either
  number would have to be `110² = 12100`, a contradiction.

Here `n` is *powerful* (幂数) if every prime divisor of `n` divides `n` to an
exponent `≥ 2`, i.e. `∀ p, p.Prime → p ∣ n → 2 ≤ n.factorization p`.

Every step below is kernel-checked; the only computations are on the small numbers
`12167`, `12168`, `23³`, `2³·3²·13²` and the squares `110²`, `111²` (discharged by
`norm_num`).  No `sorry`, no `native_decide`.
-/

namespace JSP000301

/-- A natural number `n` is *powerful* if every prime divisor `p` of `n` occurs in
`n` with exponent at least `2`: `2 ≤ n.factorization p`. -/
def Powerful (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → 2 ≤ n.factorization p

/-- `12167 = 23³` is powerful: the only prime divisor of `12167` is `23`, with
exponent `3 ≥ 2`. -/
lemma powerful_12167 : Powerful 12167 := by
  intro p hp hpd
  -- `p ∣ 12167 = 23³`, so (as `p` is prime) `p ∣ 23`.
  have h : p ∣ 23 ^ 3 := by
    simpa [show (23 ^ 3 : ℕ) = 12167 by norm_num] using hpd
  have hp23 : p = 23 :=
    (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 23)).mp (hp.dvd_of_dvd_pow h)
  subst p
  -- `2 ≤ 12167.factorization 23` is equivalent to `23² ∣ 12167`.
  rw [← Nat.Prime.pow_dvd_iff_le_factorization (p := 23) (k := 2) (n := 12167)
    (by decide : Nat.Prime 23) (by norm_num : 12167 ≠ 0)]
  norm_num

/-- `12168 = 2³ · 3² · 13²` is powerful: every prime divisor is one of `2, 3, 13`,
each occurring with exponent `≥ 2`. -/
lemma powerful_12168 : Powerful 12168 := by
  intro p hp hpd
  -- `p ∣ 12168 = 2³ · 3² · 13²`, so `p` is one of `2, 3, 13`.
  have h : p ∣ 2 ^ 3 * 3 ^ 2 * 13 ^ 2 := by
    simpa [show (2 ^ 3 * 3 ^ 2 * 13 ^ 2 : ℕ) = 12168 by norm_num] using hpd
  rcases hp.dvd_mul.mp h with h23 | h13
  · rcases hp.dvd_mul.mp h23 with h2 | h3
    · -- `p ∣ 2³`, hence `p = 2`; then `2 ≤ 12168.factorization 2` is `4 ∣ 12168`.
      have hp2 : p = 2 :=
        (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp (hp.dvd_of_dvd_pow h2)
      subst p
      rw [← Nat.Prime.pow_dvd_iff_le_factorization (p := 2) (k := 2) (n := 12168)
        (by decide : Nat.Prime 2) (by norm_num : 12168 ≠ 0)]
      norm_num
    · -- `p ∣ 3²`, hence `p = 3`; then `2 ≤ 12168.factorization 3` is `9 ∣ 12168`.
      have hp3 : p = 3 :=
        (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp (hp.dvd_of_dvd_pow h3)
      subst p
      rw [← Nat.Prime.pow_dvd_iff_le_factorization (p := 3) (k := 2) (n := 12168)
        (by decide : Nat.Prime 3) (by norm_num : 12168 ≠ 0)]
      norm_num
  · -- `p ∣ 13²`, hence `p = 13`; then `2 ≤ 12168.factorization 13` is `13² ∣ 12168`.
    have hp13 : p = 13 :=
      (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13)).mp (hp.dvd_of_dvd_pow h13)
    subst p
    rw [← Nat.Prime.pow_dvd_iff_le_factorization (p := 13) (k := 2) (n := 12168)
      (by decide : Nat.Prime 13) (by norm_num : 12168 ≠ 0)]
    norm_num

/-- `Nat.sqrt 12167 = 110`, since `12167 = 110² + 67` with `67 ≤ 2·110`. -/
lemma sqrt_12167 : Nat.sqrt 12167 = 110 := by
  rw [show (12167 : ℕ) = 110 ^ 2 + 67 by norm_num]
  exact Nat.sqrt_add_eq' 110 (by norm_num)

/-- `Nat.sqrt 12168 = 110`, since `12168 = 110² + 68` with `68 ≤ 2·110`. -/
lemma sqrt_12168 : Nat.sqrt 12168 = 110 := by
  rw [show (12168 : ℕ) = 110 ^ 2 + 68 by norm_num]
  exact Nat.sqrt_add_eq' 110 (by norm_num)

/-- `12167` is not a perfect square: `Nat.sqrt 12167 = 110`, while any square
`m² = 12167` would force `m = 110` and hence `110² = 12167`, a contradiction. -/
lemma not_square_12167 : ¬ ∃ m : ℕ, m ^ 2 = 12167 := by
  rintro ⟨m, hm⟩
  have hsq : Nat.sqrt 12167 = 110 := sqrt_12167
  have h1 : Nat.sqrt (m ^ 2) = 110 := by simpa [← hm] using hsq
  have h2 : Nat.sqrt (m ^ 2) = m := Nat.sqrt_eq' m
  have hm110 : m = 110 := by simpa [h2] using h1
  subst m
  norm_num at hm

/-- `12168` is not a perfect square: `Nat.sqrt 12168 = 110`, while any square
`m² = 12168` would force `m = 110` and hence `110² = 12168`, a contradiction. -/
lemma not_square_12168 : ¬ ∃ m : ℕ, m ^ 2 = 12168 := by
  rintro ⟨m, hm⟩
  have hsq : Nat.sqrt 12168 = 110 := sqrt_12168
  have h1 : Nat.sqrt (m ^ 2) = 110 := by simpa [← hm] using hsq
  have h2 : Nat.sqrt (m ^ 2) = m := Nat.sqrt_eq' m
  have hm110 : m = 110 := by simpa [h2] using h1
  subst m
  norm_num at hm

/-- The complete answer to JSP-000301: two consecutive powerful numbers need not
include a perfect square.  The witness is the pair `(12167, 12168)` (Golomb 1970):
`12167 = 23³` and `12168 = 2³ · 3² · 13²` are powerful, consecutive, and neither
is a perfect square. -/
theorem jsp000301 : ∃ a b : ℕ, a + 1 = b ∧ Powerful a ∧ Powerful b ∧
    ¬ (∃ m : ℕ, m ^ 2 = a) ∧ ¬ (∃ m : ℕ, m ^ 2 = b) := by
  exact ⟨12167, 12168, by norm_num, powerful_12167, powerful_12168,
    not_square_12167, not_square_12168⟩

end JSP000301
