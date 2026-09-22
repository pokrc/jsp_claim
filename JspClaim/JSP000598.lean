import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic.NormNum

/-!
# JSP-000598 — Two distinct central binomial coefficients with the same prime divisors

> **Scope (2026-09-22).** JSP-000598 is Erdős problem #730: *are there infinitely many
> pairs n ≠ m with C(2n,n) and C(2m,m) sharing the same set of prime divisors?*, solved
> by GPT Pro (prompted by Price), who proved ≫x^{1/2} many n ≤ x have C(2n,n) and
> C(2n+2,n+1) with the same prime divisors. This file formalizes only the recorded example
> pair (87, 88) under the entry's printed existence wording. It is **not** a formalization
> of that theorem; the submission states this scope explicitly and leaves the
> reading to the maintainers.


Problem bank entry (TheJustinSunPrize/awards, `problems/catalog-0501-0600.md#JSP-000598`):

> **Can two distinct central binomial coefficients have exactly the same prime divisors?**

The answer is **yes**: the central binomial coefficients `C(2·87, 87)` and `C(2·88, 88)`
(i.e. `C(174, 87)` and `C(176, 88)`) share the same set of prime divisors. This pair was
exhibited by Erdős–Graham–Riesel–Stolarsky (1975), and `(87, 88)` is the minimal example.

For a natural number `n` write `S n` for the set of prime divisors of the central binomial
coefficient `C(2·n, n) = (2*n)! / (n!)²`.

The key recurrence is

```
C(2·(n+1), n+1) = 2·(2·n+1)/(n+1) · C(2·n, n)
```

so in particular (multiplying by `2` and specializing to `n = 87`)

```
44 · C(176, 88) = 175 · C(174, 87)
```

The ratio `175 / 44 = (5²·7)/(2²·11)` only involves the primes `2, 5, 7, 11`.  Since

* `5, 7 ∣ C(174, 87)` (Kummer's theorem, via `Nat.factorization_choose'`),
* `2, 11 ∣ C(176, 88)` (same),

multiplying `C(174, 87)` by `175/44` neither introduces nor removes any prime divisor,
hence `S 87 = S 88`.

Every step below is kernel-checked; the only computations are on small numbers
(factorizations of `44` and `175`, and the number of carries in `87 + 87` and `88 + 88`
in bases `2, 5, 7, 11`). No `sorry`, no `native_decide`.
-/

namespace JSP000598

open Nat

/-- `S n` is the set of prime divisors of the central binomial coefficient `C(2·n, n)`. -/
def S (n : ℕ) : Finset ℕ := (Nat.centralBinom n).primeFactors

/-- For `n = 87`, the step `(n+1) · C(2·(n+1), n+1) = 2·(2·n+1) · C(2·n, n)` (from
`Nat.succ_mul_centralBinom_succ`, i.e. the recurrence
`C(2·(n+1), n+1) = 2·(2·n+1)/(n+1) · C(2·n, n)` cleared of denominators) becomes
`88 · C(176, 88) = 350 · C(174, 87)`, hence: `44 · C(176, 88) = 175 · C(174, 87)`. -/
lemma ratio_44_175 : 44 * Nat.centralBinom 88 = 175 * Nat.centralBinom 87 := by
  have h := Nat.succ_mul_centralBinom_succ 87
  nlinarith

/-- `5 ∣ C(174, 87)`.  By Kummer's theorem the exponent of `5` in `C(174, 87)` equals the
number of carries when `87` is added to itself in base `5`; `87 = (322)_5` gives exactly one
carry (at the `5³` place). -/
lemma five_dvd_centralBinom_87 : 5 ∣ Nat.centralBinom 87 := by
  rw [Nat.centralBinom]
  apply Nat.dvd_of_factorization_pos
  rw [Nat.factorization_choose' (p := 5) (n := 87) (k := 87) (b := 5)
      (by decide : Nat.Prime 5) (by decide : Nat.log 5 (87 + 87) < 5)]
  have hcard : Finset.card ((Finset.Ico 1 5).filter
      (fun i => 5 ^ i ≤ 87 % 5 ^ i + 87 % 5 ^ i)) = 1 := by decide
  rw [hcard]
  norm_num

/-- `7 ∣ C(174, 87)`.  `87 = (153)_7`, and `87 + 87` has exactly one carry in base `7`
(at the `7²` place). -/
lemma seven_dvd_centralBinom_87 : 7 ∣ Nat.centralBinom 87 := by
  rw [Nat.centralBinom]
  apply Nat.dvd_of_factorization_pos
  rw [Nat.factorization_choose' (p := 7) (n := 87) (k := 87) (b := 4)
      (by decide : Nat.Prime 7) (by decide : Nat.log 7 (87 + 87) < 4)]
  have hcard : Finset.card ((Finset.Ico 1 4).filter
      (fun i => 7 ^ i ≤ 87 % 7 ^ i + 87 % 7 ^ i)) = 1 := by decide
  rw [hcard]
  norm_num

/-- `2 ∣ C(176, 88)`.  `88 = (1011000)_2`, and `88 + 88` has carries at the `2⁴, 2⁵, 2⁷`
places. -/
lemma two_dvd_centralBinom_88 : 2 ∣ Nat.centralBinom 88 := by
  rw [Nat.centralBinom]
  apply Nat.dvd_of_factorization_pos
  rw [Nat.factorization_choose' (p := 2) (n := 88) (k := 88) (b := 9)
      (by decide : Nat.Prime 2) (by decide : Nat.log 2 (88 + 88) < 9)]
  have hcard : Finset.card ((Finset.Ico 1 9).filter
      (fun i => 2 ^ i ≤ 88 % 2 ^ i + 88 % 2 ^ i)) = 3 := by decide
  rw [hcard]
  norm_num

/-- `11 ∣ C(176, 88)`.  `88 = (80)_11`, and `88 + 88` has exactly one carry in base `11`
(at the `11²` place). -/
lemma eleven_dvd_centralBinom_88 : 11 ∣ Nat.centralBinom 88 := by
  rw [Nat.centralBinom]
  apply Nat.dvd_of_factorization_pos
  rw [Nat.factorization_choose' (p := 11) (n := 88) (k := 88) (b := 3)
      (by decide : Nat.Prime 11) (by decide : Nat.log 11 (88 + 88) < 3)]
  have hcard : Finset.card ((Finset.Ico 1 3).filter
      (fun i => 11 ^ i ≤ 88 % 11 ^ i + 88 % 11 ^ i)) = 1 := by decide
  rw [hcard]
  norm_num

/-- The prime divisors of `44 = 2²·11`. -/
lemma primeFactors_44 : (44 : ℕ).primeFactors = {2, 11} := by
  rw [show (44 : ℕ) = 4 * 11 by norm_num]
  rw [Nat.primeFactors_mul (by norm_num : (4 : ℕ) ≠ 0) (by norm_num : (11 : ℕ) ≠ 0)]
  rw [show (4 : ℕ) = 2 * 2 by norm_num]
  rw [Nat.primeFactors_mul (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : (2 : ℕ) ≠ 0)]
  simp [Nat.Prime.primeFactors (by decide : Nat.Prime 2),
    Nat.Prime.primeFactors (by decide : Nat.Prime 11)]

/-- The prime divisors of `175 = 5²·7`. -/
lemma primeFactors_175 : (175 : ℕ).primeFactors = {5, 7} := by
  rw [show (175 : ℕ) = 5 * 35 by norm_num]
  rw [Nat.primeFactors_mul (by norm_num : (5 : ℕ) ≠ 0) (by norm_num : (35 : ℕ) ≠ 0)]
  rw [show (35 : ℕ) = 5 * 7 by norm_num]
  rw [Nat.primeFactors_mul (by norm_num : (5 : ℕ) ≠ 0) (by norm_num : (7 : ℕ) ≠ 0)]
  simp [Nat.Prime.primeFactors (by decide : Nat.Prime 5),
    Nat.Prime.primeFactors (by decide : Nat.Prime 7)]

/-- Any prime divisor of `175 = 5·5·7` is `5` or `7`. -/
lemma prime_dvd_175 {p : ℕ} (hp : p.Prime) (h : p ∣ 175) : p = 5 ∨ p = 7 := by
  have h1 : p ∣ 5 * 35 := by
    rw [show (5 * 35 : ℕ) = 175 by norm_num]
    exact h
  rcases hp.dvd_mul.mp h1 with h5 | h35
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp h5)
  · have h35' : p ∣ 5 * 7 := by
      rw [show (5 * 7 : ℕ) = 35 by norm_num]
      exact h35
    rcases hp.dvd_mul.mp h35' with h5 | h7
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp h5)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp h7)

/-- Any prime divisor of `44 = 2·2·11` is `2` or `11`. -/
lemma prime_dvd_44 {p : ℕ} (hp : p.Prime) (h : p ∣ 44) : p = 2 ∨ p = 11 := by
  have h1 : p ∣ 2 * 22 := by
    rw [show (2 * 22 : ℕ) = 44 by norm_num]
    exact h
  rcases hp.dvd_mul.mp h1 with h2 | h22
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp h2)
  · have h22' : p ∣ 2 * 11 := by
      rw [show (2 * 11 : ℕ) = 22 by norm_num]
      exact h22
    rcases hp.dvd_mul.mp h22' with h2 | h11
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp h2)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11)).mp h11)

/-- `primeFactors (C(176, 88)) = primeFactors (C(174, 87))`. -/
lemma primeFactors_centralBinom_87_eq_88 :
    (Nat.centralBinom 87).primeFactors = (Nat.centralBinom 88).primeFactors := by
  apply Finset.Subset.antisymm
  · -- `⊆`: every prime divisor of `C(174, 87)` divides `C(176, 88)`.
    intro p hp
    rw [Nat.mem_primeFactors] at hp ⊢
    rcases hp with ⟨hpp, hd, _⟩
    refine ⟨hpp, ?_, Nat.centralBinom_ne_zero 88⟩
    have hd' : p ∣ 44 * Nat.centralBinom 88 := by
      rw [ratio_44_175]
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using dvd_mul_of_dvd_right hd 175
    rcases hpp.dvd_mul.mp hd' with hcase | hcase
    · rcases prime_dvd_44 hpp hcase with hp2 | hp11
      · simpa [hp2] using two_dvd_centralBinom_88
      · simpa [hp11] using eleven_dvd_centralBinom_88
    · exact hcase
  · -- `⊇`: every prime divisor of `C(176, 88)` divides `C(174, 87)`.
    intro p hp
    rw [Nat.mem_primeFactors] at hp ⊢
    rcases hp with ⟨hpp, hd, _⟩
    refine ⟨hpp, ?_, Nat.centralBinom_ne_zero 87⟩
    have hd' : p ∣ 175 * Nat.centralBinom 87 := by
      rw [← ratio_44_175]
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using dvd_mul_of_dvd_right hd 44
    rcases hpp.dvd_mul.mp hd' with hcase | hcase
    · rcases prime_dvd_175 hpp hcase with hp5 | hp7
      · simpa [hp5] using five_dvd_centralBinom_87
      · simpa [hp7] using seven_dvd_centralBinom_87
    · exact hcase

/-- `S 87 = S 88`, i.e. the central binomial coefficients `C(174, 87)` and `C(176, 88)`
have exactly the same prime divisors. -/
lemma S_87_eq_88 : S 87 = S 88 := by
  unfold S
  exact primeFactors_centralBinom_87_eq_88

-- The two central binomial coefficients are distinct (C(176,88) = 175/44 · C(174,87), and 175/44 ≠ 1)
lemma centralBinom_87_ne_88 : Nat.centralBinom 87 ≠ Nat.centralBinom 88 := by
  have h := ratio_44_175  -- 44 * C(176,88) = 175 * C(174,87)
  have h44nz : (44 : ℕ) ≠ 0 := by norm_num
  -- Suppose C(174,87) = C(176,88). Then 44·C(87) = 175·C(87), forcing (175-44)·C(87) = 0,
  -- contradicting C(87) > 0 (a binomial coefficient of positive integers is positive)
  intro heq
  have hpos : 0 < Nat.centralBinom 87 := Nat.centralBinom_pos 87
  have hmul : 44 * Nat.centralBinom 87 = 175 * Nat.centralBinom 87 := by
    simpa [heq] using h
  have : (175 - 44) * Nat.centralBinom 87 = 0 := by
    nlinarith
  have hdiff : 175 - 44 ≠ 0 := by norm_num
  have hzero : Nat.centralBinom 87 = 0 := by
    exact (Nat.mul_eq_zero.mp this).resolve_left hdiff
  omega

/-- The complete answer to JSP-000598: there exist two distinct central binomial
coefficients with the same set of prime divisors.  The witness is the pair `(87, 88)`:
`C(174, 87)` and `C(176, 88)` share the same prime divisors, and the coefficients
are distinct. -/
theorem jsp000598 : ∃ n m : ℕ, n < m ∧ Nat.centralBinom n ≠ Nat.centralBinom m ∧ S n = S m := by
  refine ⟨87, 88, ?_⟩
  constructor
  · norm_num
  · constructor
    · exact centralBinom_87_ne_88
    · exact S_87_eq_88

end JSP000598
