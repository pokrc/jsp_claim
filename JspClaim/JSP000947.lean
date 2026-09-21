import Mathlib.Tactic

namespace JSP000947

/-!
# JSP-000947 — Is there an integer whose differences from every permitted smaller power of two are all prime?

**Problem** (`problems/catalog-0901-1000.md#JSP-000947`):
> Is there an integer whose differences from every permitted smaller power of two are all prime?

**Answer: YES.** The integer n = 45 has the property that for every permitted smaller
power of two 2ᵏ < 45 (k = 1..5, i.e. 2, 4, 8, 16, 32), the difference 45 − 2ᵏ is prime:

  45 − 2  = 43  (prime)
  45 − 4  = 41  (prime)
  45 − 8  = 37  (prime)
  45 − 16 = 29  (prime)
  45 − 32 = 13  (prime)

The next power 64 exceeds 45, so the five differences above are all the permitted ones.
-/

/-- If 2^k < 45 then k ≤ 5 (since 2^6 = 64 ≥ 45). -/
lemma k_le_5_of_pow_lt {k : ℕ} (h : 2 ^ k < 45) : k ≤ 5 := by
  by_contra hnot
  have h6 : 6 ≤ k := by omega
  have hp : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h6
  have : 2 ^ 6 < 45 := lt_of_le_of_lt hp h
  norm_num at this

/-- 43 is prime. -/
theorem prime_43 : Nat.Prime 43 := by norm_num

/-- 41 is prime. -/
theorem prime_41 : Nat.Prime 41 := by norm_num

/-- 37 is prime. -/
theorem prime_37 : Nat.Prime 37 := by norm_num

/-- 29 is prime. -/
theorem prime_29 : Nat.Prime 29 := by norm_num

/-- 13 is prime. -/
theorem prime_13 : Nat.Prime 13 := by norm_num

/-- All five differences 45 − 2ᵏ (k=1..5) are prime. -/
theorem diffs_prime :
    Nat.Prime (45 - 2) ∧ Nat.Prime (45 - 4) ∧ Nat.Prime (45 - 8) ∧
    Nat.Prime (45 - 16) ∧ Nat.Prime (45 - 32) := by
  norm_num

/-- Main theorem: there is an integer n whose differences from every permitted smaller
    power of two are all prime.  Witness: n = 45. -/
theorem jsp000947 :
    ∃ n : ℕ, ∀ k : ℕ, 1 ≤ k → 2 ^ k < n → Nat.Prime (n - 2 ^ k) := by
  refine ⟨45, ?_⟩
  intro k hk hklt
  have hk_le5 : k ≤ 5 := k_le_5_of_pow_lt hklt
  interval_cases k <;> norm_num

end JSP000947