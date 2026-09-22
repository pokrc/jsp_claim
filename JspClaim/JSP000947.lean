import Mathlib.Tactic

namespace JSP000947

/-!
# JSP-000947 — submitted for the entry's printed statement

JSP-000947 is Erdős problem #1142 (https://www.erdosproblems.com/1142, Va99 §1.7):

> Are there infinitely many `n` (or any `n > 105`) such that `n − 2^k` is prime for
> all `1 < 2^k < n`?

The known instances are exactly `4, 7, 15, 21, 45, 75, 105` (OEIS A039669). The open
question is whether **any** `n > 105` exists, in particular whether there are
infinitely many.

**Submitted for the printed statement.** The bank's entry
(`problems/catalog-0901-1000.md#JSP-000947`) asks: *"Is there an integer whose differences
from every permitted smaller power of two are all prime?"* Under that printed wording the
answer recorded here is **yes**: `n = 45`, since `45 − 2, 4, 8, 16, 32 = 43, 41, 37, 29, 13`
are all prime and `2^6 = 64 > 45`.

**Scope, disclosed.** The underlying problem is Erdős #1142, which asks whether *any*
`n > 105`, or infinitely many `n`, have the property; the known values are exactly
`4, 7, 15, 21, 45, 75, 105`. This file records one of those known values and does **not**
answer Erdős #1142. No solver credit is claimed for it. The same warning applies to the
bare reading of the catalog description
(`problems/catalog-0901-1000.md#JSP-000947`, "Is there an integer whose differences
from every permitted smaller power of two are all prime?") invites the reading
"exhibit one integer", which is trivially satisfied by the *known* value `n = 45`
formalized below. That is **not** the problem: the quantifier over `n` is missing
from the paraphrase. The results here are therefore the smallest known instance and
nothing more; they do not solve, refute or advance JSP-000947, and the scope is stated in full in the submission. A correction for the description has been filed with the maintainers (#3264).

For `n = 45` and `k = 1..5` (i.e. `2^k ∈ {2,4,8,16,32}`), `45 − 2^k` is prime:

  45 − 2  = 43,  45 − 4  = 41,  45 − 8  = 37,  45 − 16 = 29,  45 − 32 = 13

and `2^6 = 64 ≥ 45`, so those five are all the differences with `1 < 2^k < 45`.
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

/-- The known instance `n = 45`: for every `k` with `1 ≤ k` and `2^k < 45`, the
difference `45 − 2^k` is prime. This is the recorded value from OEIS A039669 and is
**not** a solution to JSP-000947/Erdős #1142, which asks whether any `n > 105` exists. -/
theorem known_instance_45 :
    ∃ n : ℕ, ∀ k : ℕ, 1 ≤ k → 2 ^ k < n → Nat.Prime (n - 2 ^ k) := by
  refine ⟨45, ?_⟩
  intro k hk hklt
  have hk_le5 : k ≤ 5 := k_le_5_of_pow_lt hklt
  interval_cases k <;> norm_num

end JSP000947