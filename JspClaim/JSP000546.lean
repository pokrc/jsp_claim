import Mathlib.Tactic

/-!
# JSP-000546 — Product of consecutive terms of an AP with coprime difference

**Problem:** Can a product of consecutive terms of an arithmetic progression
with coprime difference be a perfect power?

**Answer: YES.** A counterexample to the conjecture that it cannot:
the progression `18, 25, 32` (with `a = 18`, `d = 7`, `k = 3` consecutive terms)
has product `18 × 25 × 32 = 14400 = 120²`, a perfect square.
Since `gcd(18, 7) = 1`, the common difference is coprime to the first term.

Every step below is kernel-checked by `norm_num`.  No `sorry`.
-/

namespace JSP000546

/-- The complete answer to JSP-000546: the product of consecutive terms of the
arithmetic progression `a, a+d, a+2d, …` with `a = 18`, `d = 7` (coprime) can
be a perfect power.  Specifically `18 · 25 · 32 = 14400 = 120²`. -/
theorem jsp000546 :
    ∃ a d k : ℕ, 1 ≤ a ∧ 1 ≤ d ∧ Nat.Coprime a d ∧
      2 ≤ k ∧ (∃ e : ℕ, 2 ≤ e ∧
        (∏ i ∈ Finset.range k, (a + d * i)) = e ^ 2) := by
  refine ⟨18, 7, 3, ?_, ?_, ?_, ?_, ⟨120, ?_, ?_⟩⟩
  · -- 1 ≤ 18
    norm_num
  · -- 1 ≤ 7
    norm_num
  · -- Nat.Coprime 18 7
    norm_num
  · -- 2 ≤ 3
    norm_num
  · -- 2 ≤ 120
    norm_num
  · -- ∏ i ∈ Finset.range 3, (18 + 7 * i) = 120 ^ 2
    simp only [Finset.prod_range_succ]
    norm_num

end JSP000546
