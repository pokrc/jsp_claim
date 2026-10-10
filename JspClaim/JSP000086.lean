/-!
# JSP-000086 / Erdős Problem 68 — checked auxiliary facts

RESEARCH ONLY. This file does not prove irrationality.
Main problem: irrationality of ∑' n : ℕ, 1 / ((n+2)! - 1).
The exact target deliberately has no proof declaration.

The starting term is n=2 (equal to 1), not n=3.
References:
* https://www.erdosproblems.com/68
* https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/68.lean

No part of this module is an award-qualifying solution.
-/

import Mathlib

noncomputable section

namespace JSP000086

open scoped Topology

/-- The complete original series, explicitly re-indexed from n=2. -/
def factorialSeries : ℝ :=
  ∑' n : ℕ, (1 : ℝ) / (((n + 2).factorial : ℝ) - 1)

/-- The open Erdős #68 target, not assumed or proved in this module. -/
def OriginalQuestion : Prop := Irrational factorialSeries

/-- Statement-fidelity check, NOT an irrationality proof. -/
theorem exact_target :
    OriginalQuestion ↔
      Irrational (∑' n : ℕ, (1 : ℝ) /
        (((n + 2).factorial : ℝ) - 1)) := by
  rfl

/-- Elementary decomposition underlying S = (e - 2) + R.
This is an algebraic identity, not a claim about the arithmetic of R. -/
theorem reciprocal_decomposition (x : ℝ)
    (hx : x ≠ 0) (hx1 : x - 1 ≠ 0) :
    (1 : ℝ) / (x - 1) =
      1 / x + 1 / (x * (x - 1)) := by
  field_simp [hx, hx1]
  <;> ring

/-- The correction term is positive for x > 1. -/
theorem remainder_term_positive (x : ℝ) (hx : 1 < x) :
    0 < (1 : ℝ) / (x * (x - 1)) := by
  have h0 : (0 : ℝ) < x := by linarith
  have h1 : (0 : ℝ) < x - 1 := by linarith
  positivity

/-- A finite exact computation; deliberately NOT an irrationality result.
2!, 3!, and 4! contribute 1 + 1/5 + 1/23 = 143/115. -/
theorem first_three_terms :
    (1 : ℚ) / (((2 : ℕ).factorial : ℚ) - 1) +
      1 / (((3 : ℕ).factorial : ℚ) - 1) +
      1 / (((4 : ℕ).factorial : ℚ) - 1) = 143 / 115 := by
  norm_num [Nat.factorial]

/-- The naive product-denominator lower bound already exceeds 1 at N=5:
D₅ = (2!-1)(3!-1)(4!-1)(5!-1) = 13685;
the first omitted denominator is 6!-1 = 719.
Therefore D₅ * tail_5 > D₅/719 > 1. -/
theorem naive_product_obstruction_at_five :
    (1 : ℚ) < 13685 / 719 := by
  norm_num

end JSP000086

-- Reproducible audit of the *auxiliary* facts (not of the open conjecture).
#print axioms JSP000086.exact_target
#print axioms JSP000086.reciprocal_decomposition
#print axioms JSP000086.remainder_term_positive
#print axioms JSP000086.first_three_terms
#print axioms JSP000086.naive_product_obstruction_at_five
