import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# JSP-000625 — analytic foundation (WIP)

Companion to `JSP000625_WIP_draft.lean`. Develops the analytic scaffolding for
the Erdős–Fuchs bound using mathlib's built-in circle-average and polynomial
Parseval (`Polynomial.sum_sq_norm_coeff_eq_circleAverage`).

⚠️ WIP — proofs marked `sorry` are the remaining analytic core (kernel lemma,
circle-majorant estimates, block argument, final contradiction).
-/

open Finset

noncomputable section

namespace JSP000625Analytic

variable {A : Set ℕ}

/-- The indicator of `A` valued in `ℂ` (coefficients of the generating
function `g(z) = Σ_{a ∈ A} z^a`). -/
def c (A : Set ℕ) (n : ℕ) : ℂ := by classical exact if n ∈ A then 1 else 0

/-- `g(z) := Σ_{a ∈ A} z^a`, the generating function of `A ⊆ ℕ`. -/
def g (A : Set ℕ) (z : ℂ) : ℂ := ∑' n : ℕ, c A n * z ^ n

/-- `c A` is absolutely summable at `z` when `‖z‖ < 1` (geometric majorant). -/
lemma summable_c_mul_pow {z : ℂ} (hz : ‖z‖ < 1) : Summable (fun n : ℕ => c A n * z ^ n) := by
  classical
  apply Summable.of_norm_bounded (g := fun n : ℕ => ‖z‖ ^ n)
  · exact summable_geometric_of_norm_lt_one (x := ‖z‖) (by simpa using hz)
  · intro n
    calc
      ‖c A n * z ^ n‖ = ‖c A n‖ * ‖z‖ ^ n := by rw [norm_mul, norm_pow]
      _ ≤ 1 * ‖z‖ ^ n := by
        gcongr
        by_cases hn : n ∈ A <;> simp [c, hn]
      _ = ‖z‖ ^ n := by ring

/-- **Truncated Parseval.** The circle average of the squared modulus of the
truncated power series with coefficients `a n` scaled by radius `r` equals the
sum of the squared coefficient norms (`Parseval's identity for polynomials`). -/
lemma trunc_parseval (a : ℕ → ℂ) (r : ℝ) (hr0 : 0 ≤ r) (K : ℕ) :
    (∑ n ∈ Finset.range K, ‖a n‖ ^ 2 * r ^ (2 * n)) =
      Real.circleAverage
        (fun z : ℂ => ‖∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n‖ ^ 2) 0 1 := by
  classical
  let p : Polynomial ℂ := ∑ n ∈ Finset.range K, Polynomial.monomial n (a n * (r : ℂ) ^ n)
  have hpoly_eval : ∀ z : ℂ, p.eval z = ∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n := by
    intro z
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro n _
    rw [Polynomial.eval_monomial, mul_pow]
    ring
  have hsupp : p.support ⊆ Finset.range K := by
    intro n hn
    rw [Polynomial.mem_support_iff] at hn
    rw [Finset.mem_range]
    by_contra hnot
    apply hn
    simp [p, Polynomial.coeff_monomial, hnot]
  have h_circle :
      (fun z : ℂ => ‖∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n‖ ^ 2) =
        (fun z : ℂ => ‖p.eval z‖ ^ 2) := by
    funext z
    rw [← hpoly_eval z]
  have hp := p.sum_sq_norm_coeff_eq_circleAverage
  rw [h_circle]
  rw [← hp]
  rw [Finset.sum_subset hsupp]
  · apply Finset.sum_congr rfl
    intro n hn
    have hcoeff : p.coeff n = a n * (r : ℂ) ^ n := by
      simp [p, Polynomial.coeff_monomial, Finset.mem_range.mp hn]
    rw [hcoeff, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    ring
  · intro n _ hnsupp
    simp only [Polynomial.mem_support_iff, ne_eq, not_not] at hnsupp
    simp [hnsupp]

-- TODO(next rounds): kernel lemma (triangle-kernel Fourier coefficients ≥ 0),
-- circle majorants, block argument, final contradiction for `jsp000625`.

end JSP000625Analytic

end