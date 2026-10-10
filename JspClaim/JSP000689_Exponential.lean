import JspClaim.JSP000689

/-!
# JSP-000689 — explicit exponential growth consequence

The existing finite Erdős–Lovász theorem proves a degree lower bound
2^(r-1)/(4r). This module derives a literal exponential rate:
for every r ≥ 8, the same vertex has degree at least (9/8)^r.
This is a derived corollary, not an earlier-priority claim or an
infinite-hypergraph statement.
-/

namespace JSP000689

/-- For every r ≥ 8, the explicit Erdős–Lovász bound is at least (9/8)^r. -/
theorem exponential_bound_mul (r : ℕ) (hr : 8 ≤ r) :
    (9 / 8 : ℝ) ^ r * (4 * (r : ℝ)) ≤ (2 : ℝ) ^ (r - 1) := by
  induction r, hr using Nat.le_induction with
  | base =>
      norm_num
  | succ k hk ih =>
      have hk_real : (8 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hratio : (9 / 8 : ℝ) * ((k : ℝ) + 1) ≤ 2 * (k : ℝ) := by
        nlinarith
      have hexp : (2 : ℝ) ^ ((k + 1) - 1) = 2 * (2 : ℝ) ^ (k - 1) := by
        have hpos : 1 ≤ k := by omega
        calc
          (2 : ℝ) ^ ((k + 1) - 1) = (2 : ℝ) ^ k := by congr 1 <;> omega
          _ = (2 : ℝ) ^ ((k - 1) + 1) := by congr 1 <;> omega
          _ = 2 * (2 : ℝ) ^ (k - 1) := by rw [pow_succ]; ring
      calc
        (9 / 8 : ℝ) ^ (k + 1) * (4 * ((k + 1 : ℕ) : ℝ))
            = (9 / 8 : ℝ) ^ k * (4 * ((9 / 8 : ℝ) * ((k : ℝ) + 1))) := by
                rw [pow_succ]
                push_cast
                ring
        _ ≤ (9 / 8 : ℝ) ^ k * (4 * (2 * (k : ℝ))) := by
              apply mul_le_mul_of_nonneg_left
              · nlinarith [hratio]
              · positivity
        _ = 2 * ((9 / 8 : ℝ) ^ k * (4 * (k : ℝ))) := by ring
        _ ≤ 2 * (2 : ℝ) ^ (k - 1) := by nlinarith [ih]
        _ = (2 : ℝ) ^ ((k + 1) - 1) := hexp.symm

/-- The explicitly exponential rate extracted from 2^(r-1)/(4r). -/
theorem exponential_rate (r : ℕ) (hr : 8 ≤ r) :
    (9 / 8 : ℝ) ^ r ≤ (2 : ℝ) ^ (r - 1) / (4 * (r : ℝ)) := by
  have hpos : (0 : ℝ) < 4 * (r : ℝ) := by
    have hn : 0 < r := by omega
    exact mul_pos (by norm_num) (by exact_mod_cast hn)
  exact (le_div_iff₀ hpos).2 (exponential_bound_mul r hr)

/-- Direct exponential-growth consequence for finite 3-chromatic r-uniform
hypergraphs. Constant c=1/8 (so base 1+c=9/8); threshold r≥8. -/
theorem erdos_lovasz_exponential_finite
    (n r : ℕ) (hr : 8 ≤ r)
    (H : Hypergraph (Fin n)) (huniform : H.Uniform r)
    (hthree : H.RequiresThreeColors) :
    ∃ v : Fin n, (9 / 8 : ℝ) ^ r ≤ (H.degree v : ℝ) := by
  obtain ⟨v, hv⟩ :=
    erdos_lovasz_explicit_finite n r (by omega) H huniform hthree
  exact ⟨v, (exponential_rate r hr).trans hv⟩

end JSP000689
