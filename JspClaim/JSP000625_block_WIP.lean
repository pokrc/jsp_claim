import JspClaim.JSP000625_analytic_WIP
import JspClaim.JSP000625_kernel_WIP

/-!
# JSP-000625 — Block argument (WIP)

Implements the block argument for the Erdős–Fuchs theorem following plby's
structure (Erdos763.lean, ~1495 lines). This file builds the discrete
Parseval identity, indicator series, and the block-circle majorant/minorant
machinery that leads to the final contradiction.

Structure (following plby):
1. Definitions: `geometricBlock`, `blockCoefficient`, `indicatorSeriesReal`
2. Parseval: `block_parseval`, `block_parseval_lower`
3. Main term: `indicatorSeriesReal_sq_lower`
4. Circle majorant: `block_circle_upper`, `block_circle_lower`
5. Chosen radius: `chosenRadius`, final contradiction
-/

open Finset Complex MeasureTheory
open scoped BigOperators

noncomputable section

namespace JSP000625Block

variable {A : Set ℕ}

-- ============================================================
-- §1. Core definitions
-- ============================================================

/-- Indicator of `A` valued in `ℕ` (0 or 1). -/
def indicator (A : Set ℕ) (n : ℕ) : ℕ := by
  classical exact if n ∈ A then 1 else 0

/-- The Dirichlet-type block: `geometricBlock M z = Σ_{k<M} z^k`. -/
def geometricBlock (M : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range M, z ^ k

/-- Block coefficients: `blockCoefficient A M n = Σ_{k<M} A(n-k)` (truncated convolution). -/
def blockCoefficient (A : Set ℕ) (M n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range M, if k ≤ n then indicator A (n - k) else 0

/-- Real indicator series evaluated at `q`: `Σ_{n≥0} (Σ_{k<M} A(n-k)) · q^n`. -/
def indicatorSeriesReal (A : Set ℕ) (M : ℕ) (q : ℝ) : ℝ :=
  ∑' n : ℕ, (blockCoefficient A M n : ℝ) * q ^ n

-- ============================================================
-- §2. Basic bounds
-- ============================================================

/-- The `ℕ`-valued indicator takes values `≤ 1`. -/
lemma indicator_le_one (A : Set ℕ) (n : ℕ) : indicator A n ≤ 1 := by
  unfold indicator
  by_cases h : n ∈ A <;> simp [h]

/-- Each block coefficient is bounded by the block length `M`. -/
lemma blockCoefficient_le (A : Set ℕ) (M n : ℕ) : blockCoefficient A M n ≤ M := by
  rw [blockCoefficient]
  calc
    (∑ k ∈ Finset.range M, if k ≤ n then indicator A (n - k) else 0) ≤
        ∑ _k ∈ Finset.range M, (1 : ℕ) := by
      refine Finset.sum_le_sum ?_
      intro k hk
      by_cases h : k ≤ n <;> simp [h, indicator_le_one A (n - k)]
    _ = M := by simp

/-- Norm of the geometric block on the unit circle: `‖Σ_{k<M} w^k‖ ≤ M`. -/
lemma geometricBlock_norm_le (M : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖geometricBlock M w‖ ≤ (M : ℝ) := by
  unfold geometricBlock
  calc
    ‖∑ k ∈ Finset.range M, w ^ k‖ ≤ ∑ k ∈ Finset.range M, ‖w ^ k‖ := by
      exact norm_sum_le (s := Finset.range M) (f := fun k : ℕ => w ^ k)
    _ ≤ ∑ _k ∈ Finset.range M, (1 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro k hk
      calc
        ‖w ^ k‖ = ‖w‖ ^ k := by rw [norm_pow]
        _ ≤ 1 := pow_le_one₀ (norm_nonneg w) hw
    _ = (M : ℝ) := by simp

-- ============================================================
-- §3. Representation counts and the error sequence
-- ============================================================

/-- Ordered representation count `r(n) = Σ_{a=0}^{n} 1_A(a)·1_A(n-a)`. -/
def representationCount (A : Set ℕ) (n : ℕ) : ℕ :=
  ∑ a ∈ Finset.range (n + 1), indicator A a * indicator A (n - a)

/-- Cumulative representation count `R(N) = Σ_{n≤N} r(n)`. -/
def summatoryRepresentationCount (A : Set ℕ) (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), representationCount A n

/-- Normalized error `ε(n) = R(n) - c·(n+1)`. -/
def summatoryError (A : Set ℕ) (c : ℝ) (n : ℕ) : ℝ :=
  (summatoryRepresentationCount A n : ℝ) - c * (n + 1)

-- `R(N+1) = R(N) + r(N+1)`
lemma summatoryRepresentationCount_succ (A : Set ℕ) (n : ℕ) :
    summatoryRepresentationCount A (n + 1) =
      summatoryRepresentationCount A n + representationCount A (n + 1) := by
  simp only [summatoryRepresentationCount]
  rw [Finset.sum_range_succ]

-- `R(N) = R(N-1) + r(N)` for `N ≥ 1`
lemma summatoryRepresentationCount_diff (A : Set ℕ) {n : ℕ} (hn : 0 < n) :
    summatoryRepresentationCount A n =
      summatoryRepresentationCount A (n - 1) + representationCount A n := by
  have h := summatoryRepresentationCount_succ A (n - 1)
  have h1 : (n - 1 : ℕ) + 1 = n := by omega
  simpa [h1] using h

-- `ε(n) - ε(n-1) = r(n) - c` for `n ≥ 1`: the key difference identity
lemma summatoryError_diff (A : Set ℕ) {c : ℝ} {n : ℕ} (hn : 0 < n) :
    summatoryError A c n - summatoryError A c (n - 1) =
      (representationCount A n : ℝ) - c := by
  rw [summatoryError, summatoryError, summatoryRepresentationCount_diff A hn]
  push_cast
  have h1 : (↑(n - 1) : ℝ) + 1 = (↑n : ℝ) := by norm_cast; omega
  rw [h1]
  ring

-- ============================================================
-- §4. Representation series identity and error bound
-- ============================================================

/-- Shifted error: `δ(n) = 0` for `n = 0`, and `ε(n-1)` for `n ≥ 1`. -/
def deltaError (A : Set ℕ) (c : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else summatoryError A c (n - 1)

/-- Pointwise identity in `ℝ`: `r(n) = c + ε(n) - δ(n)`. -/
lemma representationCount_eq_error (c : ℝ) (n : ℕ) :
    (representationCount A n : ℝ) = c + summatoryError A c n - deltaError A c n := by
  unfold deltaError
  by_cases hn : n = 0
  · subst n
    unfold summatoryError summatoryRepresentationCount
    simp
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have hdiff := summatoryError_diff A (c := c) (n := n) hpos
    have h1 : c + summatoryError A c n - summatoryError A c (n - 1) =
        (representationCount A n : ℝ) := by
      calc
        c + summatoryError A c n - summatoryError A c (n - 1) =
            c + (summatoryError A c n - summatoryError A c (n - 1)) := by ring
        _ = c + ((representationCount A n : ℝ) - c) := by rw [hdiff]
        _ = (representationCount A n : ℝ) := by ring
    simpa [hn] using h1.symm

/-- Pointwise identity lifted to `ℂ`. -/
lemma representationCount_eq_error_c (c : ℝ) (n : ℕ) :
    (representationCount A n : ℂ) = (c : ℂ) + (summatoryError A c n : ℂ) -
      (deltaError A c n : ℂ) := by
  exact_mod_cast representationCount_eq_error c n

-- Summability of the error series at z with ‖z‖ < 1
private lemma errorSeries_summable {c : ℝ} {z : ℂ} (hz : ‖z‖ < 1) {D : ℝ}
    (hbound : ∀ n, ‖summatoryError A c n‖ ≤ D) :
    Summable (fun n : ℕ => (summatoryError A c n : ℂ) * z ^ n) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => D * ‖z‖ ^ n)
  · exact (summable_geometric_of_norm_lt_one (x := ‖z‖) (by simpa using hz)).mul_left D
  · intro n
    calc
      ‖(summatoryError A c n : ℂ) * z ^ n‖ =
          ‖(summatoryError A c n : ℂ)‖ * ‖z ^ n‖ := norm_mul _ _
      _ = ‖summatoryError A c n‖ * ‖z ^ n‖ := by rw [Complex.norm_real]
      _ ≤ D * ‖z ^ n‖ := by gcongr; exact hbound n
      _ = D * ‖z‖ ^ n := by rw [norm_pow]

-- Summability of the shifted delta series
private lemma deltaErrorSeries_summable {c : ℝ} {z : ℂ} (hz : ‖z‖ < 1) {D : ℝ}
    (hbound : ∀ n, ‖summatoryError A c n‖ ≤ D) :
    Summable (fun n : ℕ => (deltaError A c n : ℂ) * z ^ n) := by
  have hshift :
      Summable (fun n : ℕ => (deltaError A c (n + 1) : ℂ) * z ^ (n + 1)) := by
    have hδ :
        (fun n : ℕ => (deltaError A c (n + 1) : ℂ) * z ^ (n + 1)) =
          fun n : ℕ => (summatoryError A c n : ℂ) * z ^ (n + 1) := by
      funext n; simp [deltaError]
    rw [hδ]
    have hzpow :
        (fun n : ℕ => (summatoryError A c n : ℂ) * z ^ (n + 1)) =
          fun n : ℕ => z * ((summatoryError A c n : ℂ) * z ^ n) := by
      funext n; rw [pow_succ']; ring
    rw [hzpow]
    exact (errorSeries_summable hz hbound).mul_left z
  exact (summable_nat_add_iff 1).mp hshift

-- The key shift identity: ∑'n δ(n)z^n = z * ∑'n ε(n)z^n
private lemma deltaError_tsum {c : ℝ} {z : ℂ} (hz : ‖z‖ < 1) {D : ℝ}
    (hbound : ∀ n, ‖summatoryError A c n‖ ≤ D) :
    (∑' n : ℕ, (deltaError A c n : ℂ) * z ^ n) =
      z * (∑' n : ℕ, (summatoryError A c n : ℂ) * z ^ n) := by
  have hsummable1 :
      Summable (fun n : ℕ => (deltaError A c (n + 1) : ℂ) * z ^ (n + 1)) := by
    have hδ :
        (fun n : ℕ => (deltaError A c (n + 1) : ℂ) * z ^ (n + 1)) =
          fun n : ℕ => (summatoryError A c n : ℂ) * z ^ (n + 1) := by
      funext n; simp [deltaError]
    rw [hδ]
    have hzpow :
        (fun n : ℕ => (summatoryError A c n : ℂ) * z ^ (n + 1)) =
          fun n : ℕ => z * ((summatoryError A c n : ℂ) * z ^ n) := by
      funext n; rw [pow_succ']; ring
    rw [hzpow]
    exact (errorSeries_summable hz hbound).mul_left z
  have htz := tsum_eq_zero_add'
    (f := fun n : ℕ => (deltaError A c n : ℂ) * z ^ n) hsummable1
  calc
    (∑' n : ℕ, (deltaError A c n : ℂ) * z ^ n)
        = (deltaError A c 0 : ℂ) * z ^ 0 +
            (∑' n : ℕ, (deltaError A c (n + 1) : ℂ) * z ^ (n + 1)) := htz
    _ = 0 + (∑' n : ℕ, (deltaError A c (n + 1) : ℂ) * z ^ (n + 1)) := by
        simp [deltaError]
    _ = (∑' n : ℕ, (deltaError A c (n + 1) : ℂ) * z ^ (n + 1)) := by ring
    _ = (∑' n : ℕ, (summatoryError A c n : ℂ) * z ^ (n + 1)) := by
        apply tsum_congr; intro n; simp [deltaError]
    _ = (∑' n : ℕ, z * ((summatoryError A c n : ℂ) * z ^ n)) := by
        apply tsum_congr; intro n; rw [pow_succ']; ring
    _ = z * (∑' n : ℕ, (summatoryError A c n : ℂ) * z ^ n) := by rw [tsum_mul_left]

/-- **Representation series identity.** For `‖z‖ < 1` and `‖ε(n)‖ ≤ D`:
  `∑ r(n)z^n = c/(1−z) + (1−z)·∑ ε(n)z^n`.
  Proved by the pointwise identity `r(n) = c + ε(n) − δ(n)`, the geometric
  series `∑ cz^n = c/(1−z)`, and the shift `∑ δ(n)z^n = z·∑ ε(n)z^n`. -/
lemma representation_series_identity {c : ℝ} {z : ℂ}
    (hz : ‖z‖ < 1) (D : ℝ) (hD : 0 ≤ D) (hbound : ∀ n, ‖summatoryError A c n‖ ≤ D) :
    (∑' n : ℕ, (representationCount A n : ℂ) * z ^ n) =
      (c : ℂ) / (1 - z) + (1 - z) *
        ∑' n : ℕ, (summatoryError A c n : ℂ) * z ^ n := by
  have hεsum := errorSeries_summable hz hbound
  have hδsum := deltaErrorSeries_summable hz hbound
  have hcsum : Summable (fun n : ℕ => (c : ℂ) * z ^ n) :=
    (summable_geometric_of_norm_lt_one (x := z) hz).mul_left (c : ℂ)
  -- Step 1: split ∑ r(n)z^n = ∑ cz^n + ∑ ε(n)z^n − ∑ δ(n)z^n
  have hsplit :
      (∑' n : ℕ, (representationCount A n : ℂ) * z ^ n) =
        (∑' n : ℕ, (c : ℂ) * z ^ n) +
          (∑' n : ℕ, (summatoryError A c n : ℂ) * z ^ n) -
            (∑' n : ℕ, (deltaError A c n : ℂ) * z ^ n) := by
    calc
      (∑' n, (representationCount A n : ℂ) * z ^ n)
          = ∑' n, ((c : ℂ) + (summatoryError A c n : ℂ) - (deltaError A c n : ℂ)) * z ^ n := by
            apply tsum_congr; intro n
            rw [representationCount_eq_error_c c n]
      _ = ∑' n, ((c : ℂ) * z ^ n + (summatoryError A c n : ℂ) * z ^ n -
            (deltaError A c n : ℂ) * z ^ n) := by
            apply tsum_congr; intro n; ring
      _ = (∑' n, (c : ℂ) * z ^ n) + (∑' n, (summatoryError A c n : ℂ) * z ^ n) -
            (∑' n, (deltaError A c n : ℂ) * z ^ n) := by
            have hsumfg := hcsum.add hεsum
            rw [Summable.tsum_sub hsumfg hδsum, Summable.tsum_add hcsum hεsum]
  -- Step 2: geometric series
  have hgeomsum : (∑' n, (c : ℂ) * z ^ n) = (c : ℂ) * (1 - z)⁻¹ :=
    (hasSum_geometric_of_norm_lt_one hz).mul_left (c : ℂ) |>.tsum_eq
  -- Step 3: shift identity
  have hδshift : (∑' n, (deltaError A c n : ℂ) * z ^ n) =
      z * (∑' n, (summatoryError A c n : ℂ) * z ^ n) :=
    deltaError_tsum hz hbound
  -- Step 4: assemble
  calc
    (∑' n, (representationCount A n : ℂ) * z ^ n)
        = (∑' n, (c : ℂ) * z ^ n) +
            (∑' n, (summatoryError A c n : ℂ) * z ^ n) -
              (∑' n, (deltaError A c n : ℂ) * z ^ n) := hsplit
    _ = (c : ℂ) * (1 - z)⁻¹ +
            (∑' n, (summatoryError A c n : ℂ) * z ^ n) -
              (z * (∑' n, (summatoryError A c n : ℂ) * z ^ n)) := by
          rw [hgeomsum, hδshift]
    _ = (c : ℂ) * (1 - z)⁻¹ + (1 - z) *
            (∑' n, (summatoryError A c n : ℂ) * z ^ n) := by ring
    _ = (c : ℂ) / (1 - z) + (1 - z) *
            (∑' n, (summatoryError A c n : ℂ) * z ^ n) := by ring

/-- **Error-series norm bound.** For `0 ≤ q < 1` and `‖ε(n)‖ ≤ D`:
  `‖∑ ε(n)q^n‖ ≤ D/(1−q)`. -/
lemma errorSeries_norm_le {c D q : ℝ} (hD : 0 ≤ D)
    (he : ∀ n, ‖summatoryError A c n‖ ≤ D) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ‖∑' n : ℕ, (summatoryError A c n : ℂ) * (q : ℂ) ^ n‖ ≤ D / (1 - q) := by
  have hq_norm : ‖q‖ = q := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]
  have hq_lt : ‖q‖ < 1 := by rwa [hq_norm]
  -- geometric summability of D * q^n
  have hg : Summable (fun n : ℕ => D * q ^ n) :=
    (summable_geometric_of_norm_lt_one hq_lt).mul_left D
  -- ‖(q : ℂ)^n‖ = q^n
  have hqpow (n : ℕ) : ‖(q : ℂ) ^ n‖ = q ^ n := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
  -- pointwise norm bound
  have hterm : ∀ n : ℕ, ‖(summatoryError A c n : ℂ) * (q : ℂ) ^ n‖ ≤ D * q ^ n := by
    intro n
    calc
      ‖(summatoryError A c n : ℂ) * (q : ℂ) ^ n‖ =
          ‖(summatoryError A c n : ℂ)‖ * ‖(q : ℂ) ^ n‖ := norm_mul _ _
      _ = ‖summatoryError A c n‖ * ‖(q : ℂ) ^ n‖ := by rw [Complex.norm_real]
      _ = ‖summatoryError A c n‖ * q ^ n := by rw [hqpow n]
      _ ≤ D * q ^ n := by gcongr; exact he n
  -- summability of the complex series
  have hsum := Summable.of_norm_bounded
    (g := fun n : ℕ => D * q ^ n) hg hterm
  -- summability of the norm series
  have hsumNorm : Summable (fun n : ℕ =>
      ‖(summatoryError A c n : ℂ) * (q : ℂ) ^ n‖) :=
    Summable.of_nonneg_of_le
      (g := fun n : ℕ => ‖(summatoryError A c n : ℂ) * (q : ℂ) ^ n‖)
      (f := fun n : ℕ => D * q ^ n)
      (fun n => norm_nonneg _) (fun n => hterm n) hg
  -- ‖∑ a_n‖ ≤ ∑ ‖a_n‖ ≤ ∑ D*q^n = D/(1−q)
  have hgeomsum : (∑' n : ℕ, (q : ℝ) ^ n) = (1 - q)⁻¹ :=
    (hasSum_geometric_of_norm_lt_one hq_lt).tsum_eq
  calc
    ‖∑' n, (summatoryError A c n : ℂ) * (q : ℂ) ^ n‖
        ≤ ∑' n, ‖(summatoryError A c n : ℂ) * (q : ℂ) ^ n‖ :=
          norm_tsum_le_tsum_norm hsumNorm
    _ ≤ ∑' n, D * q ^ n :=
          Summable.tsum_le_tsum (fun n => hterm n) hsumNorm hg
    _ = D * (∑' n, (q : ℝ) ^ n) := by rw [tsum_mul_left]
    _ = D * (1 - q)⁻¹ := by rw [hgeomsum]
    _ = D / (1 - q) := by ring



variable {A : Set ℕ}

-- ============================================================
-- §1. `M = 1` simplification
-- ============================================================

/-- With block length `1`, the block coefficient is the plain indicator. -/
lemma blockCoefficient_one (A : Set ℕ) (n : ℕ) : blockCoefficient A 1 n = indicator A n := by
  unfold blockCoefficient
  simp

/-- `indicatorSeriesReal A 1 q` is the plain indicator power series. -/
lemma indicatorSeriesReal_one (A : Set ℕ) (q : ℝ) :
    indicatorSeriesReal A 1 q = ∑' n : ℕ, (indicator A n : ℝ) * q ^ n := by
  unfold indicatorSeriesReal
  simp [blockCoefficient_one]

-- ============================================================
-- §2. Summability
-- ============================================================

/-- `‖indicator A n‖ ≤ 1` as a real number. -/
lemma indicator_norm_le_one (A : Set ℕ) (n : ℕ) : ‖(indicator A n : ℝ)‖ ≤ 1 := by
  by_cases hn : n ∈ A <;> simp [indicator, hn]

/-- The indicator power series is absolutely summable for `0 ≤ q < 1`. -/
lemma summable_norm_indicatorSeries (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => ‖(indicator A n : ℝ) * q ^ n‖) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => q ^ n) ?_ ?_
  · exact (hasSum_geometric_of_lt_one hq0 hq1).summable
  · intro n
    calc
      ‖‖(indicator A n : ℝ) * q ^ n‖‖ = ‖(indicator A n : ℝ) * q ^ n‖ := norm_norm _
      _ = ‖(indicator A n : ℝ)‖ * ‖q ^ n‖ := by rw [norm_mul]
      _ = ‖(indicator A n : ℝ)‖ * q ^ n := by
          rw [Real.norm_of_nonneg (pow_nonneg hq0 n)]
      _ ≤ 1 * q ^ n := mul_le_mul_of_nonneg_right (indicator_norm_le_one A n) (pow_nonneg hq0 n)
      _ = q ^ n := by ring

/-- The indicator power series is summable for `0 ≤ q < 1`. -/
lemma summable_indicatorSeries (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => (indicator A n : ℝ) * q ^ n) :=
  (summable_norm_indicatorSeries hq0 hq1).of_norm

/-- The error series is (absolutely) summable for `0 ≤ q < 1` given the uniform
bound `‖ε n‖ ≤ D`. -/
lemma summable_norm_errorSeries {c D q : ℝ} (he : ∀ n, ‖summatoryError A c n‖ ≤ D)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => ‖summatoryError A c n * q ^ n‖) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => D * q ^ n) ?_ ?_
  · exact (hasSum_geometric_of_lt_one hq0 hq1).summable.mul_left D
  · intro n
    calc
      ‖‖summatoryError A c n * q ^ n‖‖ = ‖summatoryError A c n * q ^ n‖ := norm_norm _
      _ = ‖summatoryError A c n‖ * ‖q ^ n‖ := by rw [norm_mul]
      _ = ‖summatoryError A c n‖ * q ^ n := by
          rw [Real.norm_of_nonneg (pow_nonneg hq0 n)]
      _ ≤ D * q ^ n := mul_le_mul_of_nonneg_right (he n) (pow_nonneg hq0 n)

/-- The error series is summable for `0 ≤ q < 1` given the uniform bound `‖ε n‖ ≤ D`. -/
lemma summable_errorSeries {c D q : ℝ} (he : ∀ n, ‖summatoryError A c n‖ ≤ D)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => summatoryError A c n * q ^ n) :=
  (summable_norm_errorSeries he hq0 hq1).of_norm

-- ============================================================
-- §3. Cauchy square: `g(q)^2 = ∑' r(n) q^n`
-- ============================================================

/-- `g(q)^2` with `g(q) = ∑' (indicator A n : ℝ) q^n` equals the representation
series `∑' (representationCount A n : ℝ) q^n` (Cauchy product). -/
lemma indicatorSeries_sq_eq_representationSeries (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' n : ℕ, (indicator A n : ℝ) * q ^ n) ^ 2 =
      ∑' n : ℕ, (representationCount A n : ℝ) * q ^ n := by
  calc
    (∑' n : ℕ, (indicator A n : ℝ) * q ^ n) ^ 2
        = (∑' n : ℕ, (indicator A n : ℝ) * q ^ n) *
            (∑' n : ℕ, (indicator A n : ℝ) * q ^ n) := by ring
    _ = ∑' n : ℕ,
          ∑ k ∈ Finset.range (n + 1),
            ((indicator A k : ℝ) * q ^ k) * ((indicator A (n - k) : ℝ) * q ^ (n - k)) := by
        rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
          (summable_norm_indicatorSeries hq0 hq1) (summable_norm_indicatorSeries hq0 hq1)]
    _ = ∑' n : ℕ, (representationCount A n : ℝ) * q ^ n := by
        apply tsum_congr
        intro n
        calc
          (∑ k ∈ Finset.range (n + 1),
              ((indicator A k : ℝ) * q ^ k) * ((indicator A (n - k) : ℝ) * q ^ (n - k)))
              = (∑ k ∈ Finset.range (n + 1),
                    (indicator A k : ℝ) * (indicator A (n - k) : ℝ) * q ^ n) := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
                  have hpow : q ^ k * q ^ (n - k) = q ^ n := by
                    calc q ^ k * q ^ (n - k) = q ^ (k + (n - k)) := (pow_add q k (n - k)).symm
                      _ = q ^ n := by rw [add_comm, Nat.sub_add_cancel hk_le]
                  calc
                    ((indicator A k : ℝ) * q ^ k) * ((indicator A (n - k) : ℝ) * q ^ (n - k))
                        = (indicator A k : ℝ) * (indicator A (n - k) : ℝ) * (q ^ k * q ^ (n - k)) := by
                            ring
                    _ = (indicator A k : ℝ) * (indicator A (n - k) : ℝ) * q ^ n := by rw [hpow]
          _ = (∑ k ∈ Finset.range (n + 1),
                  (indicator A k : ℝ) * (indicator A (n - k) : ℝ)) * q ^ n := by
                  rw [Finset.sum_mul]
          _ = (representationCount A n : ℝ) * q ^ n := by
                  rw [representationCount]
                  congr 1
                  push_cast
                  rfl

-- ============================================================
-- §4. Telescoping identity: `∑' r(n) q^n = c/(1−q) + (1−q)·H(q)`
-- ============================================================

/-- The representation series equals the main geometric term plus the error series:
`∑' r(n) q^n = c/(1−q) + (1−q)·∑' ε(n) q^n`.

This is the real version of `representation_series_identity` (a complex version is being
added to `JSP000625_block_WIP` by another agent), proven directly here from
`summatoryError_diff` (`ε(n) − ε(n−1) = r(n) − c`). -/
lemma lower_representationSeries_identity {c D q : ℝ} (he : ∀ n, ‖summatoryError A c n‖ ≤ D)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' n : ℕ, (representationCount A n : ℝ) * q ^ n) =
      c / (1 - q) + (1 - q) * (∑' n : ℕ, summatoryError A c n * q ^ n) := by
  let v : ℕ → ℝ := fun n => if n = 0 then 0 else summatoryError A c (n - 1) * q ^ n
  have hsumq : Summable (fun n : ℕ => q ^ n) := (hasSum_geometric_of_lt_one hq0 hq1).summable
  have hsu : HasSum (fun n : ℕ => q ^ n) ((1 - q)⁻¹) := hasSum_geometric_of_lt_one hq0 hq1
  have hε : Summable (fun n : ℕ => summatoryError A c n * q ^ n) :=
    summable_errorSeries he hq0 hq1
  have hsumc : Summable (fun n : ℕ => c * q ^ n) := hsumq.mul_left c
  have hsumcu : Summable (fun n : ℕ => c * q ^ n + summatoryError A c n * q ^ n) :=
    hsumc.add hε
  -- pointwise identity: r(n)·q^n = c·q^n + ε(n)·q^n − v(n)
  have hpoint : ∀ n : ℕ,
      (representationCount A n : ℝ) * q ^ n =
        c * q ^ n + summatoryError A c n * q ^ n - v n := by
    intro n
    by_cases hn : n = 0
    · subst n
      have hε0 : summatoryError A c 0 = (representationCount A 0 : ℝ) - c := by
        simp [summatoryError, summatoryRepresentationCount]
      have hr0 : (representationCount A 0 : ℝ) = c + summatoryError A c 0 := by
        rw [hε0]
        ring
      simp [v]
      rw [hr0]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hdiff := summatoryError_diff A (c := c) hnpos
      have hr : (representationCount A n : ℝ) =
          c + summatoryError A c n - summatoryError A c (n - 1) := by
        linarith
      simp [v, hn]
      rw [hr]
      ring
  -- shifted series: `Σ' v = q·H(q)` and summability of `v`
  have hvw : ∀ n : ℕ, v (n + 1) = q * (summatoryError A c n * q ^ n) := by
    intro n
    simp [v]
    rw [pow_succ]
    ring
  have hw : Summable (fun n : ℕ => q * (summatoryError A c n * q ^ n)) := hε.mul_left q
  have hv0 : v 0 = 0 := by simp [v]
  have hg : HasSum (fun n : ℕ => v (n + 1))
      ((∑' n : ℕ, q * (summatoryError A c n * q ^ n)) - v 0) := by
    simpa [hvw, hv0] using hw.hasSum
  have hv : HasSum v (∑' n : ℕ, q * (summatoryError A c n * q ^ n)) := by
    have hmain := (hasSum_nat_add_iff (f := v) (k := 1)).1 hg
    simpa [hv0] using hmain
  have hsumv : Summable v := hv.summable
  have hsv : (∑' n : ℕ, v n) = q * (∑' n : ℕ, summatoryError A c n * q ^ n) := by
    calc
      (∑' n : ℕ, v n) = ∑' n : ℕ, q * (summatoryError A c n * q ^ n) := hv.tsum_eq
      _ = q * (∑' n : ℕ, summatoryError A c n * q ^ n) := by rw [tsum_mul_left]
  -- assemble
  calc
    (∑' n : ℕ, (representationCount A n : ℝ) * q ^ n)
        = ∑' n : ℕ, (c * q ^ n + summatoryError A c n * q ^ n - v n) := by
            apply tsum_congr
            intro n
            exact hpoint n
    _ = (∑' n : ℕ, (c * q ^ n + summatoryError A c n * q ^ n)) - ∑' n : ℕ, v n := by
            exact hsumcu.tsum_sub hsumv
    _ = (∑' n : ℕ, c * q ^ n) + (∑' n : ℕ, summatoryError A c n * q ^ n)
          - ∑' n : ℕ, v n := by
            exact congrArg (fun x : ℝ => x - ∑' n : ℕ, v n) (hsumc.tsum_add hε)
    _ = c * (∑' n : ℕ, q ^ n) + (∑' n : ℕ, summatoryError A c n * q ^ n)
          - q * (∑' n : ℕ, summatoryError A c n * q ^ n) := by
            rw [tsum_mul_left, hsv]
    _ = c / (1 - q) + (1 - q) * (∑' n : ℕ, summatoryError A c n * q ^ n) := by
            rw [hsu.tsum_eq]
            ring

-- ============================================================
-- §5. Error series bound: `‖H(q)‖ ≤ D/(1−q)`
-- ============================================================

/-- `‖∑' ε(n) q^n‖ ≤ D/(1−q)` for `0 ≤ q < 1` given the uniform bound `‖ε n‖ ≤ D`. -/
lemma lower_errorSeries_norm_le {c D q : ℝ} (he : ∀ n, ‖summatoryError A c n‖ ≤ D)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ‖∑' n : ℕ, summatoryError A c n * q ^ n‖ ≤ D / (1 - q) := by
  have hsumq : Summable (fun n : ℕ => q ^ n) := (hasSum_geometric_of_lt_one hq0 hq1).summable
  have hsu : HasSum (fun n : ℕ => q ^ n) ((1 - q)⁻¹) := hasSum_geometric_of_lt_one hq0 hq1
  have hnorm : Summable (fun n : ℕ => ‖summatoryError A c n * q ^ n‖) :=
    summable_norm_errorSeries he hq0 hq1
  have hbound : ∀ n : ℕ, ‖summatoryError A c n * q ^ n‖ ≤ D * q ^ n := by
    intro n
    calc
      ‖summatoryError A c n * q ^ n‖ = ‖summatoryError A c n‖ * ‖q ^ n‖ := by rw [norm_mul]
      _ = ‖summatoryError A c n‖ * q ^ n := by
          rw [Real.norm_of_nonneg (pow_nonneg hq0 n)]
      _ ≤ D * q ^ n := mul_le_mul_of_nonneg_right (he n) (pow_nonneg hq0 n)
  calc
    ‖∑' n : ℕ, summatoryError A c n * q ^ n‖
        ≤ ∑' n : ℕ, ‖summatoryError A c n * q ^ n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, D * q ^ n := hnorm.tsum_le_tsum hbound (hsumq.mul_left D)
    _ = D * ((1 - q)⁻¹) := by
        rw [tsum_mul_left, hsu.tsum_eq]
    _ = D / (1 - q) := by ring

-- ============================================================
-- §6. Main lower bound
-- ============================================================

/-- **Main goal.** `(indicatorSeriesReal A 1 q)^2 ≥ c/(1−q) − D` for `0 ≤ q < 1`,
under the uniform error bound `‖ε(n)‖ ≤ D`. -/
lemma indicatorSeriesReal_sq_lower {c D q : ℝ} (_hc : 0 < c) (hD : 0 ≤ D)
    (he : ∀ n, ‖summatoryError A c n‖ ≤ D) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    c / (1 - q) - D ≤ (indicatorSeriesReal A 1 q) ^ 2 := by
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  have hmain : (indicatorSeriesReal A 1 q) ^ 2 =
      c / (1 - q) + (1 - q) * (∑' n : ℕ, summatoryError A c n * q ^ n) := by
    rw [indicatorSeriesReal_one]
    rw [indicatorSeries_sq_eq_representationSeries hq0 hq1]
    rw [lower_representationSeries_identity he hq0 hq1]
  let H : ℝ := ∑' n : ℕ, summatoryError A c n * q ^ n
  have hnorm : ‖H‖ ≤ D / (1 - q) := by
    simpa [H] using lower_errorSeries_norm_le he hq0 hq1
  have habs : ‖(1 - q) * H‖ ≤ D := by
    calc
      ‖(1 - q) * H‖ = (1 - q) * ‖H‖ := by
          rw [norm_mul, Real.norm_of_nonneg h1q.le]
      _ ≤ (1 - q) * (D / (1 - q)) := mul_le_mul_of_nonneg_left hnorm h1q.le
      _ = D := mul_div_cancel₀ D h1q.ne'
  have hlower : -D ≤ (1 - q) * H := by
    have hx : |(1 - q) * H| ≤ D := by simpa using habs
    exact (abs_le.mp hx).1
  rw [hmain]
  linarith








variable {A : Set ℕ}

-- ============================================================
-- §1. Core definitions
-- ============================================================

/-- Coefficient of `w^m` in `(Σ_{k<M} w^k) · (Σ_{n<2M} c A n · w^n)`.
For `m < 2M` this equals `(blockCoefficient A M m : ℂ)`. -/
def productCoefficient (A : Set ℕ) (M m : ℕ) : ℂ :=
  ∑ k ∈ Finset.range M, if k ≤ m ∧ m - k < 2 * M
    then JSP000625Analytic.c A (m - k) else 0

/-- The block polynomial whose evaluation at `z` gives
`geometricBlock M ((r:ℂ)*z) · (Σ_{n<2M} c A n · ((r:ℂ)*z)^n)`. -/
def blockPoly (A : Set ℕ) (M : ℕ) (r : ℝ) : Polynomial ℂ :=
  (∑ k ∈ Finset.range M, Polynomial.monomial k ((r : ℂ) ^ k)) *
    (∑ n ∈ Finset.range (2 * M),
      Polynomial.monomial n (JSP000625Analytic.c A n * (r : ℂ) ^ n))

-- ============================================================
-- §2. Coefficient identity helpers
-- ============================================================

/-- Coefficients of the geometric-block factor. -/
private lemma geomFactor_coeff (M : ℕ) (r : ℝ) (i : ℕ) :
    ((∑ k ∈ Finset.range M, Polynomial.monomial k ((r : ℂ) ^ k)) : Polynomial ℂ).coeff i =
      if i < M then (r : ℂ) ^ i else 0 := by
  classical
  simp [Polynomial.coeff_monomial]

/-- Coefficients of the c-factor. -/
private lemma cFactor_coeff (A : Set ℕ) (M : ℕ) (r : ℝ) (j : ℕ) :
    ((∑ n ∈ Finset.range (2 * M), Polynomial.monomial n (JSP000625Analytic.c A n * (r : ℂ) ^ n)) :
          Polynomial ℂ).coeff j =
      if j < 2 * M then JSP000625Analytic.c A j * (r : ℂ) ^ j else 0 := by
  classical
  simp [Polynomial.coeff_monomial]

/-- The two filter sets for the guarded sum are extensionally equal. -/
private lemma guard_set_eq (M m : ℕ) :
    (Finset.range (m + 1)).filter (fun i => i < M ∧ m - i < 2 * M) =
      (Finset.range M).filter (fun k => k ≤ m ∧ m - k < 2 * M) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor <;> omega

/-- Sum over `range (m+1)` with antidiagonal guard equals `productCoefficient`. -/
private lemma sum_guard_eq_productCoeff (A : Set ℕ) (M m : ℕ) :
    (∑ i ∈ Finset.range (m + 1),
        if i < M ∧ m - i < 2 * M
        then JSP000625Analytic.c A (m - i) else 0) =
      productCoefficient A M m := by
  unfold productCoefficient
  rw [← Finset.sum_filter, ← Finset.sum_filter, guard_set_eq M m]

-- ============================================================
-- §3. blockPoly coefficient formula
-- ============================================================

/-- The m-th coefficient of `blockPoly` equals `(r:ℂ)^m · productCoefficient A M m`. -/
lemma blockPoly_coeff (A : Set ℕ) (M : ℕ) (r : ℝ) (m : ℕ) :
    (blockPoly A M r).coeff m = (r : ℂ) ^ m * productCoefficient A M m := by
  classical
  unfold blockPoly
  rw [Polynomial.coeff_mul]
  -- Convert antidiagonal sum to range (m+1)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j : ℕ =>
      ((∑ k ∈ Finset.range M, Polynomial.monomial k ((r : ℂ) ^ k)) : Polynomial ℂ).coeff i *
        ((∑ n ∈ Finset.range (2 * M),
            Polynomial.monomial n (JSP000625Analytic.c A n * (r : ℂ) ^ n)) : Polynomial ℂ).coeff j)]
  -- Factor out (r:ℂ)^m and relate to productCoefficient
  rw [← sum_guard_eq_productCoeff A M m, Finset.mul_sum]
  -- Term-by-term
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < m + 1 := Finset.mem_range.mp hi
  have hi_le : i ≤ m := by omega
  rw [geomFactor_coeff, cFactor_coeff]
  by_cases h1 : i < M <;> by_cases h2 : m - i < 2 * M <;> simp [h1, h2]
  · -- both conditions true: (r:ℂ)^i * (c A (m-i) * (r:ℂ)^(m-i)) = (r:ℂ)^m * c A (m-i)
    have hsum : i + (m - i) = m := by omega
    calc
      (r : ℂ) ^ i * (JSP000625Analytic.c A (m - i) * (r : ℂ) ^ (m - i))
          = JSP000625Analytic.c A (m - i) * ((r : ℂ) ^ i * (r : ℂ) ^ (m - i)) := by ring
      _ = JSP000625Analytic.c A (m - i) * (r : ℂ) ^ (i + (m - i)) := by
        rw [← pow_add]
      _ = JSP000625Analytic.c A (m - i) * (r : ℂ) ^ m := by rw [hsum]
      _ = (r : ℂ) ^ m * JSP000625Analytic.c A (m - i) := by ring

-- ============================================================
-- §4. productCoefficient = blockCoefficient for m < 2M
-- ============================================================

/-- For `m < 2M`, `productCoefficient` equals `blockCoefficient`. -/
lemma productCoefficient_eq_blockCoefficient (A : Set ℕ) (M : ℕ) {m : ℕ} (hm : m < 2 * M) :
    productCoefficient A M m = (blockCoefficient A M m : ℂ) := by
  unfold productCoefficient blockCoefficient
  have hset : (Finset.range M).filter (fun k => k ≤ m ∧ m - k < 2 * M) =
      (Finset.range M).filter (fun k => k ≤ m) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor <;> intro h <;> refine ⟨h.1, ?_⟩
    · exact h.2.1
    · omega
  calc
    (∑ k ∈ Finset.range M, if k ≤ m ∧ m - k < 2 * M then JSP000625Analytic.c A (m - k) else 0)
        = ∑ k ∈ (Finset.range M).filter (fun k => k ≤ m ∧ m - k < 2 * M),
            JSP000625Analytic.c A (m - k) := by
          rw [Finset.sum_filter]
    _ = ∑ k ∈ (Finset.range M).filter (fun k => k ≤ m),
            JSP000625Analytic.c A (m - k) := by
          rw [hset]
    _ = ∑ k ∈ (Finset.range M).filter (fun k => k ≤ m),
            ((indicator A (m - k) : ℕ) : ℂ) := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases h : m - k ∈ A <;> simp [JSP000625Analytic.c, indicator, h]
    _ = (∑ k ∈ Finset.range M, if k ≤ m then ((indicator A (m - k) : ℕ) : ℂ) else 0) := by
          rw [Finset.sum_filter]
    _ = ((∑ k ∈ Finset.range M, if k ≤ m then indicator A (m - k) else 0 : ℕ) : ℂ) := by
          push_cast
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hkm : k ≤ m <;> simp [hkm]

-- ============================================================
-- §5. Support and zero-coefficient lemmas
-- ============================================================

/-- `productCoefficient` vanishes above the product degree `3M - 2`. -/
lemma productCoefficient_eq_zero_of_le (A : Set ℕ) (M : ℕ) {m : ℕ} (hm : 3 * M - 1 ≤ m) :
    productCoefficient A M m = 0 := by
  unfold productCoefficient
  apply Finset.sum_eq_zero
  intro i hi
  have hiM : i < M := Finset.mem_range.mp hi
  by_cases hle : i ≤ m
  · have h2 : ¬ m - i < 2 * M := by
      have hMpos : 0 < M := by omega
      omega
    simp [hle, h2]
  · simp [hle]

/-- Support of `blockPoly` is contained in `range (3*M - 1)`. -/
lemma blockPoly_support_subset (A : Set ℕ) (M : ℕ) (r : ℝ) :
    (blockPoly A M r).support ⊆ Finset.range (3 * M - 1) := by
  intro m hm
  rw [Polynomial.mem_support_iff] at hm
  rw [Finset.mem_range]
  by_contra hnot
  apply hm
  rw [blockPoly_coeff]
  simp [productCoefficient_eq_zero_of_le A M (not_lt.mp hnot)]

-- ============================================================
-- §6. Eval identity
-- ============================================================

/-- Eval identity for blockPoly. -/
lemma blockPoly_eval (A : Set ℕ) (M : ℕ) (r : ℝ) (z : ℂ) :
    (blockPoly A M r).eval z =
      geometricBlock M ((r : ℂ) * z) *
        (∑ n ∈ Finset.range (2 * M),
          JSP000625Analytic.c A n * ((r : ℂ) * z) ^ n) := by
  unfold blockPoly
  rw [Polynomial.eval_mul]
  congr 1
  · -- geometric block factor
    rw [Polynomial.eval_finsetSum]
    unfold geometricBlock
    apply Finset.sum_congr rfl
    intro k _
    rw [Polynomial.eval_monomial, mul_pow]
  · -- c-factor
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro n _
    rw [Polynomial.eval_monomial, mul_pow]
    ring

-- ============================================================
-- §7. Block Parseval (full correct version)
-- ============================================================

/-- Norm of a real power: `‖(r:ℂ)^m‖² = r^(2m)` for `r ≥ 0`. -/
private lemma norm_real_pow (r : ℝ) (hr0 : 0 ≤ r) (m : ℕ) :
    ‖(r : ℂ) ^ m‖ ^ 2 = r ^ (2 * m) := by
  calc
    ‖(r : ℂ) ^ m‖ ^ 2 = (‖(r : ℂ)‖ ^ m) ^ 2 := by rw [norm_pow]
    _ = ‖(r : ℂ)‖ ^ (2 * m) := by
      calc
        (‖(r : ℂ)‖ ^ m) ^ 2 = ‖(r : ℂ)‖ ^ (m * 2) := by rw [pow_mul]
        _ = ‖(r : ℂ)‖ ^ (2 * m) := by rw [show m * 2 = 2 * m by ring]
    _ = r ^ (2 * m) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]

/-- **Block Parseval — full identity.** The circle average of the squared modulus
of the block generating function equals the sum of squared coefficient norms
weighted by powers of the radius. The sum runs over all degrees `m < 3M-1`
(the full support of the product polynomial). -/
lemma block_parseval (A : Set ℕ) (M : ℕ) {r : ℝ} (hr0 : 0 ≤ r) :
    Real.circleAverage
        (fun z : ℂ => ‖geometricBlock M ((r : ℂ) * z) *
          (∑ n ∈ Finset.range (2 * M),
            JSP000625Analytic.c A n * ((r : ℂ) * z) ^ n)‖ ^ 2) 0 1 =
      ∑ m ∈ Finset.range (3 * M - 1),
        ‖productCoefficient A M m‖ ^ 2 * r ^ (2 * m) := by
  classical
  have hp := (blockPoly A M r).sum_sq_norm_coeff_eq_circleAverage
  -- hp : (∑ i ∈ support, ‖coeff i‖²) = circleAverage (fun θ => ‖eval θ‖²) 0 1
  rw [show (fun z : ℂ => ‖geometricBlock M ((r : ℂ) * z) *
          (∑ n ∈ Finset.range (2 * M),
            JSP000625Analytic.c A n * ((r : ℂ) * z) ^ n)‖ ^ 2) =
      (fun z : ℂ => ‖(blockPoly A M r).eval z‖ ^ 2) from by
    funext z
    rw [← blockPoly_eval A M r z]]
  rw [← hp]
  rw [Finset.sum_subset (blockPoly_support_subset A M r)]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [blockPoly_coeff, norm_mul, mul_pow, norm_real_pow r hr0]
    ring
  · intro m _ hm
    simp only [Polynomial.mem_support_iff, ne_eq, not_not] at hm
    simp [hm]

-- ============================================================
-- §8. Coefficient identity for n < 2M (requested form)
-- ============================================================

/-- Coefficient identity for n < 2M: the blockPoly coefficient is
`blockCoefficient A M n · (r:ℂ)^n`. -/
lemma blockPoly_coeff_eq_blockCoefficient (A : Set ℕ) (M : ℕ) (r : ℝ) {n : ℕ}
    (hn : n < 2 * M) :
    (blockPoly A M r).coeff n = (blockCoefficient A M n : ℂ) * (r : ℂ) ^ n := by
  rw [blockPoly_coeff, productCoefficient_eq_blockCoefficient A M hn]
  ring

-- ============================================================
-- §9. Main-term lower bound
-- ============================================================

/-- Norm of the blockCoefficient cast to ℂ is the natural number. -/
private lemma norm_blockCoefficient (A : Set ℕ) (M n : ℕ) :
    ‖((blockCoefficient A M n : ℕ) : ℂ)‖ = (blockCoefficient A M n : ℝ) := by
  norm_cast

/-- **Main-term lower bound**: Σ_{n<2M} (blockCoefficient A M n)² · r^{2n} ≤ the
circle average. Drops the (nonneg) tail degrees `2M ≤ m < 3M-1`. This is the
bound usable for the Erdős–Fuchs contradiction. -/
lemma block_parseval_lower (A : Set ℕ) (M : ℕ) {r : ℝ} (hr0 : 0 ≤ r) :
    (∑ n ∈ Finset.range (2 * M), (blockCoefficient A M n : ℝ) ^ 2 * r ^ (2 * n)) ≤
      Real.circleAverage
        (fun z : ℂ => ‖geometricBlock M ((r : ℂ) * z) *
          (∑ n ∈ Finset.range (2 * M),
            JSP000625Analytic.c A n * ((r : ℂ) * z) ^ n)‖ ^ 2) 0 1 := by
  rw [block_parseval A M hr0]
  calc
    (∑ n ∈ Finset.range (2 * M), (blockCoefficient A M n : ℝ) ^ 2 * r ^ (2 * n))
        = ∑ n ∈ Finset.range (2 * M),
            ‖productCoefficient A M n‖ ^ 2 * r ^ (2 * n) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [productCoefficient_eq_blockCoefficient A M (Finset.mem_range.mp hn)]
          rw [norm_blockCoefficient]
    _ ≤ ∑ m ∈ Finset.range (3 * M - 1),
            ‖productCoefficient A M m‖ ^ 2 * r ^ (2 * m) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?hsubset ?hnonneg
          · intro n hn
            rw [Finset.mem_range] at hn ⊢
            by_cases hM : M = 0
            · subst hM
              omega
            · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
              omega
          · intro m _ _
            exact mul_nonneg (sq_nonneg _) (pow_nonneg hr0 _)





-- TODO(next rounds):
-- 6. Circle majorant: block_circle_upper, block_circle_lower
-- 7. Chosen radius and final contradiction

end JSP000625Block

end
