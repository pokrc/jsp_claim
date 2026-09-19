import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# JSP-000625 — nonnegative kernel

Triangle (Fejér-type) kernel `(1 − |θ|/α)⁺` on the circle.
Establishes: support, nonnegativity, continuity, and `∫_{-π}^{π} kern α θ dθ = α`.
-/

open Real intervalIntegral MeasureTheory

noncomputable section

namespace JSP000625Kernel

/-- Triangle kernel `(1 − |θ|/α)⁺`. -/
def kern (α : ℝ) (θ : ℝ) : ℝ := if |θ| ≤ α then 1 - |θ| / α else 0

lemma kern_support (α : ℝ) {θ : ℝ} (h : |θ| ≤ α) : kern α θ = 1 - |θ| / α := by
  simp [kern, h]

lemma kern_eq_zero_of_lt (α : ℝ) {θ : ℝ} (h : α < |θ|) : kern α θ = 0 := by
  simp [kern, not_le.mpr h]

/-- Kernel vanishes when `|θ| ≥ α` (including the boundary). -/
lemma kern_eq_zero_of_ge_abs {α : ℝ} (hα0 : 0 < α) {θ : ℝ} (h : α ≤ |θ|) :
    kern α θ = 0 := by
  unfold kern
  by_cases h2 : |θ| ≤ α
  · rw [if_pos h2]
    rw [le_antisymm h2 h, div_self hα0.ne', sub_self]
  · rw [if_neg h2]

/-- Nonnegativity for `α > 0`. -/
lemma kern_nonneg {α : ℝ} (hα : 0 < α) (θ : ℝ) : 0 ≤ kern α θ := by
  unfold kern
  by_cases h : |θ| ≤ α
  · rw [if_pos h]
    linarith [(div_le_one hα).2 h]
  · rw [if_neg h]

/-- `kern α θ = max (1 - |θ|/α) 0` for `α > 0`. -/
lemma kern_eq_max {α : ℝ} (hα0 : 0 < α) (θ : ℝ) :
    kern α θ = max (1 - |θ| / α) 0 := by
  unfold kern
  by_cases h : |θ| ≤ α
  · rw [if_pos h]
    rw [max_eq_left (by linarith [(div_le_one hα0).2 h] : 0 ≤ 1 - |θ| / α)]
  · rw [if_neg h]
    rw [max_eq_right (by
        have hlt : α < |θ| := not_le.mp h
        have hone : 1 < |θ| / α := (lt_div_iff₀ hα0).2 (by simpa using hlt)
        linarith)]

/-- Kernel is continuous for `α > 0`. -/
lemma kern_continuous {α : ℝ} (hα0 : 0 < α) : Continuous (kern α) := by
  rw [show kern α = fun θ => max (1 - |θ| / α) 0 from funext (kern_eq_max hα0)]
  exact Continuous.max (continuous_const.sub (continuous_abs.div_const α)) continuous_const

lemma kern_integrable {α : ℝ} (hα0 : 0 < α) (a b : ℝ) :
    IntervalIntegrable (kern α) volume a b :=
  (kern_continuous hα0).intervalIntegrable a b

/-- `∫_{-α}^{0} (1 + θ/α) dθ = α/2`. -/
lemma integral_half_left (α : ℝ) (hα0 : 0 < α) :
    ∫ θ in (-α : ℝ)..0, (1 + θ / α) = α / 2 := by
  have h1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (-α) 0 :=
    continuous_const.intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun θ : ℝ => θ / α) volume (-α) 0 :=
    (continuous_id.div_const α).intervalIntegrable _ _
  have hθα_eq : (fun θ : ℝ => θ / α) = fun θ : ℝ => (1 / α) * θ := by
    funext θ
    rw [div_eq_mul_inv]
    ring
  calc ∫ θ in (-α : ℝ)..0, (1 + θ / α)
      = (∫ θ in (-α : ℝ)..0, (1 : ℝ)) + ∫ θ in (-α : ℝ)..0, θ / α := by
          rw [integral_add h1 h2]
    _ = (0 - (-α)) * 1 + (1 / α) * ∫ θ in (-α : ℝ)..0, θ := by
          rw [intervalIntegral.integral_const, hθα_eq,
            intervalIntegral.integral_const_mul, integral_id]
          simp
    _ = α / 2 := by
          rw [integral_id]
          field_simp [hα0.ne']
          ring

/-- `∫_{0}^{α} (1 - θ/α) dθ = α/2`. -/
lemma integral_half_right (α : ℝ) (hα0 : 0 < α) :
    ∫ θ in (0 : ℝ)..α, (1 - θ / α) = α / 2 := by
  have h1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 α :=
    continuous_const.intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun θ : ℝ => θ / α) volume 0 α :=
    (continuous_id.div_const α).intervalIntegrable _ _
  have hθα_eq : (fun θ : ℝ => θ / α) = fun θ : ℝ => (1 / α) * θ := by
    funext θ
    rw [div_eq_mul_inv]
    ring
  calc ∫ θ in (0 : ℝ)..α, (1 - θ / α)
      = (∫ θ in (0 : ℝ)..α, (1 : ℝ)) - ∫ θ in (0 : ℝ)..α, θ / α := by
          rw [integral_sub h1 h2]
    _ = (α - 0) * 1 - (1 / α) * ∫ θ in (0 : ℝ)..α, θ := by
          rw [intervalIntegral.integral_const, hθα_eq,
            intervalIntegral.integral_const_mul, integral_id]
          simp
    _ = α / 2 := by
          rw [integral_id]
          field_simp [hα0.ne']
          ring

/-- `∫_{-α}^{α} kern α θ dθ = α`. -/
lemma kern_int_mid (α : ℝ) (hα0 : 0 < α) :
    ∫ θ in (-α : ℝ)..α, kern α θ = α := by
  have hEq_left : Set.EqOn (kern α) (fun θ : ℝ => 1 + θ / α) (Set.uIcc (-α) 0) := by
    intro θ hθ
    have hIcc := Set.uIcc_of_le (by linarith : (-α : ℝ) ≤ 0)
    have hmem := Set.mem_Icc.mp (by simpa [hIcc] using hθ)
    have habs : |θ| = -θ := abs_of_nonpos hmem.2
    rw [kern_support α (by rw [habs]; linarith), habs]; ring
  have hEq_right : Set.EqOn (kern α) (fun θ : ℝ => 1 - θ / α) (Set.uIcc 0 α) := by
    intro θ hθ
    have hIcc := Set.uIcc_of_le (hα0.le : (0 : ℝ) ≤ α)
    have hmem := Set.mem_Icc.mp (by simpa [hIcc] using hθ)
    have habs : |θ| = θ := abs_of_nonneg hmem.1
    rw [kern_support α (by rw [habs]; linarith)]
    rw [habs]
  have hInt := intervalIntegral.integral_add_adjacent_intervals
    (kern_integrable hα0 (-α) 0) (kern_integrable hα0 0 α)
  -- rewrite: ∫_{-α}^{α} kern = ∫_{-α}^{0} kern + ∫_{0}^{α} kern
  -- ∫_{-α}^{0} kern = ∫_{-α}^{0} (1+θ/α) = α/2
  -- ∫_{0}^{α} kern = ∫_{0}^{α} (1-θ/α) = α/2
  -- total: α
  calc ∫ θ in (-α : ℝ)..α, kern α θ
      = (∫ θ in (-α : ℝ)..0, kern α θ) + (∫ θ in (0 : ℝ)..α, kern α θ) := by
        exact (intervalIntegral.integral_add_adjacent_intervals
          (kern_integrable hα0 (-α) 0) (kern_integrable hα0 0 α)).symm
    _ = (∫ θ in (-α : ℝ)..0, (1 + θ / α)) + (∫ θ in (0 : ℝ)..α, kern α θ) := by
        rw [intervalIntegral.integral_congr hEq_left]
    _ = α / 2 + (∫ θ in (0 : ℝ)..α, kern α θ) := by rw [integral_half_left α hα0]
    _ = α / 2 + (∫ θ in (0 : ℝ)..α, (1 - θ / α)) := by
        rw [intervalIntegral.integral_congr hEq_right]
    _ = α / 2 + α / 2 := by rw [integral_half_right α hα0]
    _ = α := by ring

/-- **Main lemma:** `∫_{-π}^{π} kern α θ dθ = α` for `0 < α ≤ π`. -/
lemma kernel_int (α : ℝ) (hα0 : 0 < α) (hαπ : α ≤ π) :
    ∫ θ in (-π : ℝ)..π, kern α θ = α := by
  -- left tail: ∫_{-π}^{-α} kern = 0
  have h_left : ∫ θ in (-π : ℝ)..(-α), kern α θ = 0 := by
    have hEq : Set.EqOn (kern α) (fun _ : ℝ => 0) (Set.uIcc (-π) (-α)) := by
      intro θ hθ
      have hIcc := Set.uIcc_of_le (by linarith : (-π : ℝ) ≤ -α)
      have hmem := Set.mem_Icc.mp (by simpa [hIcc] using hθ)
      exact kern_eq_zero_of_ge_abs hα0 (by
        have hθ0 : θ ≤ 0 := by linarith
        rw [abs_of_nonpos hθ0]
        linarith)
    rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_zero]
  -- right tail: ∫_{α}^{π} kern = 0
  have h_right : ∫ θ in (α : ℝ)..π, kern α θ = 0 := by
    have hEq : Set.EqOn (kern α) (fun _ : ℝ => 0) (Set.uIcc α π) := by
      intro θ hθ
      have hIcc := Set.uIcc_of_le hαπ
      have hmem := Set.mem_Icc.mp (by simpa [hIcc] using hθ)
      exact kern_eq_zero_of_ge_abs hα0 (by rw [abs_of_nonneg (hα0.le.trans hmem.1)]; exact hmem.1)
    rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_zero]
  -- middle: ∫_{-α}^{α} kern = α
  have h_mid := kern_int_mid α hα0
  -- assemble: ∫_{-π}^{π} = ∫_{-π}^{-α} + ∫_{-α}^{α} + ∫_{α}^{π}
  have h1 : ∫ θ in (-π : ℝ)..π, kern α θ =
      (∫ θ in (-π : ℝ)..(-α), kern α θ) + (∫ θ in (-α : ℝ)..π, kern α θ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (kern_integrable hα0 (-π) (-α)) (kern_integrable hα0 (-α) π)]
  have h2 : ∫ θ in (-α : ℝ)..π, kern α θ =
      (∫ θ in (-α : ℝ)..α, kern α θ) + (∫ θ in (α : ℝ)..π, kern α θ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (kern_integrable hα0 (-α) α) (kern_integrable hα0 α π)]
  rw [h1, h2, h_left, h_right, h_mid]; ring
/-! ### Nonzero Fourier coefficients of the kernel are nonnegative -/

/-- Integrability of `θ ↦ kern α θ · cos (k·θ)` for `α > 0`. -/
lemma kern_cos_integrable {α : ℝ} (hα0 : 0 < α) (k : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => kern α θ * cos (k * θ)) volume a b :=
  ((kern_continuous hα0).mul (continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable a b

/-- `∫₀ᵃ sin (k·θ) dθ = (1 - cos (k·a)) / k` for `k ≠ 0`. -/
lemma integral_sin_const_mul (k : ℝ) (hk : k ≠ 0) (a : ℝ) :
    ∫ θ in (0 : ℝ)..a, sin (k * θ) = (1 - cos (k * a)) / k := by
  have hsubst : ∫ θ in (0 : ℝ)..a, sin (k * θ) * k = ∫ t in (0 : ℝ)..(k * a), sin t := by
    have hsub := intervalIntegral.integral_comp_mul_deriv (f := fun θ : ℝ => k * θ)
      (f' := fun _ : ℝ => k) (g := sin) (a := 0) (b := a)
      (by intro x hx; exact hasDerivAt_const_mul k)
      (by exact continuousOn_const)
      continuous_sin
    simpa using hsub
  have hsin : ∫ t in (0 : ℝ)..(k * a), sin t = 1 - cos (k * a) := by
    rw [integral_sin]
    simp
  have hmul : (∫ θ in (0 : ℝ)..a, sin (k * θ)) * k = 1 - cos (k * a) := by
    rw [← intervalIntegral.integral_mul_const k (fun θ => sin (k * θ)), hsubst, hsin]
  calc ∫ θ in (0 : ℝ)..a, sin (k * θ)
      = ((∫ θ in (0 : ℝ)..a, sin (k * θ)) * k) / k := by field_simp [hk]
    _ = (1 - cos (k * a)) / k := by rw [hmul]

/-- `∫₀ᵅ (1 - θ/α)·cos (k·θ) dθ = (1 - cos (k·α)) / (α·k²)` for `0 < α`, `k ≠ 0`. -/
lemma integral_half_cos (k : ℝ) (hk : k ≠ 0) (α : ℝ) (hα0 : 0 < α) :
    ∫ θ in (0 : ℝ)..α, (1 - θ / α) * cos (k * θ) = (1 - cos (k * α)) / (α * k ^ 2) := by
  let u : ℝ → ℝ := fun θ => 1 - θ / α
  let v : ℝ → ℝ := fun θ => sin (k * θ) / k
  let u' : ℝ → ℝ := fun _ => -(1 / α)
  let v' : ℝ → ℝ := fun θ => cos (k * θ)
  have hu : ∀ x ∈ Set.uIcc (0 : ℝ) α, HasDerivAt u (u' x) x := by
    intro x hx
    have hd : HasDerivAt (fun θ : ℝ => 1 - θ / α) (0 - 1 / α) x :=
      (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).div_const α)
    exact hd.congr_deriv (by simp [u'])
  have hv : ∀ x ∈ Set.uIcc (0 : ℝ) α, HasDerivAt v (v' x) x := by
    intro x hx
    have hd : HasDerivAt (fun θ : ℝ => sin (k * θ) / k) ((cos (k * x) * k) / k) x :=
      ((hasDerivAt_sin (k * x)).comp x (hasDerivAt_const_mul k)).div_const k
    exact hd.congr_deriv (by simp [v'] <;> field_simp [hk])
  have hu' : IntervalIntegrable u' volume (0 : ℝ) α := by
    simpa [u'] using (continuous_const.intervalIntegrable (0 : ℝ) α)
  have hv' : IntervalIntegrable v' volume (0 : ℝ) α := by
    have hc : Continuous (fun θ : ℝ => cos (k * θ)) := by fun_prop
    simpa [v'] using hc.intervalIntegrable (0 : ℝ) α
  have hbp : ∫ x in (0 : ℝ)..α, u x * v' x = u α * v α - u 0 * v 0 - ∫ x in (0 : ℝ)..α, u' x * v x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := u) (v := v) (u' := u') (v' := v') hu hv hu' hv'
  have hInt : ∫ x in (0 : ℝ)..α, u' x * v x = -(1 / α) * (((1 - cos (k * α)) / k) * (1 / k)) := by
    calc ∫ x in (0 : ℝ)..α, u' x * v x
        = ∫ x in (0 : ℝ)..α, -(1 / α) * (sin (k * x) / k) := by simp [u', v]
      _ = -(1 / α) * ∫ x in (0 : ℝ)..α, sin (k * x) / k := by rw [intervalIntegral.integral_const_mul]
      _ = -(1 / α) * ((∫ x in (0 : ℝ)..α, sin (k * x)) * (1 / k)) := by
          rw [← intervalIntegral.integral_mul_const (1 / k) (fun x => sin (k * x))]
          congr 1
          apply intervalIntegral.integral_congr
          intro x hx
          simp [div_eq_mul_inv, one_div]
      _ = -(1 / α) * (((1 - cos (k * α)) / k) * (1 / k)) := by
          rw [integral_sin_const_mul k hk α]
  calc ∫ θ in (0 : ℝ)..α, (1 - θ / α) * cos (k * θ)
      = ∫ x in (0 : ℝ)..α, u x * v' x := by simp [u, v']
    _ = u α * v α - u 0 * v 0 - ∫ x in (0 : ℝ)..α, u' x * v x := hbp
    _ = 0 - (-(1 / α) * (((1 - cos (k * α)) / k) * (1 / k))) := by
        rw [hInt]
        simp [u, v, hα0.ne']
    _ = (1 - cos (k * α)) / (α * k ^ 2) := by
        field_simp [hk, hα0.ne'] <;> ring

/-- `∫₋ₐᵃ kern α θ · cos (k·θ) dθ = 2·(1 - cos (k·α)) / (α·k²)` for `0 < α`, `k ≠ 0`. -/
lemma kern_cos_integral (k : ℝ) (hk : k ≠ 0) (α : ℝ) (hα0 : 0 < α) :
    ∫ θ in (-α : ℝ)..α, kern α θ * cos (k * θ) = 2 * (1 - cos (k * α)) / (α * k ^ 2) := by
  have hEven : ∫ θ in (-α : ℝ)..0, (1 + θ / α) * cos (k * θ) =
      ∫ θ in (0 : ℝ)..α, (1 - θ / α) * cos (k * θ) := by
    have hcn := intervalIntegral.integral_comp_neg (a := -α) (b := 0)
      (f := fun x : ℝ => (1 - x / α) * cos (k * x))
    simpa [neg_div, cos_neg] using hcn
  have hleft : ∫ θ in (-α : ℝ)..0, kern α θ * cos (k * θ) =
      ∫ θ in (-α : ℝ)..0, (1 + θ / α) * cos (k * θ) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hIcc := Set.uIcc_of_le (by linarith : (-α : ℝ) ≤ 0)
    have hmem := Set.mem_Icc.mp (by simpa [hIcc] using hθ)
    have habs : |θ| = -θ := abs_of_nonpos hmem.2
    dsimp
    rw [kern_support α (by rw [habs]; linarith), habs]
    ring
  have hright : ∫ θ in (0 : ℝ)..α, kern α θ * cos (k * θ) =
      ∫ θ in (0 : ℝ)..α, (1 - θ / α) * cos (k * θ) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hIcc := Set.uIcc_of_le hα0.le
    have hmem := Set.mem_Icc.mp (by simpa [hIcc] using hθ)
    have habs : |θ| = θ := abs_of_nonneg hmem.1
    dsimp
    rw [kern_support α (by rw [habs]; linarith)]
    rw [habs]
  calc ∫ θ in (-α : ℝ)..α, kern α θ * cos (k * θ)
      = (∫ θ in (-α : ℝ)..0, kern α θ * cos (k * θ)) + (∫ θ in (0 : ℝ)..α, kern α θ * cos (k * θ)) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (kern_cos_integrable hα0 k (-α) 0) (kern_cos_integrable hα0 k 0 α)]
    _ = (∫ θ in (-α : ℝ)..0, (1 + θ / α) * cos (k * θ)) + (∫ θ in (0 : ℝ)..α, (1 - θ / α) * cos (k * θ)) := by
        rw [hleft, hright]
    _ = 2 * ∫ θ in (0 : ℝ)..α, (1 - θ / α) * cos (k * θ) := by
        rw [hEven]
        ring
    _ = 2 * ((1 - cos (k * α)) / (α * k ^ 2)) := by rw [integral_half_cos k hk α hα0]
    _ = 2 * (1 - cos (k * α)) / (α * k ^ 2) := by ring

/-- Nonnegativity of the `k`-th Fourier coefficient on `[-α, α]` for `0 < α`, `k ≠ 0`. -/
lemma kern_cos_integral_nonneg (k : ℝ) (hk : k ≠ 0) (α : ℝ) (hα0 : 0 < α) :
    0 ≤ ∫ θ in (-α : ℝ)..α, kern α θ * cos (k * θ) := by
  rw [kern_cos_integral k hk α hα0]
  have hnum : 0 ≤ 1 - cos (k * α) := sub_nonneg.mpr (cos_le_one (k * α))
  have hden : 0 < α * k ^ 2 := mul_pos hα0 (sq_pos_of_ne_zero hk)
  exact div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hnum) hden.le

/-- **Nonnegativity of nonzero Fourier coefficients of the kernel:**
`∫₋πᵖ kern α θ · cos (k·θ) dθ ≥ 0` for `0 < α ≤ π` and every `k : ℕ`. -/
lemma kernel_fourier_coeff_nonneg (α : ℝ) (hα0 : 0 < α) (hαπ : α ≤ π) (k : ℕ) :
    0 ≤ ∫ θ in (-π : ℝ)..π, kern α θ * cos ((k : ℝ) * θ) := by
  by_cases hk0 : k = 0
  · have hker : ∫ θ in (-π : ℝ)..π, kern α θ * cos ((k : ℝ) * θ) =
        ∫ θ in (-π : ℝ)..π, kern α θ := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      dsimp
      simp [hk0]
    rw [hker, kernel_int α hα0 hαπ]
    exact hα0.le
  · have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
    have h_full : ∫ θ in (-π : ℝ)..π, kern α θ * cos ((k : ℝ) * θ) =
        ∫ θ in (-α : ℝ)..α, kern α θ * cos ((k : ℝ) * θ) := by
      have h_left : ∫ θ in (-π : ℝ)..(-α), kern α θ * cos ((k : ℝ) * θ) = 0 := by
        have hEq : Set.EqOn (fun θ => kern α θ * cos ((k : ℝ) * θ)) (fun _ : ℝ => 0)
            (Set.uIcc (-π) (-α)) := by
          intro θ hθ
          have hIcc := Set.uIcc_of_le (by linarith : (-π : ℝ) ≤ -α)
          have hmem := Set.mem_Icc.mp (by simpa [hIcc] using hθ)
          dsimp
          rw [kern_eq_zero_of_ge_abs hα0 (by
            have hθ0 : θ ≤ 0 := by linarith
            rw [abs_of_nonpos hθ0]
            linarith)]
          simp
        rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_zero]
      have h_right : ∫ θ in (α : ℝ)..π, kern α θ * cos ((k : ℝ) * θ) = 0 := by
        have hEq : Set.EqOn (fun θ => kern α θ * cos ((k : ℝ) * θ)) (fun _ : ℝ => 0)
            (Set.uIcc α π) := by
          intro θ hθ
          have hIcc := Set.uIcc_of_le hαπ
          have hmem := Set.mem_Icc.mp (by simpa [hIcc] using hθ)
          dsimp
          rw [kern_eq_zero_of_ge_abs hα0 (by rw [abs_of_nonneg (hα0.le.trans hmem.1)]; exact hmem.1)]
          simp
        rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_zero]
      have h1 : ∫ θ in (-π : ℝ)..π, kern α θ * cos ((k : ℝ) * θ) =
          (∫ θ in (-π : ℝ)..(-α), kern α θ * cos ((k : ℝ) * θ)) + (∫ θ in (-α : ℝ)..π, kern α θ * cos ((k : ℝ) * θ)) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (kern_cos_integrable hα0 (k : ℝ) (-π) (-α)) (kern_cos_integrable hα0 (k : ℝ) (-α) π)]
      have h2 : ∫ θ in (-α : ℝ)..π, kern α θ * cos ((k : ℝ) * θ) =
          (∫ θ in (-α : ℝ)..α, kern α θ * cos ((k : ℝ) * θ)) + (∫ θ in (α : ℝ)..π, kern α θ * cos ((k : ℝ) * θ)) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (kern_cos_integrable hα0 (k : ℝ) (-α) α) (kern_cos_integrable hα0 (k : ℝ) α π)]
      rw [h1, h2, h_left, h_right]
      simp
    rw [h_full]
    exact kern_cos_integral_nonneg (k : ℝ) hkr α hα0

end JSP000625Kernel

end
