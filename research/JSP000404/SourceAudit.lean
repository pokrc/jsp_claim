import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# JSP-000404 / Erdős 504: independently checked foundations and source audit

This file is **NOT** a complete proof of Blumenthal's problem.

It uses genuine Euclidean angles and point sets, not a function defined
by the answer formula. It establishes:
1. guaranteed angle thresholds are monotone in the number of points;
2. every configuration of at least three points has an angle ≥ π/3;
3. the *printed* (numerator-one) lower formula and the six-point upper
   formula from erdosproblems.com/504 cannot both describe the extremal
   values (α_5 would be 4π/5 > α_6 = 2π/3);
4. the numerator-two formula reported from Sendov 1995 is compatible
   with monotonicity at that boundary.

The general Sendov classification is **not** proved here. This is a
source-correction certificate, not a prize claim.

Prior art: Jackie1021/jsp000404-lean already reports the numerator-two
correction and substantial partial Lean formalizations. No novelty
or proof priority is claimed for the correction.
-/

namespace JSP000404

open EuclideanGeometry
open scoped Real

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The literal geometric guarantee in Erdős 504:
every set of N distinct Euclidean planar points contains three pairwise
distinct vertices with a genuine (unoriented) angle ≥ θ. -/
def GuaranteedAngle (N : ℕ) (θ : ℝ) : Prop :=
  ∀ s : Finset Plane, s.card = N →
    ∃ x ∈ s, ∃ y ∈ s, ∃ z ∈ s,
      x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ θ ≤ EuclideanGeometry.angle x y z

/-- The guarantee persists when extra points are added.
No assumptions about the angle formula are used. -/
theorem guaranteed_mono {n m : ℕ} {θ : ℝ}
    (hnm : n ≤ m) (h : GuaranteedAngle n θ) : GuaranteedAngle m θ := by
  classical
  intro s hs
  obtain ⟨t, hts, htcard⟩ :=
    Finset.exists_subset_card_eq (s := s) (n := n) (by omega : n ≤ s.card)
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, hθ⟩ := h t htcard
  exact ⟨x, hts hx, y, hts hy, z, hts hz, hxy, hyz, hxz, hθ⟩

/-- Every N ≥ 3 planar point configuration contains an angle ≥ 60°.
This uses the actual geometry via the triangle-angle sum in Mathlib.
It is only a weak universal lower bound, not Sendov's classification. -/
theorem elementary_lower_bound (N : ℕ) (hN : 3 ≤ N) :
    GuaranteedAngle N (Real.pi / 3) := by
  classical
  intro s hs
  have hcard : 2 < s.card := by omega
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card_iff.mp hcard
  have hsum : EuclideanGeometry.angle x y z +
      EuclideanGeometry.angle y z x +
      EuclideanGeometry.angle z x y = Real.pi :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := x) (p₂ := y) z hxy.symm
  by_cases h₁ : Real.pi / 3 ≤ EuclideanGeometry.angle x y z
  · exact ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, h₁⟩
  by_cases h₂ : Real.pi / 3 ≤ EuclideanGeometry.angle y z x
  · exact ⟨y, hy, z, hz, x, hx, hyz, hxz.symm, hxy.symm, h₂⟩
  have h₃ : Real.pi / 3 ≤ EuclideanGeometry.angle z x y := by
    push_neg at h₁ h₂
    linarith
  exact ⟨z, hz, x, hx, y, hy, hxz.symm, hxy, hyz.symm, h₃⟩

/-- N=5 is in the website's lower band when n=3. -/
theorem five_in_reported_lower_band :
    2 ^ (3 - 1 : ℕ) < 5 ∧
    5 ≤ 2 ^ (3 - 1 : ℕ) + 2 ^ (3 - 3 : ℕ) := by
  norm_num

/-- N=6 is in the website's upper band when n=3. -/
theorem six_in_reported_upper_band :
    2 ^ (3 - 1 : ℕ) + 2 ^ (3 - 3 : ℕ) < 6 ∧
    6 ≤ 2 ^ (3 : ℕ) := by
  norm_num

/-- The source's numerator-one lower value (4π/5) is larger than the
source's six-point upper value (2π/3). This is a direct arithmetic
contradiction with the mathematically necessary monotonicity of α_N. -/
theorem printed_values_descend :
    Real.pi * (1 - (1 : ℝ) / 3) <
    Real.pi * (1 - (1 : ℝ) / 5) := by
  have hpi := Real.pi_pos
  nlinarith

/-- The actual geometric statement ruling out *both* printed branches.
The second hypothesis says the optimum for six points is at most 2π/3.
If the five-point lower branch really guaranteed 4π/5, then its
guarantee would also hold for every six-point set, contradiction.

Both hypotheses are deliberately explicit; neither is supplied by an
axiom or hidden in a definition. -/
theorem website_bands_cannot_both_hold
    (h5 : GuaranteedAngle 5 (Real.pi * (1 - (1 : ℝ) / 5)))
    (h6 : ∀ θ : ℝ, GuaranteedAngle 6 θ →
      θ ≤ Real.pi * (1 - (1 : ℝ) / 3)) : False := by
  have h56 : GuaranteedAngle 6 (Real.pi * (1 - (1 : ℝ) / 5)) :=
    guaranteed_mono (by decide : 5 ≤ 6) h5
  have hbound := h6 _ h56
  have hstrict := printed_values_descend
  linarith

/-- The corrected 1995 lower-band value at five points is 3π/5,
and it does not violate the six-point upper value 2π/3.
This verifies only the numerical consistency of the correction. -/
theorem corrected_values_increase :
    Real.pi * (1 - (2 : ℝ) / 5) <
    Real.pi * (1 - (1 : ℝ) / 3) := by
  have hpi := Real.pi_pos
  nlinarith

#print axioms JSP000404.guaranteed_mono
#print axioms JSP000404.elementary_lower_bound
#print axioms JSP000404.website_bands_cannot_both_hold
#print axioms JSP000404.corrected_values_increase

end JSP000404
