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

/-! ### The actual extremal quantity (no preloaded answer formula) -/

/-- Direct supremum definition of Erdős 504's α_N, literally over the
angles guaranteed in every N-point planar configuration. -/
noncomputable def alpha (N : ℕ) : ℝ :=
  sSup {θ : ℝ | GuaranteedAngle N θ}

/-- The collection of guaranteed angle thresholds is bounded above by π.
We select one configuration of N distinct planar points; no geometric
configuration or result is assumed as an axiom. -/
theorem guaranteed_bddAbove (N : ℕ) :
    BddAbove {θ : ℝ | GuaranteedAngle N θ} := by
  classical
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq Plane N
  refine ⟨Real.pi, ?_⟩
  intro θ hθ
  obtain ⟨x, _, y, _, z, _, _, _, _, ha⟩ := hθ s hs
  exact ha.trans (EuclideanGeometry.angle_le_pi x y z)

/-- When at least three vertices are present, there exists a
guaranteed threshold: π/3. -/
theorem guaranteed_nonempty (N : ℕ) (hN : 3 ≤ N) :
    ({θ : ℝ | GuaranteedAngle N θ} : Set ℝ).Nonempty :=
  ⟨Real.pi / 3, elementary_lower_bound N hN⟩

/-- Monotonicity of the actual supremum α_N from its defining predicate,
not from the published answer formula. -/
theorem alpha_mono {n m : ℕ} (hn : 3 ≤ n) (hnm : n ≤ m) :
    alpha n ≤ alpha m := by
  unfold alpha
  exact csSup_le_csSup (guaranteed_bddAbove m) (guaranteed_nonempty n hn)
    (fun θ hθ => guaranteed_mono hnm hθ)

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

/-- In fact the printed numerator-one lower value exceeds the upper
value at *every* dyadic band boundary with parameter n ≥ 2.
This algebraic fact is independent of the geometric model. -/
theorem printed_values_descend_every_band (n : ℕ) (hn : 2 ≤ n) :
    Real.pi * (1 - (1 : ℝ) / (n : ℝ)) <
    Real.pi * (1 - (1 : ℝ) / (2 * (n : ℝ) - 1)) := by
  have hn' : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hnlt : (n : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have hdiv : (1 : ℝ) / (2 * (n : ℝ) - 1) < 1 / (n : ℝ) :=
    one_div_lt_one_div_of_lt (by linarith : (0 : ℝ) < n) hnlt
  nlinarith [mul_lt_mul_of_pos_left hdiv Real.pi_pos]

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

/-- The two printed α-values are literally impossible for the
original supremum-defined geometry, with no hypothetical envelope
assumptions and no additional axioms. -/
theorem posted_alpha_values_impossible :
    ¬ (alpha 5 = Real.pi * (1 - (1 : ℝ) / 5) ∧
       alpha 6 = Real.pi * (1 - (1 : ℝ) / 3)) := by
  rintro ⟨h5, h6⟩
  have hm : alpha 5 ≤ alpha 6 :=
    alpha_mono (by decide : 3 ≤ 5) (by decide : 5 ≤ 6)
  rw [h5, h6] at hm
  have hstrict := printed_values_descend
  exact (not_le_of_gt hstrict) hm

/-- The corrected 1995 lower-band value at five points is 3π/5,
and it does not violate the six-point upper value 2π/3.
This verifies only the numerical consistency of the correction. -/
theorem corrected_values_increase :
    Real.pi * (1 - (2 : ℝ) / 5) <
    Real.pi * (1 - (1 : ℝ) / 3) := by
  have hpi := Real.pi_pos
  nlinarith

#print axioms JSP000404.guaranteed_mono
#print axioms JSP000404.alpha_mono
#print axioms JSP000404.posted_alpha_values_impossible
#print axioms JSP000404.elementary_lower_bound
#print axioms JSP000404.printed_values_descend_every_band
#print axioms JSP000404.website_bands_cannot_both_hold
#print axioms JSP000404.corrected_values_increase

end JSP000404
