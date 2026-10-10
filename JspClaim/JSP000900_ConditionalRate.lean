import JspClaim.JSP000900_Radial

/-!
# Dimension-uniform power bound under a radial injectivity hypothesis

Proves a genuine subcase of the target exponent for sets with an anchor
seeing different distances to all other vertices. The hypothesis is
nontrivial and DOES NOT hold for arbitrary high-dimensional point sets.

This conditional theorem is not the solution to JSP-000900.
-/

namespace JSP000900

/-- If some anchor sees all other points at different distances,
the desired power exponent holds with explicit constant 1/2,
uniformly for every dimension d ≥ 3 and size n ≥ 2. -/
theorem high_dimensional_bound_of_radial_inj
    {d : ℕ} (hd : 3 ≤ d)
    (P : Finset (EuclideanSpace ℝ (Fin d)))
    (hn : 2 ≤ P.card)
    (p : EuclideanSpace ℝ (Fin d)) (hp : p ∈ P)
    (hinj : Set.InjOn (fun q => dist p q) (↑(P.erase p) : Set _)) :
    (1 / 2 : ℝ) * ((P.card : ℝ) ^ ((2 : ℝ) / (d : ℝ))) ≤
      ((distanceValues P).card : ℝ) := by
  have hnR : (2 : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hn
  have hdR : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hden : (0 : ℝ) < d := by linarith
  have he : ((2 : ℝ) / (d : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ hden).2
    linarith
  have hpow : ((P.card : ℝ) ^ ((2 : ℝ) / (d : ℝ))) ≤ (P.card : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ P.card by linarith) he
    simpa using h
  have hpred_nat : P.card - 1 + 1 = P.card := by omega
  have hpred : ((P.card - 1 : ℕ) : ℝ) + 1 = (P.card : ℝ) := by
    exact_mod_cast hpred_nat
  have hhalf : (P.card : ℝ) / 2 ≤ ((P.card - 1 : ℕ) : ℝ) := by
    linarith
  have hrad : ((P.card - 1 : ℕ) : ℝ) ≤
      ((distanceValues P).card : ℝ) := by
    exact_mod_cast card_sub_one_le_distanceValues_of_radial_inj P p hp hinj
  calc
    (1 / 2 : ℝ) * ((P.card : ℝ) ^ ((2 : ℝ) / (d : ℝ)))
        ≤ (P.card : ℝ) / 2 := by linarith
    _ ≤ ((P.card - 1 : ℕ) : ℝ) := hhalf
    _ ≤ ((distanceValues P).card : ℝ) := hrad

end JSP000900

#print axioms JSP000900.high_dimensional_bound_of_radial_inj
