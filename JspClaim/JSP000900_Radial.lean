import JspClaim.JSP000900_Statement

/-!
# JSP-000900 — radial distance-counting lemmas (proved)

These facts are genuine, kernel-checked sublemmas of the finite
Euclidean distance-counting interface. They are NOT the main lower bound
of the distinct-distances conjecture.
-/

set_option maxHeartbeats 2000000

namespace JSP000900

/-- Every distance to an anchor point in the finite set is among the
global distances determined by all pairs of distinct points. -/
theorem radialDistances_subset {d : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin d)))
    (p : EuclideanSpace ℝ (Fin d)) (hp : p ∈ P) :
    (P.erase p).image (fun q => dist p q) ⊆ distanceValues P := by
  classical
  intro r hr
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨hqp, hqP⟩ := Finset.mem_erase.mp hq
  change dist p q ∈
    ((P.product P).filter (fun pq => pq.1 ≠ pq.2)).image
      (fun pq => dist pq.1 pq.2)
  apply Finset.mem_image.mpr
  refine ⟨(p, q), ?_, rfl⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hp, hqP⟩, Ne.symm hqp⟩

/-- If all non-anchor vertices have different radial distances from
an anchor, the point set determines at least cardinality minus one
different distances. Exact cardinality, no asymptotics. -/
theorem card_sub_one_le_distanceValues_of_radial_inj {d : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin d)))
    (p : EuclideanSpace ℝ (Fin d)) (hp : p ∈ P)
    (hinj : Set.InjOn (fun q => dist p q) (↑(P.erase p) : Set _)) :
    P.card - 1 ≤ (distanceValues P).card := by
  classical
  calc
    P.card - 1 = (P.erase p).card := (Finset.card_erase_of_mem hp).symm
    _ = ((P.erase p).image (fun q => dist p q)).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (distanceValues P).card :=
      Finset.card_le_card (radialDistances_subset P p hp)

/-- A nontrivial pair of different points in P gives a strictly positive
distance contained in the global distance spectrum. -/
theorem pair_distance_mem {d : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin d)))
    (p q : EuclideanSpace ℝ (Fin d))
    (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    dist p q ∈ distanceValues P := by
  classical
  change dist p q ∈
    ((P.product P).filter (fun pq => pq.1 ≠ pq.2)).image
      (fun pq => dist pq.1 pq.2)
  exact Finset.mem_image.mpr
    ⟨(p, q), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hpq⟩, rfl⟩

/-- Any two distinct points already force at least one positive
distinct distance. This is not the n^(2/d) lower bound. -/
theorem one_le_distanceValues_card_of_two_points {d : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin d)))
    (p q : EuclideanSpace ℝ (Fin d))
    (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    1 ≤ (distanceValues P).card := by
  apply Finset.card_pos.mpr
  exact ⟨dist p q, pair_distance_mem P p q hp hq hpq⟩

end JSP000900

#print axioms JSP000900.card_sub_one_le_distanceValues_of_radial_inj
#print axioms JSP000900.one_le_distanceValues_card_of_two_points
