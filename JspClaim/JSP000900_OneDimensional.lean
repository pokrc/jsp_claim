import JspClaim.JSP000900_Radial

/-!
# A fully proven 1-dimensional distinct-distances model

In a finite set of n distinct real points, the leftmost point sees n-1
different positive distances. The proof uses the exact same pair-image
model as JSP000900's high-dimensional question.

**Scope limitation:** 1-dimensional only. This does NOT prove or imply the
claimed sharp lower bound for arbitrary dimensions d ≥ 3.
-/

namespace JSP000900

/-- Full spectrum of pairwise distances of distinct points on the real line. -/
noncomputable def realDistanceValues (P : Finset ℝ) : Finset ℝ := by
  classical
  exact ((P.product P).filter (fun pq => pq.1 ≠ pq.2)).image
    (fun pq => dist pq.1 pq.2)

/-- Every radial distance from a member of a finite real point set is a
global distance, exactly as in the high-dimensional statement. -/
theorem realRadialDistances_subset
    (P : Finset ℝ) (p : ℝ) (hp : p ∈ P) :
    (P.erase p).image (fun q => dist p q) ⊆ realDistanceValues P := by
  classical
  intro r hr
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨hqp, hqP⟩ := Finset.mem_erase.mp hq
  change dist p q ∈
    ((P.product P).filter (fun pq => pq.1 ≠ pq.2)).image
      (fun pq => dist pq.1 pq.2)
  exact Finset.mem_image.mpr
    ⟨(p, q), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hp, hqP⟩, Ne.symm hqp⟩, rfl⟩

/-- **Complete theorem in one dimension.**
Every nonempty finite n-point subset of the real line determines at least
n - 1 distinct positive pairwise distances. -/
theorem real_distinct_distances_lower_bound
    (P : Finset ℝ) (hP : P.Nonempty) :
    P.card - 1 ≤ (realDistanceValues P).card := by
  classical
  let p : ℝ := P.min' hP
  have hp : p ∈ P := Finset.min'_mem P hP
  have hp_le (q : ℝ) (hq : q ∈ P) : p ≤ q := by
    exact Finset.min'_le q hq
  have hinj : Set.InjOn (fun q : ℝ => dist p q) (↑(P.erase p) : Set ℝ) := by
    intro x hx y hy hxy
    have hxP : x ∈ P := (Finset.mem_erase.mp hx).2
    have hyP : y ∈ P := (Finset.mem_erase.mp hy).2
    have hpx := hp_le x hxP
    have hpy := hp_le y hyP
    rw [Real.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hpx),
      abs_of_nonpos (sub_nonpos.mpr hpy)] at hxy
    linarith
  calc
    P.card - 1 = (P.erase p).card := (Finset.card_erase_of_mem hp).symm
    _ = ((P.erase p).image (fun q => dist p q)).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (realDistanceValues P).card :=
      Finset.card_le_card (realRadialDistances_subset P p hp)

end JSP000900

#print axioms JSP000900.real_distinct_distances_lower_bound
