import JspClaim.JSP000900_Radial

/-!
# Quantitative capacity of distance profiles (proved, unconditional combinatorics)

Let P be a finite set in Euclidean space, and let k selected anchor points
belong to P. If the vector of distances to these anchors uniquely determines
a point of P, then |P| ≤ (|Δ(P)| + 1)^k.

The +1 is reserved for zero self-distances; zero is not counted by Δ(P).

This is a genuine, broadly applicable information-theoretic reduction.
It does NOT prove that such a family of ≤ d+1 anchors always exists, nor the
sharp conjectured n^(2/d) bound for arbitrary P.
-/

namespace JSP000900

/-- Nonzero distances in the spectrum cannot vanish. -/
theorem zero_not_mem_distanceValues {d : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin d))) :
    (0 : ℝ) ∉ distanceValues P := by
  classical
  intro h
  rcases Finset.mem_image.mp h with ⟨⟨p, q⟩, hpq, hzero⟩
  have hneq : p ≠ q := (Finset.mem_filter.mp hpq).2
  exact hneq (dist_eq_zero.mp hzero)

/-- The profile of an element relative to k anchors takes values in the
finite global distance spectrum augmented with the diagonal distance 0. -/
theorem radial_profile_mem_range {d k : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin d)))
    (anchors : Fin k → EuclideanSpace ℝ (Fin d))
    (ha : ∀ i, anchors i ∈ P)
    (p : EuclideanSpace ℝ (Fin d)) (hp : p ∈ P) :
    (fun i : Fin k => dist p (anchors i)) ∈
      Fintype.piFinset (fun _ : Fin k => insert 0 (distanceValues P)) := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro i
  by_cases e : p = anchors i
  · subst p
    simp
  · exact Finset.mem_insert_of_mem (pair_distance_mem P p (anchors i) hp (ha i) e)

/-- If k anchors in P separate all points by their distance profiles,
the number of points is bounded by (number of nonzero distances + 1)^k. -/
theorem card_le_distance_spectrum_pow_of_injective_profile {d k : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin d)))
    (anchors : Fin k → EuclideanSpace ℝ (Fin d))
    (ha : ∀ i, anchors i ∈ P)
    (hinj : Set.InjOn
      (fun p : EuclideanSpace ℝ (Fin d) =>
        fun i : Fin k => dist p (anchors i))
      (↑P : Set (EuclideanSpace ℝ (Fin d)))) :
    P.card ≤ ((distanceValues P).card + 1) ^ k := by
  classical
  let S : Finset ℝ := insert 0 (distanceValues P)
  let allProfiles : Finset (Fin k → ℝ) :=
    Fintype.piFinset (fun _ : Fin k => S)
  have hsub : P.image (fun p => fun i : Fin k => dist p (anchors i)) ⊆
      allProfiles := by
    intro f hf
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hf
    exact radial_profile_mem_range P anchors ha p hp
  have hcard : P.card ≤ allProfiles.card := by
    calc
      P.card = (P.image
          (fun p => fun i : Fin k => dist p (anchors i))).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ allProfiles.card := Finset.card_le_card hsub
  have hprofiles : allProfiles.card = S.card ^ k := by
    exact Fintype.card_piFinset_const S k
  have hS : S.card = (distanceValues P).card + 1 := by
    simp [S, zero_not_mem_distanceValues P]
  rw [hprofiles, hS] at hcard
  exact hcard

end JSP000900

#print axioms JSP000900.zero_not_mem_distanceValues
#print axioms JSP000900.card_le_distance_spectrum_pow_of_injective_profile
