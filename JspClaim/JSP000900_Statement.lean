import Mathlib

/-!
# JSP-000900 — research-only exact statement interface

The source question (OpenAI, 2026-09-23 preprint, independently unreviewed)
asks for c_d > 0 such that every finite n-point set of R^d, d >= 3, n >= 2,
determines at least c_d * n^(2/d) *distinct Euclidean distances*.

**No proof of the principal proposition is provided or claimed here.**
The statements and the elementary helper checks are research scaffolding, not
a full formalization and not an award submission.

Sources:
* https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000900
* https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-higher-dimensional-Erdos-distinct-distances-conjecture-September-23-2026/build/sections/introduction.tex
-/

namespace JSP000900

open scoped EuclideanGeometry

/-- The set of *distinct positive* Euclidean distances determined by two
different points in a finite subset of d-dimensional Euclidean space.
A Finset image automatically removes duplicated lengths. -/
noncomputable def distanceValues {d : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin d))) : Finset ℝ := by
  classical
  exact ((P.product P).filter (fun pq => pq.1 ≠ pq.2)).image
    (fun pq => dist pq.1 pq.2)

/-- Exact proposition of the 2026-09-23 published mathematical claim:
the constant depends on the dimension d, but neither on cardinality nor
on the particular set P. This is a definition, NOT a proved theorem. -/
def OriginalQuestion : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    ∃ c : ℝ, 0 < c ∧
      ∀ P : Finset (EuclideanSpace ℝ (Fin d)),
        2 ≤ P.card →
          c * ((P.card : ℝ) ^ ((2 : ℝ) / (d : ℝ))) ≤
            ((distanceValues P).card : ℝ)

/-- The empty set determines no distances. Does not prove OriginalQuestion. -/
theorem distanceValues_empty (d : ℕ) :
    distanceValues (∅ : Finset (EuclideanSpace ℝ (Fin d))) = ∅ := by
  classical
  simp [distanceValues]

/-- Every distance in the image is nonnegative, a definition sanity check. -/
theorem distanceValues_nonneg {d : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin d)))
    (r : ℝ) (hr : r ∈ distanceValues P) : 0 ≤ r := by
  classical
  obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hr
  exact dist_nonneg

end JSP000900

#print axioms JSP000900.distanceValues_empty
#print axioms JSP000900.distanceValues_nonneg
