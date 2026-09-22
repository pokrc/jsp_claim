import Mathlib.Tactic

namespace JSP000876

/-!
# JSP-000876 — WITHDRAWN. This file does **not** solve the problem.

**Status (2026-09-22): claim withdrawn.** The submission of this file as a
formalization for `JSP-000876` (PR #2801 to `TheJustinSunPrize/awards`, with
claim issue #2802) has been withdrawn, and this file must not be read as a
solution to JSP-000876.

JSP-000876 is Erdős problem #1056 (Guy's collection A15, Erdős 1979). The
problem asks: for every `k ≥ 2`, does there exist a prime `p` and intervals
`I₁, …, I_k` given by strictly increasing boundaries `b₀ < b₁ < … < b_k`
(i.e. `Iᵢ = [bᵢ, bᵢ₊₁)`, so the intervals are **contiguous** and tile a single
block) such that `∏_{n ∈ Iᵢ} n ≡ 1 (mod p)` for all `i`? The formal statement
used by the problem bank's source is `Erdos1056.erdos_1056` in
`google-deepmind/formal-conjectures`:

```lean
answer(sorry) ↔ ∀ k ≥ 2, ∃ (p : ℕ) (_ : p.Prime) (boundaries : Fin (k + 1) → ℕ)
    (_ : StrictMono boundaries), AllModProdEqualsOne p boundaries
```

The theorems below concern **non-adjacent** intervals with gaps, which is not
the problem, and the `p = 5` construction fails for `k ≥ 3` once the intervals
must be contiguous: a block tiling `k ≥ 3` intervals must contain a multiple of
`5` in some interval, forcing that interval's product to be `0` rather than `1`
modulo `5`. What remains here is a true but irrelevant arithmetic observation,
kept only so that the repository history stays coherent with the withdrawn
submission. Do not cite it as a result about JSP-000876.
-/

/-- Product of all integers in `[a, b]`. -/
def intervalProd (a b : ℕ) : ℤ := ∏ x ∈ Finset.Icc a b, (x : ℤ)

/-- The product of `[1,3]` is `6 ≡ 1 (mod 5)`. -/
theorem prod_1_3 : intervalProd 1 3 % (5 : ℤ) = 1 := by
  decide

/-- The product of `[6,8]` is `336 ≡ 1 (mod 5)`. -/
theorem prod_6_8 : intervalProd 6 8 % (5 : ℤ) = 1 := by
  decide

/-- The product of `[11,13]` is `1716 ≡ 1 (mod 5)`. -/
theorem prod_11_13 : intervalProd 11 13 % (5 : ℤ) = 1 := by
  decide

/-- For every `k`, the product over `[5k+1, 5k+3]` is `≡ 1 (mod 5)`, since
modulo `5` it is `1·2·3 = 6 ≡ 1`. -/
theorem product_mod5 (k : ℕ) :
    intervalProd (5*k + 1) (5*k + 3) % (5 : ℤ) = 1 := by
  unfold intervalProd
  have hIcc : Finset.Icc (5*k + 1) (5*k + 3) = {5*k + 1, 5*k + 2, 5*k + 3} := by
    ext x; simp [Finset.mem_Icc]; omega
  rw [hIcc]
  simp [Int.add_emod, Int.mul_emod]

/-- Consecutive construction intervals do not overlap. -/
theorem intervals_disjoint (k : ℕ) : 5*k + 3 < 5*(k+1) + 1 := by
  omega

/-- True but **not** a solution to JSP-000876: three pairwise-disjoint (with
gaps) intervals each have product `≡ 1 (mod 5)`. The real problem requires
contiguous intervals defined by strictly increasing boundaries. -/
theorem three_disjoint_intervals_product_one_mod5 :
    ∃ (a1 b1 a2 b2 a3 b3 : ℕ),
      b1 < a2 ∧ b2 < a3 ∧
      intervalProd a1 b1 % (5 : ℤ) = 1 ∧
      intervalProd a2 b2 % (5 : ℤ) = 1 ∧
      intervalProd a3 b3 % (5 : ℤ) = 1 := by
  refine ⟨1, 3, 6, 8, 11, 13, ?d12, ?d23, ?p1, ?p2, ?p3⟩
  · norm_num
  · norm_num
  · exact prod_1_3
  · exact prod_6_8
  · exact prod_11_13

end JSP000876
