import Mathlib.Tactic

namespace JSP000876

/-!
# JSP-000876 — Can several consecutive integer intervals each have product congruent to one modulo the same prime?

**Problem** (`problems/catalog-0801-0900.md#JSP-000876`):
> Can several consecutive integer intervals each have product congruent to one modulo the same prime?

**Answer: YES.** There are *several* (three, and in fact any prescribed number
of) pairwise-disjoint consecutive-integer intervals each of whose products is
congruent to 1 modulo the same prime 5.

**Explicit witness (three intervals):** [1,3], [6,8], [11,13].

   1·2·3     =   6   ≡ 1 (mod 5)
   6·7·8     = 336   ≡ 1 (mod 5)
   11·12·13  = 1716  ≡ 1 (mod 5)

The intervals are pairwise disjoint.  In fact for every k the interval
[5k+1, 5k+3] has product (5k+1)(5k+2)(5k+3) ≡ 6 ≡ 1 (mod 5), and consecutive
such intervals [5k+1,5k+3], [5(k+1)+1,5(k+1)+3] are disjoint because
5k+3 < 5(k+1)+1.  So any prescribed number m ≥ 1 of such intervals exists.
-/

/-- Product of all integers in [a, b]. -/
def intervalProd (a b : ℕ) : ℤ := ∏ x ∈ Finset.Icc a b, (x : ℤ)

/-- The product of [1,3] is 6 ≡ 1 (mod 5). -/
theorem prod_1_3 : intervalProd 1 3 % (5 : ℤ) = 1 := by
  decide

/-- The product of [6,8] is 336 ≡ 1 (mod 5). -/
theorem prod_6_8 : intervalProd 6 8 % (5 : ℤ) = 1 := by
  decide

/-- The product of [11,13] is 1716 ≡ 1 (mod 5). -/
theorem prod_11_13 : intervalProd 11 13 % (5 : ℤ) = 1 := by
  decide

/-- For every k, the product over [5k+1, 5k+3] is ≡ 1 (mod 5).
    Proof: modulo 5, (5k+1)(5k+2)(5k+3) ≡ 1·2·3 = 6 ≡ 1. -/
theorem product_mod5 (k : ℕ) :
    intervalProd (5*k + 1) (5*k + 3) % (5 : ℤ) = 1 := by
  unfold intervalProd
  -- rewrite the interval product as the product of three consecutive integers
  have hIcc : Finset.Icc (5*k + 1) (5*k + 3) = {5*k + 1, 5*k + 2, 5*k + 3} := by
    ext x; simp [Finset.mem_Icc]; omega
  rw [hIcc]
  simp [Int.add_emod, Int.mul_emod]

/-- Consecutive construction intervals do not overlap. -/
theorem intervals_disjoint (k : ℕ) : 5*k + 3 < 5*(k+1) + 1 := by
  omega

/-- Main theorem: several (at least three) pairwise-disjoint consecutive-integer
    intervals each have product congruent to 1 modulo the same prime.
    Witness: [1,3], [6,8], [11,13] modulo 5. -/
theorem jsp000876 :
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
