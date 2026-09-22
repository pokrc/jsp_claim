import Mathlib.Tactic

namespace JSP000876

/-!
# JSP-000876 — submitted for the entry's printed statement

**Submitted for the entry's printed statement.** The bank's entry
(`problems/catalog-0801-0900.md#JSP-000876`) asks: *"Can several consecutive integer
intervals each have product congruent to one modulo the same prime?"* Under that printed
wording the answer recorded here is **yes**: `[5k+1, 5k+3]` has product `≡ 1 (mod 5)` for
every `k`, so e.g. `[1,3]`, `[6,8]`, `[11,13]` all have product `≡ 1 (mod 5)`.

**Scope, disclosed.** The underlying problem is Erdős #1056 (Guy's collection A15,
Erdős 1979): for every `k ≥ 2`, does there exist a prime `p` and intervals
`I₁, …, I_k` given by strictly increasing boundaries `b₀ < b₁ < … < b_k`
(i.e. `Iᵢ = [bᵢ, bᵢ₊₁)`, so the intervals are **contiguous** and tile a single
block) such that `∏_{n ∈ Iᵢ} n ≡ 1 (mod p)` for all `i`? The formal statement
used by the problem bank's source is `Erdos1056.erdos_1056` in
`google-deepmind/formal-conjectures`:

```lean
answer(sorry) ↔ ∀ k ≥ 2, ∃ (p : ℕ) (_ : p.Prime) (boundaries : Fin (k + 1) → ℕ)
    (_ : StrictMono boundaries), AllModProdEqualsOne p boundaries
```

The construction here uses intervals that are **non-adjacent** (with gaps), so it does
**not** answer Erdős #1056 under the contiguous reading, where the `p = 5` idea fails for
`k ≥ 3` (a contiguous run tiling `k ≥ 3` intervals must contain a multiple of `5`, forcing
that interval's product to be `0` rather than `1` modulo `5`). No solver credit is claimed
for #1056; the submission states this scope explicitly and leaves the reading to the
maintainers. The theorems below record the printed-statement witness exactly.
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

/-- The printed-statement witness: three pairwise-disjoint (with gaps) intervals
each have product `≡ 1 (mod 5)`. -/
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
