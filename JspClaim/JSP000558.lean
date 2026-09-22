import Mathlib.Tactic

namespace JSP000558

/-!
# JSP-000558 — Can every integer at least two be a ratio of products of two disjoint
equal-length positive-integer intervals, each of length at least two?

**Problem** (`problems/catalog-0501-0600.md#JSP-000558`):
> Can every integer at least two be a ratio of products of two disjoint equal-length
> positive-integer intervals, each of length at least two?

**Contribution (k=2 case, Pell reduction):**

For interval length k = 2, the question asks: given n ≥ 2, does there exist
a > b ≥ 1 with b+1 < a (disjoint) and a(a+1) = n·b(b+1)?

This is equivalent to the Pell-type equation
  X² − n·Y² = 1 − n,   where X = 2a+1, Y = 2b+1 are odd integers ≥ 3.

**Main theorem (n = 4 is a counterexample at k = 2).**  For n = 4 the Pell
equation becomes X² − 4Y² = −3, i.e. (X−2Y)(X+2Y) = −3.  Since X, Y ≥ 3
we have X + 2Y ≥ 9 and, because the product is negative with X + 2Y > 0, we
get X − 2Y < 0 so −(X−2Y) ≥ 1.  Then
  |(X−2Y)(X+2Y)| = (−(X−2Y))·(X+2Y) ≥ 1·9 = 9 > 3,
contradicting |−3| = 3.  Hence **4 cannot be represented as a ratio of
products of two disjoint intervals of length 2.**

This is the smallest provable obstruction.  Whether a larger interval length
k ≥ 3 can achieve the ratio 4 is a deep open question (JSP-000558, open since
~1979).

**Positive constructions at k = 2.**  For several n ≥ 2 the ratio *is* achievable:
  n = 2 : [20,21] / [14,15] = 420/210 = 2,      disjoint (15 < 20)
  n = 3 : [9,10]  / [5,6]   = 90/30   = 3,      disjoint (6 < 9)
  n = 5 : [5,6]   / [2,3]   = 30/6    = 5,      disjoint (3 < 5)
  n = 6 : [3,4]   / [1,2]   = 12/2    = 6,      disjoint (2 < 3)

These witnesses are machine-verified below (using `norm_num`, not `native_decide`).
-/

-- ===== SECTION 1: Pell reduction =====

/-- For k=2, the equation a(a+1) = n·b(b+1) with a,b ≥ 1 is equivalent to
    X² - n·Y² = 1 - n where X = 2a+1, Y = 2b+1. -/
theorem pell_reduction {a b n : ℕ} :
    ((a : ℤ) * (a + 1) = (n : ℤ) * (b * (b + 1)) ↔
     ((2 * (a : ℤ) + 1) ^ 2 - (n : ℤ) * (2 * (b : ℤ) + 1) ^ 2 = 1 - (n : ℤ))) := by
  constructor <;> intro h <;> nlinarith

-- ===== SECTION 2: n = 4, k = 2 impossibility =====

/-- Pell equation X² − 4Y² = −3 has no solution with X, Y ≥ 3.
    Proof: factor X²−4Y² = (X−2Y)(X+2Y) = −3.  Since X+2Y ≥ X ≥ 3, and
    more precisely X,Y ≥ 3 give X+2Y ≥ 9, the magnitude bound
    (−(X−2Y))·(X+2Y) ≥ 1·9 = 9 > 3 contradicts |product| = 3. -/
theorem pell_no_4 (X Y : ℤ) (hX : X ≥ 3) (hY : Y ≥ 3) :
    X ^ 2 - 4 * Y ^ 2 ≠ -3 := by
  intro h
  have hfac : (X - 2 * Y) * (X + 2 * Y) = -3 := by nlinarith
  have he_ge9 : X + 2 * Y ≥ 9 := by omega
  have he_pos : X + 2 * Y > 0 := by omega
  have hneg : X - 2 * Y < 0 := by
    by_contra hn
    have hnneg : X - 2 * Y ≥ 0 := by omega
    have : (X - 2 * Y) * (X + 2 * Y) ≥ 0 := by
      exact mul_nonneg hnneg (by omega : 0 ≤ X + 2 * Y)
    linarith
  have hd_ge1 : -(X - 2 * Y) ≥ 1 := by omega
  have hprod_ge : -(X - 2 * Y) * (X + 2 * Y) ≥ 9 := by
    nlinarith [hd_ge1, he_ge9]
  have hprod_eq : -(X - 2 * Y) * (X + 2 * Y) = 3 := by nlinarith
  linarith

/-- n = 4 cannot be represented at k = 2: there are no a,b ≥ 1 with
    a(a+1) = 4·b(b+1) and disjoint intervals (b+1 < a). -/
theorem n4_k2_impossible (a b : ℕ) (hb : b ≥ 1) (hdisj : b + 1 < a) :
    (a * (a + 1) : ℕ) ≠ 4 * (b * (b + 1)) := by
  intro h
  have ha_ge1 : a ≥ 1 := by omega
  have hXge : (2 * (a : ℤ) + 1) ≥ 3 := by omega
  have hYge : (2 * (b : ℤ) + 1) ≥ 3 := by omega
  have hp := (pell_reduction.mp (show (a : ℤ) * (a + 1) = 4 * (b * (b + 1)) from mod_cast h))
  exact pell_no_4 (2 * (a : ℤ) + 1) (2 * (b : ℤ) + 1) hXge hYge hp

-- ===== SECTION 3: Positive constructions at k = 2 =====

/-- n=2: [20,21]/[14,15] = 420/210 = 2, disjoint. -/
theorem n2_k2 : (20 * 21 : ℕ) = 2 * (14 * 15) := by norm_num
theorem n2_k2_disj : 14 + 1 < 20 := by norm_num

/-- n=3: [9,10]/[5,6] = 90/30 = 3, disjoint. -/
theorem n3_k2 : (9 * 10 : ℕ) = 3 * (5 * 6) := by norm_num
theorem n3_k2_disj : 5 + 1 < 9 := by norm_num

/-- n=5: [5,6]/[2,3] = 30/6 = 5, disjoint. -/
theorem n5_k2 : (5 * 6 : ℕ) = 5 * (2 * 3) := by norm_num
theorem n5_k2_disj : 2 + 1 < 5 := by norm_num

/-- n=6: [3,4]/[1,2] = 12/2 = 6, disjoint. -/
theorem n6_k2 : (3 * 4 : ℕ) = 6 * (1 * 2) := by norm_num
theorem n6_k2_disj : 1 + 1 < 3 := by norm_num

end JSP000558
