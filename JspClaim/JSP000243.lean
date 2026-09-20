import Mathlib.Tactic

namespace JSP000243

/-!
# JSP-000243 — shortest interval for a distinct unit-fraction representation of 1

Problem: What is the shortest integer interval containing distinct denominators
whose reciprocals sum to one?

Answer: The minimum span is 4, achieved by [2,6] via 1/2 + 1/3 + 1/6 = 1.

Approach:
  - Small cases (lo=2,3,4) verified by `native_decide` over all subsets.
  - Large case (lo ≥ 5): at most 4 denominators, each ≥ 5, so sum ≤ 4/5 < 1.
  - Span ≤ 3 implies at most 4 elements in any interval.
-/

/-- No subset of distinct integers in `[2,5]` has reciprocals summing to 1. -/
theorem no_rep_2_5 :
    ¬ ∃ S ∈ (Finset.Icc (2 : ℕ) 5).powerset, (∑ d ∈ S, (1 : ℚ) / d) = 1 := by
  native_decide

/-- No subset of distinct integers in `[3,6]` has reciprocals summing to 1. -/
theorem no_rep_3_6 :
    ¬ ∃ S ∈ (Finset.Icc (3 : ℕ) 6).powerset, (∑ d ∈ S, (1 : ℚ) / d) = 1 := by
  native_decide

/-- No subset of distinct integers in `[4,7]` has reciprocals summing to 1. -/
theorem no_rep_4_7 :
    ¬ ∃ S ∈ (Finset.Icc (4 : ℕ) 7).powerset, (∑ d ∈ S, (1 : ℚ) / d) = 1 := by
  native_decide

/-- Enlarging the right endpoint preserves representability. -/
theorem hasUnitFractionSumOne_mono_right
    {lo hi hi' : ℕ} (hhi : hi ≤ hi')
    (h : ∃ S ∈ (Finset.Icc lo hi).powerset, (∑ d ∈ S, (1 : ℚ) / d) = 1) :
    ∃ S ∈ (Finset.Icc lo hi').powerset, (∑ d ∈ S, (1 : ℚ) / d) = 1 := by
  rcases h with ⟨S, hS, hsum⟩
  refine ⟨S, Finset.mem_powerset.mpr ?_, hsum⟩
  intro d hd
  have hd' := (Finset.mem_powerset.mp hS) hd
  have hdIcc := Finset.mem_Icc.mp hd'
  exact Finset.mem_Icc.mpr ⟨hdIcc.1, le_trans hdIcc.2 hhi⟩

/-- A span at most 3 cannot work once the left endpoint is at least 5.
    There are at most four possible denominators, each contributing at most 1/5. -/
theorem no_rep_span_le_three_large_start
    {lo hi : ℕ} (hlo : 5 ≤ lo) (hlohi : lo ≤ hi)
    (hspan : hi ≤ lo + 3) :
    ¬ ∃ S ∈ (Finset.Icc lo hi).powerset, (∑ d ∈ S, (1 : ℚ) / d) = 1 := by
  rintro ⟨S, hS, hsum⟩
  have hsub : S ⊆ Finset.Icc lo hi := Finset.mem_powerset.mp hS

  have hcard : S.card ≤ 4 := by
    have h1 : (Finset.Icc lo hi).card = hi + 1 - lo := by simp
    have h2 := Finset.card_le_card hsub
    omega

  have hsum_le :
      (∑ d ∈ S, (1 : ℚ) / d) ≤ (S.card : ℚ) / 5 := by
    calc
      (∑ d ∈ S, (1 : ℚ) / d)
          ≤ ∑ _d ∈ S, (1 : ℚ) / 5 := by
            apply Finset.sum_le_sum
            intro d hd
            have hdl := (Finset.mem_Icc.mp (hsub hd)).1
            have hd5q : (5 : ℚ) ≤ d := by exact_mod_cast le_trans hlo hdl
            exact one_div_le_one_div_of_le (by norm_num) hd5q
      _ = (S.card : ℚ) / 5 := by rw [Finset.sum_const, nsmul_eq_mul]; ring

  have hlt : (S.card : ℚ) / 5 < 1 := by
    have : (S.card : ℚ) ≤ 4 := by exact_mod_cast hcard
    nlinarith

  rw [hsum] at hsum_le
  linarith

/-- No span at most 3 works when all denominators are at least 2. -/
theorem no_rep_span_le_three
    {lo hi : ℕ} (hlo : 2 ≤ lo) (hlohi : lo ≤ hi)
    (hspan : hi ≤ lo + 3) :
    ¬ ∃ S ∈ (Finset.Icc lo hi).powerset, (∑ d ∈ S, (1 : ℚ) / d) = 1 := by
  by_cases h5 : 5 ≤ lo
  · exact no_rep_span_le_three_large_start h5 hlohi hspan
  · have hcases : lo = 2 ∨ lo = 3 ∨ lo = 4 := by omega
    rcases hcases with rfl | rfl | rfl
    · intro h
      exact no_rep_2_5 (hasUnitFractionSumOne_mono_right (by omega) h)
    · intro h
      exact no_rep_3_6 (hasUnitFractionSumOne_mono_right (by omega) h)
    · intro h
      exact no_rep_4_7 (hasUnitFractionSumOne_mono_right (by omega) h)

/-- The interval `[2,6]` attains the optimum with denominators `2,3,6`. -/
theorem has_rep_2_6 :
    ∃ S ∈ (Finset.Icc (2 : ℕ) 6).powerset, (∑ d ∈ S, (1 : ℚ) / d) = 1 := by
  refine ⟨{2, 3, 6}, ?_, ?_⟩
  · exact Finset.mem_powerset.mpr (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl | rfl <;> norm_num)
  · norm_num [Finset.sum_insert, Finset.sum_singleton]

/-- Main formal answer:
    * every valid interval has span at least 4;
    * span 4 is attained by `[2,6]`. -/
theorem jsp000243 :
    (∀ lo hi : ℕ, 2 ≤ lo → lo ≤ hi →
      (∃ S ∈ (Finset.Icc lo hi).powerset, (∑ d ∈ S, (1 : ℚ) / d) = 1) → 4 ≤ hi - lo) ∧
    ∃ S ∈ (Finset.Icc (2 : ℕ) 6).powerset, (∑ d ∈ S, (1 : ℚ) / d) = 1 := by
  constructor
  · intro lo hi hlo hlohi hrep
    by_contra hnot
    have hspan : hi ≤ lo + 3 := by omega
    exact no_rep_span_le_three hlo hlohi hspan hrep
  · exact has_rep_2_6

end JSP000243
