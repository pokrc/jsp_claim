import Mathlib.Tactic

namespace JSP000243

/-!
# JSP-000243 — shortest interval for a distinct unit-fraction representation of 1

Problem as printed: What is the shortest integer interval containing distinct
denominators whose reciprocals sum to one?

Answer (this file): The minimum span is 4, achieved by [2,6] via
1/2 + 1/3 + 1/6 = 1.

**Scope (2026-09-22).** This settles the *literal* minimal-span reading: over all
representations by distinct denominators `≥ 2`, every supporting interval `[lo, hi]`
has `hi − lo ≥ 4`, and `[2, 6]` attains it. It does **not** formalize the entry's
recorded solution: the entry cites Croot [Cr01], *On unit fractions with
denominators in short intervals*, Acta Arith. 99 (2001), 99–114, which settles
Erdős problems #286 and #284 — for every `k ≥ 2` there is an interval of width
`(e − 1 + o(1))k` holding `k` distinct denominators with reciprocal sum 1,
equivalently `f(k) = (1 + o(1))k/(e − 1)`. That asymptotic law for the minimal
width as a function of `k`, and Croot's construction, are **not** proved here and
are not claimed. The scope question is raised with the maintainers in the
submission for this problem.

Approach:
  - Small cases (lo=2,3,4): bridge rational sum = 1 → natural sum = L via common
    denominator L = lcm(lo…lo+3), then kernel-reducible `decide` on the full
    powerset-quantified natural-number statement. **No `native_decide`**.
  - Large case (lo ≥ 5): at most 4 denominators, each ≥ 5, so sum ≤ 4/5 < 1.
-/

/-- Common-denominator bridge (forward direction): if every d ∈ S divides L,
    then the rational unit-fraction sum over S equals 1 implies the
    natural-number sum of L/d over S equals L. -/
private lemma unitfrac_sum_le_nat_sum
    (S : Finset ℕ) (L : ℕ) (hL : 0 < L)
    (hdiv : ∀ d ∈ S, d ∣ L) (hpos : ∀ d ∈ S, 0 < d)
    (hsum : (∑ d ∈ S, (1 : ℚ) / d) = 1) :
    (∑ d ∈ S, L / d) = L := by
  -- Show (↑(∑ L/d)) = ↑L in ℚ, then exact_mod_cast
  have hr : (∑ d ∈ S, (L : ℚ) / d) = (L : ℚ) := by
    calc ∑ d ∈ S, (L : ℚ) / d
        = ∑ d ∈ S, (L : ℚ) * ((1 : ℚ) / d) := by
            apply Finset.sum_congr rfl; intro d hd
            have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (hpos d hd).ne'
            field_simp
      _ = (L : ℚ) * ∑ d ∈ S, (1 : ℚ) / d := by rw [Finset.mul_sum]
      _ = (L : ℚ) * 1 := by rw [hsum]
      _ = ↑L := by norm_num
  have hcast : ((∑ d ∈ S, L / d : ℕ) : ℚ) = (L : ℚ) := by
    push_cast
    rw [← hr]
    apply Finset.sum_congr rfl; intro d hd
    exact_mod_cast (Nat.cast_div (hdiv d hd) (by exact_mod_cast (hpos d hd).ne'))
  exact_mod_cast hcast

/-- No subset of Icc 2 5 has natural sum 60/d = 60 (kernel-reducible `decide`). -/
private theorem nat_no_rep_2_5 :
    ∀ S ∈ (Finset.Icc (2 : ℕ) 5).powerset, ¬ (∑ d ∈ S, (60 / d : ℕ)) = 60 := by
  decide

/-- No subset of Icc 3 6 has natural sum 360/d = 360. -/
private theorem nat_no_rep_3_6 :
    ∀ S ∈ (Finset.Icc (3 : ℕ) 6).powerset, ¬ (∑ d ∈ S, (360 / d : ℕ)) = 360 := by
  decide

/-- No subset of Icc 4 7 has natural sum 840/d = 840. -/
private theorem nat_no_rep_4_7 :
    ∀ S ∈ (Finset.Icc (4 : ℕ) 7).powerset, ¬ (∑ d ∈ S, (840 / d : ℕ)) = 840 := by
  decide

/-- Every element of {2,3,4,5} divides 60. -/
private lemma divisors_60 : ∀ d ∈ (Finset.Icc (2:ℕ) 5), d ∣ 60 := by
  intro d hd
  have hlo : 2 ≤ d := (Finset.mem_Icc.mp hd).1
  have hhi : d ≤ 5 := (Finset.mem_Icc.mp hd).2
  interval_cases d <;> norm_num

private lemma divisors_360 : ∀ d ∈ (Finset.Icc (3:ℕ) 6), d ∣ 360 := by
  intro d hd
  have hlo : 3 ≤ d := (Finset.mem_Icc.mp hd).1
  have hhi : d ≤ 6 := (Finset.mem_Icc.mp hd).2
  interval_cases d <;> norm_num

private lemma divisors_840 : ∀ d ∈ (Finset.Icc (4:ℕ) 7), d ∣ 840 := by
  intro d hd
  have hlo : 4 ≤ d := (Finset.mem_Icc.mp hd).1
  have hhi : d ≤ 7 := (Finset.mem_Icc.mp hd).2
  interval_cases d <;> norm_num

private lemma pos_of_mem_icc_25 : ∀ d ∈ (Finset.Icc (2:ℕ) 5), 0 < d := by
  intro d hd; have ⟨hlo, _⟩ := Finset.mem_Icc.mp hd; omega

private lemma pos_of_mem_icc_36 : ∀ d ∈ (Finset.Icc (3:ℕ) 6), 0 < d := by
  intro d hd; have ⟨hlo, _⟩ := Finset.mem_Icc.mp hd; omega

private lemma pos_of_mem_icc_47 : ∀ d ∈ (Finset.Icc (4:ℕ) 7), 0 < d := by
  intro d hd; have ⟨hlo, _⟩ := Finset.mem_Icc.mp hd; omega

/-- No subset of distinct integers in `[2,5]` has reciprocals summing to 1. -/
theorem no_rep_2_5 :
    ¬ ∃ S ∈ (Finset.Icc (2 : ℕ) 5).powerset,
      (∑ d ∈ S, (1 : ℚ) / d) = 1 := by
  rintro ⟨S, hS, hsum⟩
  have hdiv : ∀ d ∈ S, d ∣ 60 := by
    intro d hd; exact divisors_60 d (Finset.mem_powerset.mp hS hd)
  have hpos : ∀ d ∈ S, 0 < d := by
    intro d hd; exact pos_of_mem_icc_25 d (Finset.mem_powerset.mp hS hd)
  have hnat := unitfrac_sum_le_nat_sum S 60 (by norm_num) hdiv hpos hsum
  exact absurd hnat (nat_no_rep_2_5 S hS)

/-- No subset of distinct integers in `[3,6]` has reciprocals summing to 1. -/
theorem no_rep_3_6 :
    ¬ ∃ S ∈ (Finset.Icc (3 : ℕ) 6).powerset,
      (∑ d ∈ S, (1 : ℚ) / d) = 1 := by
  rintro ⟨S, hS, hsum⟩
  have hdiv : ∀ d ∈ S, d ∣ 360 := by
    intro d hd; exact divisors_360 d (Finset.mem_powerset.mp hS hd)
  have hpos : ∀ d ∈ S, 0 < d := by
    intro d hd; exact pos_of_mem_icc_36 d (Finset.mem_powerset.mp hS hd)
  have hnat := unitfrac_sum_le_nat_sum S 360 (by norm_num) hdiv hpos hsum
  exact absurd hnat (nat_no_rep_3_6 S hS)

/-- No subset of distinct integers in `[4,7]` has reciprocals summing to 1. -/
theorem no_rep_4_7 :
    ¬ ∃ S ∈ (Finset.Icc (4 : ℕ) 7).powerset,
      (∑ d ∈ S, (1 : ℚ) / d) = 1 := by
  rintro ⟨S, hS, hsum⟩
  have hdiv : ∀ d ∈ S, d ∣ 840 := by
    intro d hd; exact divisors_840 d (Finset.mem_powerset.mp hS hd)
  have hpos : ∀ d ∈ S, 0 < d := by
    intro d hd; exact pos_of_mem_icc_47 d (Finset.mem_powerset.mp hS hd)
  have hnat := unitfrac_sum_le_nat_sum S 840 (by norm_num) hdiv hpos hsum
  exact absurd hnat (nat_no_rep_4_7 S hS)

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
    ¬ ∃ S ∈ (Finset.Icc lo hi).powerset,
      (∑ d ∈ S, (1 : ℚ) / d) = 1 := by
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
    ¬ ∃ S ∈ (Finset.Icc lo hi).powerset,
      (∑ d ∈ S, (1 : ℚ) / d) = 1 := by
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
    ∃ S ∈ (Finset.Icc (2 : ℕ) 6).powerset,
      (∑ d ∈ S, (1 : ℚ) / d) = 1 := by
  refine ⟨{2, 3, 6}, ?_, ?_⟩
  · exact Finset.mem_powerset.mpr (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> norm_num)
  · norm_num [Finset.sum_insert, Finset.sum_singleton]

/-- Main formal answer:
    * every valid interval has span at least 4;
    * span 4 is attained by `[2,6]`. -/
theorem jsp000243 :
    (∀ lo hi : ℕ, 2 ≤ lo → lo ≤ hi →
      (∃ S ∈ (Finset.Icc lo hi).powerset, (∑ d ∈ S, (1 : ℚ) / d) = 1) → 4 ≤ hi - lo) ∧
    ∃ S ∈ (Finset.Icc (2 : ℕ) 6).powerset,
      (∑ d ∈ S, (1 : ℚ) / d) = 1 := by
  constructor
  · intro lo hi hlo hlohi hrep
    by_contra hnot
    have hspan : hi ≤ lo + 3 := by omega
    exact no_rep_span_le_three hlo hlohi hspan hrep
  · exact has_rep_2_6

end JSP000243
