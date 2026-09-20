import Mathlib.Tactic

namespace JSP000554

def ConsecutivePrimes (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧
    ∀ n : ℕ, p < n → n < q → ¬ n.Prime

def HasRoughInteger (p q : ℕ) : Prop :=
  ∃ n : ℕ, p < n ∧ n < q ∧ q - p ≤ n.minFac

/-- `7, 11` are consecutive primes. -/
lemma seven_eleven_consecutive : ConsecutivePrimes 7 11 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro n hn7 hn11
  interval_cases n <;> decide

/-- There is no rough integer in the gap (7, 11): the only integers are
8, 9, 10, with minFac 2, 3, 2 respectively, all < gap 4. -/
lemma not_hasRoughInteger_7_11 : ¬ HasRoughInteger 7 11 := by
  rintro ⟨n, hn7, hn11, hrough⟩
  have hn_cases : n = 8 ∨ n = 9 ∨ n = 10 := by omega
  rcases hn_cases with rfl | rfl | rfl
  · have : Nat.minFac 8 = 2 := by norm_num
    rw [this] at hrough
    norm_num at hrough
  · have : Nat.minFac 9 = 3 := by norm_num
    rw [this] at hrough
    norm_num at hrough
  · have : Nat.minFac 10 = 2 := by norm_num
    rw [this] at hrough
    norm_num at hrough

theorem jsp000554 :
    ¬ ∀ p q : ℕ, ConsecutivePrimes p q → HasRoughInteger p q := by
  intro h
  exact not_hasRoughInteger_7_11 (h 7 11 seven_eleven_consecutive)

end JSP000554
