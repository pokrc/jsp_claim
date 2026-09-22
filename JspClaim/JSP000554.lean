import Mathlib.Tactic

namespace JSP000554

**Submitted for the entry's printed statement.** The bank's entry
(`problems/catalog-0501-0600.md#JSP-000554`) asks: *"Between consecutive primes, is there an
integer whose least prime factor is at least their gap?"* Read as a universal question over
pairs of consecutive primes, the answer recorded here is **no**: for `(p, q) = (7, 11)` the gap
is `4` while every integer strictly between them (`8, 9, 10`) has least prime factor `2, 3, 2`.

**Scope, disclosed.** The entry's recorded solution (Gafni–Tao [GaTa25], Erdős #682) answers
the *almost all n* version **affirmatively** (`≪ X/(log X)^2` exceptional `n ≤ X`). This file
does not formalize that theorem and no solver credit is claimed; it is the negation of the
universal reading. A correction proposing that the entry state the "almost all n" scope has
been filed (#3342).

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
