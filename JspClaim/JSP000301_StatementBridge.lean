import JspClaim.JSP000301
import Mathlib.Tactic

/-!
# JSP-000301 — exact yes/no question bridge

The selected prize PR pins the original kernel proof at commit
0a2313e9c66df33d010ffeea30f12172ded89c0d.
This additional module does not alter that historical proof or its priority anchor.

The original statement quantifies over **positive** consecutive integers.
The Golomb counterexample from the existing module refutes the universal question.
-/

namespace JSP000301

/-- The original JSP-000301 yes/no question, explicitly restricted to positive
consecutive integers. It is false by Golomb's counterexample. -/
def PublishedYesNoQuestion : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → a + 1 = b →
    Powerful a → Powerful b →
      (∃ m : ℕ, m ^ 2 = a) ∨ (∃ m : ℕ, m ^ 2 = b)

/-- A counterexample with positivity explicit, unlike a bare existential witness. -/
theorem positive_counterexample :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + 1 = b ∧
      Powerful a ∧ Powerful b ∧
      ¬ (∃ m : ℕ, m ^ 2 = a) ∧
      ¬ (∃ m : ℕ, m ^ 2 = b) := by
  exact ⟨12167, 12168, by norm_num, by norm_num, by norm_num,
    powerful_12167, powerful_12168, not_square_12167, not_square_12168⟩

/-- The direct negative answer to the universally quantified published question. -/
theorem published_question_false : ¬ PublishedYesNoQuestion := by
  intro h
  have hsq : (∃ m : ℕ, m ^ 2 = 12167) ∨ (∃ m : ℕ, m ^ 2 = 12168) :=
    h 12167 12168 (by norm_num) (by norm_num) (by norm_num)
      powerful_12167 powerful_12168
  exact hsq.elim not_square_12167 not_square_12168

end JSP000301
