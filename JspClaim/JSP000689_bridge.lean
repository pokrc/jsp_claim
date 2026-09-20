import JspClaim.JSP000689_helpers
import Mathlib.Combinatorics.Hypergraph.Basic

noncomputable section
open scoped BigOperators

namespace JSP000689Bridge

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Convert one hyperedge (a `Set`) to a `Finset` (possible because `α` is finite). -/
def edgeToFinset (e : Set α) : Finset α := (Set.toFinite e).toFinset

/-- The edge set of `H` as a `Finset` of `Finset`s. -/
def edgeFinset (H : Hypergraph α) : Finset (Finset α) :=
  (Set.toFinite H.edgeSet).toFinset.image edgeToFinset

/-- A non-monochromatic finite edge contains two vertices of different colors. -/
lemma finset_not_mono_has_two_colors {e : Finset α} {g : α → Fin 2}
    (hmono : ¬ Jsp689.Mono e g) : ∃ x ∈ e, ∃ y ∈ e, g x ≠ g y := by
  classical
  have hne : e.Nonempty := by
    by_contra hempty
    have htriv : Jsp689.Mono e g := by
      unfold Jsp689.Mono
      refine ⟨0, ?_⟩
      intro x hx
      exfalso
      exact hempty ⟨x, hx⟩
    exact hmono htriv
  obtain ⟨x, hx⟩ := hne
  by_contra hnot
  have hall : ∀ y ∈ e, g y = g x := by
    intro y hy
    by_contra hneq
    exact hnot ⟨y, hy, x, hx, hneq⟩
  have hmono' : Jsp689.Mono e g := by
    unfold Jsp689.Mono
    exact ⟨g x, hall⟩
  exact hmono hmono'

/-- `e ∈ E(H)` implies the converted finset is in the finset edge set. -/
lemma edgeToFinset_mem_edgeFinset {H : Hypergraph α} {e : Set α} (he : e ∈ H.edgeSet) :
    edgeToFinset e ∈ edgeFinset H := by
  simp [edgeFinset]
  exact Set.mem_image_of_mem _ he

/-- A `Good` coloring on the finset edge set is a proper coloring of `H`. -/
lemma good_imp_properColoring {H : Hypergraph α} {g : α → Fin 2}
    (hgood : Jsp689.Good (edgeFinset H) g) :
    ∀ e ∈ H.edgeSet, ∃ x ∈ e, ∃ y ∈ e, g x ≠ g y := by
  intro e he
  have hmem : edgeToFinset e ∈ edgeFinset H := edgeToFinset_mem_edgeFinset he
  have hmono : ¬ Jsp689.Mono (edgeToFinset e) g := hgood (edgeToFinset e) hmem
  have hcol := finset_not_mono_has_two_colors (e := edgeToFinset e) hmono
  rcases hcol with ⟨x, hx, y, hy, hxy⟩
  refine ⟨x, ?_, y, ?_, hxy⟩
  · simpa [edgeToFinset] using hx
  · simpa [edgeToFinset] using hy

end JSP000689Bridge
