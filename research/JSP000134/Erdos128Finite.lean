import Mathlib

/-!
# JSP-000134 / Erdős 128: a completely proved finite six-vertex case

IMPORTANT: The unrestricted original problem is OPEN. This file DOES NOT solve
the original problem and must not be registered for a prize.

It formalizes a genuine, unconditional six-vertex theorem using the standard
R(3,3) argument. The original n-vertex density premise, for n=6, forces
every triple to span at least one edge. R(3,3)=6 then forces a triangle.

No `sorry`, `admit`, `native_decide`, or custom mathematical axioms are used.
The small `decide` invocations below only verify edge-index bijectivity.
-/

namespace JSP000134

/-- The 15 unordered edges of the complete graph on six labelled vertices. -/
def pairIndex (i j : Fin 6) : Fin 15 :=
  let a := min i.val j.val
  let b := max i.val j.val
  Fin.ofNat 15 (a * (11 - a) / 2 + (b - a - 1))

theorem pairIndex_symm : ∀ i j : Fin 6, pairIndex i j = pairIndex j i := by
  decide

theorem pairIndex_injective :
    ∀ a b c d : Fin 6, a < b → c < d →
      pairIndex a b = pairIndex c d → a = c ∧ b = d := by
  decide

theorem pairIndex_surjective :
    ∀ k : Fin 15, ∃ i j : Fin 6, i < j ∧ pairIndex i j = k := by
  decide

/-- An edge bit is interpreted symmetrically; loops are absent. -/
def Adj (graph : Fin 15 → Bool) (i j : Fin 6) : Bool :=
  if i = j then false else graph (pairIndex i j)

theorem adj_irrefl (graph : Fin 15 → Bool) (i : Fin 6) :
    Adj graph i i = false := by simp [Adj]

theorem adj_symm (graph : Fin 15 → Bool) (i j : Fin 6) :
    Adj graph i j = Adj graph j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm hij
    simp only [Adj, if_neg hij, if_neg hji, pairIndex_symm i j]

/-- A monochromatic triple for a Boolean edge-coloring (the edge colors need
not satisfy symmetry for the combinatorial argument). -/
def Mono (edge : Fin 6 → Fin 6 → Bool) (x y z : Fin 6) : Prop :=
  x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
    ∃ c : Bool, edge x y = c ∧ edge y z = c ∧ edge x z = c

def neighbors (edge : Fin 6 → Fin 6 → Bool) (v : Fin 6) (c : Bool) :
    Finset (Fin 6) :=
  (Finset.univ.erase v).filter (fun w => edge v w = c)

theorem neighbors_total (edge : Fin 6 → Fin 6 → Bool) (v : Fin 6) :
    (neighbors edge v true).card + (neighbors edge v false).card = 5 := by
  have hpartition : neighbors edge v true ∪ neighbors edge v false =
      Finset.univ.erase v := by
    ext w
    simp only [neighbors, Finset.mem_union, Finset.mem_filter]
    cases edge v w <;> simp
  have hdisjoint : Disjoint (neighbors edge v true) (neighbors edge v false) := by
    rw [Finset.disjoint_left]
    intro w ht hf
    have ht' := (Finset.mem_filter.mp ht).2
    have hf' := (Finset.mem_filter.mp hf).2
    rw [ht'] at hf'
    cases hf'
  rw [← Finset.card_union_of_disjoint hdisjoint, hpartition]
  simp

theorem pigeonhole_edges (edge : Fin 6 → Fin 6 → Bool) (v : Fin 6) :
    ∃ c : Bool, 3 ≤ (neighbors edge v c).card := by
  have ht := neighbors_total edge v
  by_cases hr : 3 ≤ (neighbors edge v true).card
  · exact ⟨true, hr⟩
  · exact ⟨false, by omega⟩

private theorem bool_eq_not_of_ne {a c : Bool} (h : a ≠ c) : a = !c := by
  cases a <;> cases c <;> simp_all

/-- R(3,3) ≤ 6, via a fixed vertex and three neighbors of the same color.
The proof is symbolic, not a brute force search over 32768 graphs. -/
theorem ramsey_six (edge : Fin 6 → Fin 6 → Bool) :
    ∃ x y z, Mono edge x y z := by
  let v : Fin 6 := 0
  obtain ⟨c, hc⟩ := pigeonhole_edges edge v
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card_iff.mp (by omega :
      2 < (neighbors edge v c).card)
  have hvx := (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).1
  have hvy := (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).1
  have hvz := (Finset.mem_erase.mp (Finset.mem_filter.mp hz).1).1
  have evx := (Finset.mem_filter.mp hx).2
  have evy := (Finset.mem_filter.mp hy).2
  have evz := (Finset.mem_filter.mp hz).2
  by_cases hcx : edge x y = c
  · exact ⟨v, x, y, hvx.symm, hxy, hvy.symm, c, evx, hcx, evy⟩
  by_cases hcy : edge y z = c
  · exact ⟨v, y, z, hvy.symm, hyz, hvz.symm, c, evy, hcy, evz⟩
  by_cases hcz : edge x z = c
  · exact ⟨v, x, z, hvx.symm, hxz, hvz.symm, c, evx, hcz, evz⟩
  exact ⟨x, y, z, hxy, hyz, hxz, !c,
    bool_eq_not_of_ne hcx, bool_eq_not_of_ne hcy, bool_eq_not_of_ne hcz⟩

def ContainsTriangle (graph : Fin 15 → Bool) : Prop :=
  ∃ i j k : Fin 6, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
    Adj graph i j = true ∧ Adj graph j k = true ∧ Adj graph i k = true

def ContainsIndependentTriple (graph : Fin 15 → Bool) : Prop :=
  ∃ i j k : Fin 6, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
    Adj graph i j = false ∧ Adj graph j k = false ∧ Adj graph i k = false

/-- A noncomputational proof of the universal Ramsey dichotomy. -/
theorem ramsey_three_three_six (graph : Fin 15 → Bool) :
    ContainsTriangle graph ∨ ContainsIndependentTriple graph := by
  obtain ⟨i, j, k, hij, hjk, hik, c, h1, h2, h3⟩ := ramsey_six (Adj graph)
  cases c with
  | false => exact Or.inr ⟨i, j, k, hij, hjk, hik, h1, h2, h3⟩
  | true => exact Or.inl ⟨i, j, k, hij, hjk, hik, h1, h2, h3⟩

/-- For n=6, the exact original inequality 50*|E(G[S])| > n²
restricted to triples S (which are all the smallest qualifying subsets). -/
def TripleDensity (graph : Fin 15 → Bool) : Prop :=
  ∀ i j k : Fin 6, i ≠ j → j ≠ k → i ≠ k →
    36 < 50 * ((if Adj graph i j then 1 else 0) +
      (if Adj graph j k then 1 else 0) +
      (if Adj graph i k then 1 else 0))

theorem no_independent_triple (graph : Fin 15 → Bool)
    (h : TripleDensity graph) : ¬ ContainsIndependentTriple graph := by
  rintro ⟨i, j, k, hij, hjk, hik, h1, h2, h3⟩
  have hd := h i j k hij hjk hik
  simp [h1, h2, h3] at hd

/-- Full proof of the six-vertex special case; NOT a proof for general n. -/
theorem erdos128_six_vertices (graph : Fin 15 → Bool)
    (h : TripleDensity graph) : ContainsTriangle graph := by
  rcases ramsey_three_three_six graph with ht | hi
  · exact ht
  · exact False.elim (no_independent_triple graph h hi)

#print axioms JSP000134.ramsey_six
#print axioms JSP000134.erdos128_six_vertices

end JSP000134
