import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# JSP-000134 / Erdős problem 128 — a six-vertex finite verification

This module formalizes ONLY the six-vertex case. The unrestricted mathematical
problem remains OPEN. In particular, this is NOT a prize-ready formalization.

The original condition (as in Formal Conjectures, Erdős 128) requires every
induced subgraph on at least floor(n/2) vertices to contain strictly more than
n²/50 edges. For n = 6, it implies that each triple spans at least one edge.
The theorem below proves that this forces a triangle, by a finite kernel
decision of the classical Ramsey fact R(3,3) = 6.

A 6-vertex labelled undirected graph is encoded by 15 Boolean edge bits.
All 15 unordered pairs receive distinct indices (independently checked below).
No custom axioms, sorry, admit, or native_decide are used.
-/

namespace JSP000134

/-- Canonical index of the unordered pair {i,j} among the 15 pairs of Fin 6.
It is only used when i ≠ j. -/
def pairIndex (i j : Fin 6) : Fin 15 :=
  let a := min i.val j.val
  let b := max i.val j.val
  Fin.ofNat 15 (a * (11 - a) / 2 + (b - a - 1))

/-- Equality of the indexing under swapping endpoints. -/
theorem pairIndex_symm : ∀ i j : Fin 6, pairIndex i j = pairIndex j i := by
  decide

/-- Distinct unordered edges have distinct bit indices. -/
theorem pairIndex_injective :
    ∀ a b c d : Fin 6, a < b → c < d →
      pairIndex a b = pairIndex c d → a = c ∧ b = d := by
  decide

/-- Every one of the 15 bits corresponds to a genuine unordered pair. -/
theorem pairIndex_surjective :
    ∀ k : Fin 15, ∃ i j : Fin 6, i < j ∧ pairIndex i j = k := by
  decide

/-- Edges of a loop-free, symmetric six-vertex graph represented by 15 bits. -/
def Adj (graph : Fin 15 → Bool) (i j : Fin 6) : Prop :=
  i ≠ j ∧ graph (pairIndex i j) = true

theorem adj_irrefl (graph : Fin 15 → Bool) (i : Fin 6) :
    ¬ Adj graph i i := by
  simp [Adj]

theorem adj_symm (graph : Fin 15 → Bool) (i j : Fin 6) :
    Adj graph i j ↔ Adj graph j i := by
  constructor
  · rintro ⟨hij, he⟩
    refine ⟨Ne.symm hij, ?_⟩
    rw [pairIndex_symm j i]
    exact he
  · rintro ⟨hji, he⟩
    refine ⟨Ne.symm hji, ?_⟩
    rw [pairIndex_symm i j]
    exact he

/-- Three distinct vertices forming a triangle. -/
def ContainsTriangle (graph : Fin 15 → Bool) : Prop :=
  ∃ i j k : Fin 6, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
    Adj graph i j ∧ Adj graph j k ∧ Adj graph i k

/-- Three distinct vertices spanning no edge. -/
def ContainsIndependentTriple (graph : Fin 15 → Bool) : Prop :=
  ∃ i j k : Fin 6, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
    ¬ Adj graph i j ∧ ¬ Adj graph j k ∧ ¬ Adj graph i k

/-- R(3,3) ≤ 6. Kernel-checked finite case analysis of all 2^15 graphs. -/
theorem ramsey_three_three_six :
    ∀ graph : Fin 15 → Bool,
      ContainsTriangle graph ∨ ContainsIndependentTriple graph := by
  decide

/-- The exact condition the original density hypothesis imposes on triples
when n=6: 50 times their edge count must exceed 6²=36. -/
def TripleDensity (graph : Fin 15 → Bool) : Prop :=
  ∀ i j k : Fin 6, i ≠ j → j ≠ k → i ≠ k →
    36 < 50 * ((if Adj graph i j then 1 else 0) +
      (if Adj graph j k then 1 else 0) +
      (if Adj graph i k then 1 else 0))

/-- A triple satisfying the six-vertex density bound cannot be independent. -/
theorem no_independent_triple (graph : Fin 15 → Bool)
    (h : TripleDensity graph) : ¬ ContainsIndependentTriple graph := by
  rintro ⟨i, j, k, hij, hjk, hik, h1, h2, h3⟩
  have hd := h i j k hij hjk hik
  simp [h1, h2, h3] at hd

/-- Complete six-vertex special case of the original Erdős 128 conjecture.
The general n-vertex problem is NOT proved here. -/
theorem erdos128_six_vertices (graph : Fin 15 → Bool)
    (h : TripleDensity graph) : ContainsTriangle graph := by
  rcases ramsey_three_three_six graph with ht | hi
  · exact ht
  · exact False.elim (no_independent_triple graph h hi)

#print axioms JSP000134.erdos128_six_vertices
#print axioms JSP000134.ramsey_three_three_six

end JSP000134
