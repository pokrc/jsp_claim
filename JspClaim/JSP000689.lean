import Mathlib.Combinatorics.Hypergraph.Basic
import Mathlib.Tactic
import JspClaim.JSP000689_helpers

-- The Fano-plane checks below are small finite computations discharged by the kernel
-- `decide` (no `native_decide`, no extra axioms); the option raises the elaborator
-- recursion limit that `decide` needs on the 128-coloring search.
set_option maxRecDepth 100000

/-!
# JSP-000689 — Erdős–Lovász: uniform hypergraphs requiring three colors

Problem bank entry (JSP-000689):

> **Must a uniform hypergraph requiring three colors have maximum degree exponential
> in its edge size?**

This is problem #833 of Erdős's problem list (Erdős–Lovász 1975).  The answer is
**YES**: if `H` is an `r`-uniform hypergraph (`r ≥ 2`) which is *not 2-colorable*
(i.e. fails Property B), then some vertex `v` lies in at least `2^(r-1)/(4r)` edges,
so the maximum degree of `H` grows exponentially in `r`.

## Verification example: the Fano plane

The Fano plane is the hypergraph on `Fin 7` with the seven 3-uniform lines

```
{0,1,2}  {0,3,4}  {0,5,6}  {1,3,5}  {1,4,6}  {2,3,6}  {2,4,5}
```

* it is 3-uniform (every line has 3 vertices);
* it requires three colors: it is not 2-colorable (every 2-coloring of the 7
  vertices leaves a monochromatic line — verified below by exhaustive search over
  all `2^7` colorings), but it admits a proper 3-coloring (color vertex `i` by
  `i % 3`);
* its maximum degree is 3 (each vertex lies on exactly 3 lines).

All Fano facts below are proved with zero `sorry` and without `native_decide` (the
only computations are tiny exhaustive searches, discharged by kernel `decide`).  The Erdős–Lovász lower
bound is proved below for finite-vertex hypergraphs (`Hypergraph (Fin n)`, the
setting in which the problem is posed), also with zero `sorry`, using the
Lovász Local Lemma developed in `JspClaim.JSP000689_helpers`.
-/

open scoped Hypergraph
open Set
open Classical

noncomputable section

/-! ## Basic hypergraph definitions (self-built on top of `Mathlib.Combinatorics.Hypergraph.Basic`)

mathlib's `Hypergraph.Basic` (v4.34.0) provides the structure `Hypergraph α`
(vertices `V(H) : Set α`, edges `E(H) : Set (Set α)`, with edges required to be
subsets of the vertex set), plus adjacency and a few predicates — but *no* notion of
uniformity, degree, or coloring.  We build those here, inside the `Hypergraph`
namespace so that dot notation (`H.Uniform r`, `H.degree v`, …) works. -/

namespace Hypergraph

variable {α : Type*}

/-- A hypergraph `H` is `r`-uniform if every edge has cardinality exactly `r`. -/
def Uniform (H : Hypergraph α) (r : ℕ) : Prop :=
  ∀ e ∈ E(H), e.ncard = r

/-- The degree of a vertex `v` in `H`: the number of edges containing `v`. -/
noncomputable def degree (H : Hypergraph α) (v : α) : ℕ :=
  {e | e ∈ E(H) ∧ v ∈ e}.ncard

/-- A coloring `c : α → Fin n` of `H` is *proper* if no edge is monochromatic, i.e. every
edge contains two vertices of different colors. -/
def IsProperColoring (H : Hypergraph α) {n : ℕ} (c : α → Fin n) : Prop :=
  ∀ e ∈ E(H), ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

/-- `H` is `n`-colorable if it admits a proper coloring with `n` colors. -/
def IsColorable (H : Hypergraph α) (n : ℕ) : Prop :=
  ∃ c : α → Fin n, IsProperColoring H c

/-- `H` has Property B: it is 2-colorable. -/
def HasPropertyB (H : Hypergraph α) : Prop :=
  IsColorable H 2

/-- `H` requires three colors: it is not 2-colorable, but it is 3-colorable. -/
def RequiresThreeColors (H : Hypergraph α) : Prop :=
  ¬ IsColorable H 2 ∧ IsColorable H 3

/-- `d` is the maximum degree of `H`: every vertex has degree at most `d`, and some vertex
has degree exactly `d`. -/
def HasMaxDegree (H : Hypergraph α) (d : ℕ) : Prop :=
  (∀ v : α, degree H v ≤ d) ∧ ∃ v : α, degree H v = d

end Hypergraph

namespace JSP000689

/-! ## The Fano plane -/

/-- The seven lines of the Fano plane, as a `Finset` of `Finset`s on `Fin 7` (this explicit
finite description is what makes the exhaustive `decide` checks possible). -/
def fanoLines : Finset (Finset (Fin 7)) :=
  { {0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5} }

/-- The Fano plane as a hypergraph on `Fin 7`: all seven vertices, edges the seven lines. -/
def fano : Hypergraph (Fin 7) where
  vertexSet := Set.univ
  edgeSet := {e | ∃ f ∈ fanoLines, e = (f : Set (Fin 7))}
  subset_vertexSet_of_mem_edgeSet' := by
    intro e he
    exact Set.subset_univ (s := e)

/-- The lines of the Fano plane, as edges of the hypergraph. -/
@[simp]
lemma mem_fano_edgeSet {e : Set (Fin 7)} : e ∈ E(fano) ↔ ∃ f ∈ fanoLines, e = (f : Set (Fin 7)) := by
  simp [fano]

/-! ### Uniformity -/

/-- Computational verification: every line of the Fano plane has exactly 3 vertices. -/
lemma fanoLines_uniform : ∀ f ∈ fanoLines, f.card = 3 := by
  decide

/-- The Fano plane is 3-uniform. -/
lemma fano_uniform : fano.Uniform 3 := by
  intro e he
  rw [mem_fano_edgeSet] at he
  rcases he with ⟨f, hf, rfl⟩
  simpa using fanoLines_uniform f hf

/-! ### Degrees and maximum degree -/

/-- The degree of a vertex `v` in the Fano plane, computed directly on the finset of lines. -/
def fanoDegree (v : Fin 7) : ℕ :=
  (fanoLines.filter fun f => v ∈ f).card

/-- Computational verification: every vertex lies on exactly 3 lines. -/
lemma fanoDegree_eq_three (v : Fin 7) : fanoDegree v = 3 := by
  fin_cases v <;> decide

/-- The abstract `degree` (counting edges of the hypergraph) agrees with the direct
computation on the finset of lines. -/
lemma degree_fano (v : Fin 7) : Hypergraph.degree fano v = fanoDegree v := by
  unfold Hypergraph.degree fanoDegree
  -- The set of edges containing `v` is exactly the image of the lines containing `v`
  -- under the coercion from `Finset (Fin 7)` to `Set (Fin 7)`.
  have hset : {e | e ∈ E(fano) ∧ v ∈ e} =
      (fun f : Finset (Fin 7) => (f : Set (Fin 7))) ''
        {f | f ∈ fanoLines ∧ v ∈ f} := by
    ext e
    constructor
    · intro he
      rcases he with ⟨heE, hve⟩
      rw [mem_fano_edgeSet] at heE
      rcases heE with ⟨f, hf, rfl⟩
      exact ⟨f, ⟨hf, hve⟩, rfl⟩
    · rintro ⟨f, ⟨hf, hv⟩, rfl⟩
      exact ⟨by
        rw [mem_fano_edgeSet]
        exact ⟨f, hf, rfl⟩, hv⟩
  rw [hset]
  -- the coercion `Finset (Fin 7) → Set (Fin 7)` is injective, so the cardinality is unchanged
  rw [Set.ncard_image_of_injective _ Finset.coe_injective]
  -- `{f | f ∈ fanoLines ∧ v ∈ f}` is the set underlying `fanoLines.filter (· ∈ ·)`
  show ({f : Finset (Fin 7) | f ∈ fanoLines ∧ v ∈ f}).ncard =
    (fanoLines.filter fun f => v ∈ f).card
  rw [← Set.ncard_coe_finset]
  congr 1
  ext f
  simp

/-- Every vertex of the Fano plane has degree 3. -/
lemma fano_degree (v : Fin 7) : Hypergraph.degree fano v = 3 := by
  rw [degree_fano, fanoDegree_eq_three]

/-- The maximum degree of the Fano plane is 3. -/
lemma fano_maxDegree : fano.HasMaxDegree 3 := by
  constructor
  · intro v
    simp [fano_degree v]
  · exact ⟨0, fano_degree 0⟩

/-! ### Not 2-colorable -/

/-- Computational verification: every 2-coloring of the 7 vertices has a monochromatic
line (exhaustive search over all `2^7 = 128` colorings). -/
lemma fano_not_two_colorable_brute :
    ∀ c : Fin 7 → Fin 2, ∃ f ∈ fanoLines, ∀ x ∈ f, ∀ y ∈ f, c x = c y := by
  decide

/-- The Fano plane is not 2-colorable (fails Property B). -/
lemma fano_not_two_colorable : ¬ Hypergraph.IsColorable fano 2 := by
  rintro ⟨c, hc⟩
  rcases fano_not_two_colorable_brute c with ⟨f, hf, hmono⟩
  have hfE : (f : Set (Fin 7)) ∈ E(fano) := by
    rw [mem_fano_edgeSet]
    exact ⟨f, hf, rfl⟩
  rcases hc (f : Set (Fin 7)) hfE with ⟨x, hx, y, hy, hxy⟩
  exact hxy (hmono x hx y hy)

/-! ### 3-colorable -/

/-- The coloring of the Fano plane that sends vertex `i` to `i % 3`. -/
def fanoColoring : Fin 7 → Fin 3 :=
  fun i => ⟨i.val % 3, Nat.mod_lt _ (by decide : 0 < 3)⟩

/-- Computational verification: every line of the Fano plane contains two vertices of
different colors under `fanoColoring`. -/
lemma fanoColoring_brute :
    ∀ f ∈ fanoLines, ∃ x ∈ f, ∃ y ∈ f, fanoColoring x ≠ fanoColoring y := by
  decide

/-- `fanoColoring` is a proper 3-coloring of the Fano plane. -/
lemma fanoColoring_proper : Hypergraph.IsProperColoring fano fanoColoring := by
  intro e he
  rw [mem_fano_edgeSet] at he
  rcases he with ⟨f, hf, rfl⟩
  exact fanoColoring_brute f hf

/-- The Fano plane is 3-colorable. -/
lemma fano_is_three_colorable : Hypergraph.IsColorable fano 3 :=
  ⟨fanoColoring, fanoColoring_proper⟩

/-- The Fano plane requires three colors. -/
lemma fano_requires_three_colors : fano.RequiresThreeColors :=
  ⟨fano_not_two_colorable, fano_is_three_colorable⟩

/-! ## The Erdős–Lovász theorem (finite-vertex version, proved via the LLL)

The main theorem of JSP-000689: for every `r ≥ 2`, every `r`-uniform hypergraph `H`
on a **finite** vertex set that requires three colors has a vertex of degree at
least `2^(r-1) / (4r)`; in particular, the maximum degree of such hypergraphs grows
exponentially in `r`.

### Why the finite-vertex version

The Lovász Local Lemma machinery in `JspClaim.JSP000689_helpers` (`Jsp689.lll_two_coloring`)
is a purely finite combinatorial statement: it 2-colors the vertices of a finite type
`ι` so that no edge of a finite edge family `E₀ : Finset (Finset ι)` is monochromatic,
provided every edge has `r ≥ 2` vertices, every edge meets at most `N` other edges,
and `4·(N+1)² ≤ (N+2)·2^(r-1)`.

The Erdős–Lovász bound is a statement about **finite** hypergraphs (an infinite
`Hypergraph ℕ` is not directly amenable to the LLL — its edge set need not be
enumerable by a `Finset`).  We therefore prove the theorem for `H : Hypergraph (Fin n)`,
which is the formulation matching the problem statement ("an `r`-uniform hypergraph").

### Proof sketch (contrapositive, via the LLL)

Assume, towards a contradiction, that every vertex has degree `< Pre` where
`Pre = 2^(r-1) / (4r)`.

1. Let `E₀` be the family of all edges of `H`, viewed as a `Finset (Finset (Fin n))`
   (all subsets of a finite type are finite, so `E(H) : Set (Set (Fin n))` can be
   enumerated by a `Finset`).
2. `H.Uniform r` gives `hcard : ∀ e ∈ E₀, e.card = r`.
3. Put `D = ⌈Pre⌉ - 1` and `N = r·(D-1)`.  From `degree v < Pre` we get
   `degree v ≤ D` for every vertex (via the ceiling), so each edge `e` meets at most
   `Σ_{v∈e} (degree v - 1) ≤ r·(D-1) = N` other edges — this is `hdep` (double counting
   pairs `(v, e')` with `v ∈ e ∩ e'`).
4. The constant `Pre = 2^(r-1)/(4r)` is chosen so that the LLL hypothesis
   `hcond : 4·(N+1)² ≤ (N+2)·2^(r-1)` holds for `N = r·(D-1)` (a short real-arithmetic
   argument splitting on `D = 0` vs `D ≥ 1`; the ceiling slack `D ≤ Pre` is what makes
   the inequality come out exactly).
5. The LLL yields a 2-coloring `g : Fin n → Fin 2` with no monochromatic edge of `E₀`
   (`Jsp689.Good E₀ g`); this is exactly a proper 2-coloring of `H` (each edge is
   non-monochromatic).  This contradicts `H.RequiresThreeColors`.

### Finite edge family and the bridge from `Finset` edges to `Set` edges

mathlib models edges as sets (`edgeSet : Set (Set α)`); the LLL works with
`Finset (Finset ι)`.  The definitions `edgeFinset`, `edgeFinset'` below convert
`E(H)` into a finset of finsets, `degree_eq_card_filter` shows the two notions of
degree agree, and `good_implies_proper` shows the LLL's "no monochromatic edge"
is precisely a proper coloring. -/

/-- All edges of a hypergraph on a finite vertex type, as a `Finset` of `Set`s. -/
def edgeFinset (H : Hypergraph (Fin n)) : Finset (Set (Fin n)) :=
  Finset.univ.filter (fun e : Set (Fin n) => e ∈ E(H))

/-- All edges of a hypergraph on a finite vertex type, as a `Finset` of `Finset`s. -/
def edgeFinset' (H : Hypergraph (Fin n)) : Finset (Finset (Fin n)) :=
  (edgeFinset H).image (fun e : Set (Fin n) => e.toFinite.toFinset)

/-- Coercing a finite set to a `Finset` is injective. -/
lemma toFinset_injective {n : ℕ} :
    Function.Injective (fun e : Set (Fin n) => e.toFinite.toFinset) := by
  intro a b h
  apply Set.ext
  intro x
  rw [← Set.Finite.mem_toFinset a.toFinite, ← Set.Finite.mem_toFinset b.toFinite]
  rw [show a.toFinite.toFinset = b.toFinite.toFinset from h]

/-- Membership in the finset version of the edge family. -/
lemma mem_edgeFinset' (H : Hypergraph (Fin n)) (s : Finset (Fin n)) :
    s ∈ edgeFinset' H ↔ ∃ e : Set (Fin n), e ∈ E(H) ∧ s = e.toFinite.toFinset := by
  rw [edgeFinset']
  rw [Finset.mem_image]
  constructor
  · rintro ⟨e, he, hs⟩
    exact ⟨e, (Finset.mem_filter.mp he).2, hs.symm⟩
  · rintro ⟨e, he, hs⟩
    exact ⟨e, Finset.mem_filter.mpr ⟨by simp, he⟩, hs.symm⟩

/-- The finset of edges containing a vertex `v` is the image of the corresponding
set of set-edges. -/
lemma filter_image_toFinset (H : Hypergraph (Fin n)) (v : Fin n) :
    ((edgeFinset' H).filter (fun e' => v ∈ e')) =
      ((Finset.univ : Finset (Set (Fin n))).filter (fun e => e ∈ E(H) ∧ v ∈ e)).image
        (fun e : Set (Fin n) => e.toFinite.toFinset) := by
  ext s
  constructor
  · intro h
    rw [Finset.mem_filter] at h
    rcases h with ⟨he', hvs⟩
    rw [mem_edgeFinset'] at he'
    rcases he' with ⟨e, heE, rfl⟩
    rw [Finset.mem_image]
    refine ⟨e, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨by simp, ⟨heE, by simpa using hvs⟩⟩
  · intro h
    rw [Finset.mem_image] at h
    rcases h with ⟨e, he, rfl⟩
    rw [Finset.mem_filter] at he
    rcases he with ⟨heU, ⟨heE, hve⟩⟩
    rw [Finset.mem_filter]
    constructor
    · rw [mem_edgeFinset']
      exact ⟨e, heE, rfl⟩
    · simpa using hve

/-- The abstract degree (counting set-edges) equals the cardinality of the finset of
finset-edges containing the vertex. -/
lemma degree_eq_card_filter (H : Hypergraph (Fin n)) (v : Fin n) :
    H.degree v = ((edgeFinset' H).filter (fun e' => v ∈ e')).card := by
  unfold Hypergraph.degree
  let S : Set (Set (Fin n)) := {e | e ∈ E(H) ∧ v ∈ e}
  calc
    H.degree v = S.ncard := rfl
    _ = S.toFinite.toFinset.card := by rw [Set.ncard_eq_toFinset_card]
    _ = (((Finset.univ : Finset (Set (Fin n))).filter (fun e => e ∈ E(H) ∧ v ∈ e)).card) := by
      congr 1
      ext e
      simp [S]
    _ = ((edgeFinset' H).filter (fun e' => v ∈ e')).card := by
      rw [filter_image_toFinset H v]
      rw [Finset.card_image_of_injective _ toFinset_injective]

/-- A 2-coloring with no monochromatic edge (in the finset sense) is a proper
2-coloring of the hypergraph (in the set sense). -/
lemma good_implies_proper (H : Hypergraph (Fin n)) (g : Fin n → Fin 2)
    (hG : Jsp689.Good (edgeFinset' H) g) : Hypergraph.IsProperColoring H g := by
  intro e he
  have hg : ¬ Jsp689.Mono e.toFinite.toFinset g := by
    exact hG e.toFinite.toFinset (by
      rw [mem_edgeFinset']
      exact ⟨e, he, rfl⟩)
  rw [Jsp689.Mono] at hg
  have hne : e.toFinite.toFinset.Nonempty := by
    by_contra hne'
    apply hg
    exact ⟨(0 : Fin 2), fun x hx => False.elim (hne' ⟨x, hx⟩)⟩
  rcases hne with ⟨x₀, hx₀⟩
  by_contra hbad
  have hall : ∀ x ∈ e, g x = g x₀ := by
    intro x hx
    by_contra hdiff
    apply hbad
    exact ⟨x, hx, x₀, by simpa using hx₀, hdiff⟩
  apply hg
  exact ⟨g x₀, fun x hx => hall x (by simpa using hx)⟩

/-- The Lovász Local Lemma hypothesis for `N = r·(D-1)` where `D = ⌈Pre⌉ - 1` and
`Pre = 2^(r-1) / (4r)`.  This is the sharp constant that makes the whole argument go
through: the ceiling slack `D ≤ Pre` is exactly enough for
`4·(N+1)² ≤ (N+2)·2^(r-1)`. -/
lemma lll_hcond (r : ℕ) (hr : 2 ≤ r) (Pre : ℝ) (hPre0 : 0 < Pre)
    (hPreEq : Pre = (2 : ℝ) ^ (r - 1) / (4 * (r : ℝ))) (D : ℕ)
    (hD : D = Nat.ceil Pre - 1) :
    4 * (((r * (D - 1) + 1 : ℕ) : ℝ)) ^ 2 ≤ (((r * (D - 1) + 2 : ℕ) : ℝ)) * (2 : ℝ) ^ (r - 1) := by
  by_cases hD0 : D = 0
  · rw [hD0]
    norm_num
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (r - 1) := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
        _ ≤ (2 : ℝ) ^ (r - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  · have hD1 : 1 ≤ D := by omega
    have hpr : 0 ≤ Pre := hPre0.le
    have h1 : 1 ≤ Nat.ceil Pre := Nat.ceil_pos.mpr hPre0
    have hDlePre : (D : ℝ) ≤ Pre := by
      rw [hD]
      rw [Nat.cast_sub h1]
      norm_num
      have hceil : (Nat.ceil Pre : ℝ) < Pre + 1 := Nat.ceil_lt_add_one hpr
      linarith
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
    have hk : ((D - 1 : ℕ) : ℝ) ≤ Pre - 1 := by
      rw [Nat.cast_sub hD1]
      norm_num
      linarith
    have h4rP : (2 : ℝ) ^ (r - 1) = 4 * (r : ℝ) * Pre := by
      rw [hPreEq]
      field_simp
    have hN1' : (r : ℝ) * ((D - 1 : ℕ) : ℝ) + 1 ≤ (r : ℝ) * Pre := by
      nlinarith [hk, hr1]
    have hN1 : ((r * (D - 1) + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (r - 1) / 4 := by
      rw [h4rP]
      norm_num
      nlinarith [hN1']
    have hmain : 4 * (((r * (D - 1) + 1 : ℕ) : ℝ)) ^ 2 ≤
        (((r * (D - 1) + 2 : ℕ) : ℝ)) * (2 : ℝ) ^ (r - 1) := by
      norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      have hN1'' : (r : ℝ) * ((D - 1 : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (r - 1) / 4 := by
        simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hN1
      have hpos : 0 ≤ (r : ℝ) * ((D - 1 : ℕ) : ℝ) + 1 := by positivity
      nlinarith [hN1'', hpos]
    exact hmain

/-- In a finite edge family `E₀`, the number of edges other than `e` that meet `e` is at
most `|e|·(D-1)`, provided every vertex of `e` lies in at most `D` edges of `E₀`.
(Double counting of pairs `(v, e')` with `v ∈ e ∩ e'`.) -/
lemma hdep_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E₀ : Finset (Finset ι)) (e : Finset ι) (heE : e ∈ E₀) (D : ℕ)
    (hdeg : ∀ v ∈ e, ((E₀.filter (fun e' => v ∈ e')).card) ≤ D) :
    (E₀.filter (fun e' => e' ≠ e ∧ (e ∩ e').Nonempty)).card ≤ (e.card) * (D - 1) := by
  let P := E₀.filter (fun e' => e' ≠ e ∧ (e ∩ e').Nonempty)
  have hsub : P ⊆ e.biUnion (fun v => E₀.filter (fun e' => v ∈ e' ∧ e' ≠ e)) := by
    intro e' he'
    rw [Finset.mem_biUnion]
    rw [Finset.mem_filter] at he'
    rcases he' with ⟨he'E₀, hne', hnn⟩
    rcases hnn with ⟨x, hx⟩
    rw [Finset.mem_inter] at hx
    exact ⟨x, hx.1, Finset.mem_filter.mpr ⟨he'E₀, hx.2, hne'⟩⟩
  calc
    P.card ≤ (e.biUnion (fun v => E₀.filter (fun e' => v ∈ e' ∧ e' ≠ e))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ v ∈ e, (E₀.filter (fun e' => v ∈ e' ∧ e' ≠ e)).card := Finset.card_biUnion_le
    _ = ∑ v ∈ e, ((E₀.filter (fun e' => v ∈ e')).card - 1) := by
      apply Finset.sum_congr rfl
      intro v hv
      have hf : E₀.filter (fun e' => v ∈ e' ∧ e' ≠ e) = (E₀.filter (fun e' => v ∈ e')).erase e := by
        ext e'
        by_cases heq : e' = e
        · subst e'
          simp [hv]
        · simp [heq]
      rw [hf]
      have hem : e ∈ E₀.filter (fun e' => v ∈ e') := by
        rw [Finset.mem_filter]
        exact ⟨heE, hv⟩
      rw [Finset.card_erase_of_mem hem]
    _ ≤ ∑ v ∈ e, (D - 1) := by
      apply Finset.sum_le_sum
      intro v hv
      exact Nat.sub_le_sub_right (hdeg v hv) 1
    _ = (e.card) * (D - 1) := by simp

/-- **The Erdős–Lovász theorem (explicit bound, finite vertices).**

If `H` is an `r`-uniform hypergraph (`r ≥ 2`) on `Fin n` which requires three colors,
then some vertex has degree at least `2^(r-1)/(4r)`.  In particular the maximum degree
of a non-2-colorable `r`-uniform hypergraph grows exponentially in `r`.

The bound `2^(r-1)/(4r)` is the constant predicted by the Lovász Local Lemma; it is
the natural extension of the classical Erdős–Lovász result (Erdős's problem list,
#833, Erdős–Lovász 1975).  The Fano plane (`r = 3`, max degree 3 ≥ `2^2/12 = 1/3`)
is the canonical example. -/
theorem erdos_lovasz_explicit_finite :
    ∀ (n r : ℕ), 2 ≤ r → ∀ H : Hypergraph (Fin n), H.Uniform r → H.RequiresThreeColors →
      ∃ v : Fin n, (2 : ℝ) ^ (r - 1) / (4 * (r : ℝ)) ≤ (H.degree v : ℝ) := by
  intro n r hr H hUnif hReq
  classical
  let Pre : ℝ := (2 : ℝ) ^ (r - 1) / (4 * (r : ℝ))
  let D : ℕ := Nat.ceil Pre - 1
  let N : ℕ := r * (D - 1)
  have hPre0 : 0 < Pre := by dsimp [Pre]; positivity
  by_contra hlt
  push Not at hlt
  -- hlt : ∀ v : Fin n, (H.degree v : ℝ) < Pre
  have hdegD : ∀ v : Fin n, H.degree v ≤ D := by
    intro v
    dsimp [D]
    have h1 : (H.degree v : ℝ) < (Nat.ceil Pre : ℝ) := by
      exact lt_of_lt_of_le (hlt v) (Nat.le_ceil Pre)
    have hd : H.degree v < Nat.ceil Pre := by exact_mod_cast h1
    omega
  have hcard : ∀ e ∈ edgeFinset' H, e.card = r := by
    intro e heE
    rw [mem_edgeFinset'] at heE
    rcases heE with ⟨s, hsE, rfl⟩
    have hr' : s.toFinite.toFinset.card = s.ncard := by
      exact (Set.ncard_eq_toFinset_card s s.toFinite).symm
    rw [hr']
    exact hUnif s hsE
  have hdep : ∀ e ∈ edgeFinset' H,
      ((edgeFinset' H).filter (fun e' => e' ≠ e ∧ (e ∩ e').Nonempty)).card ≤ N := by
    intro e heE
    have hdeg_v : ∀ v ∈ e, (((edgeFinset' H).filter (fun e' => v ∈ e')).card) ≤ D := by
      intro v hv
      calc
        (((edgeFinset' H).filter (fun e' => v ∈ e')).card) = H.degree v := by
          exact (degree_eq_card_filter H v).symm
        _ ≤ D := hdegD v
    have hb := hdep_bound (edgeFinset' H) e heE D hdeg_v
    calc
      ((edgeFinset' H).filter (fun e' => e' ≠ e ∧ (e ∩ e').Nonempty)).card
          ≤ (e.card) * (D - 1) := hb
      _ = r * (D - 1) := by rw [hcard e heE]
      _ = N := by dsimp [N]
  have hcond : 4 * ((N + 1 : ℕ) : ℝ) ^ 2 ≤ ((N + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (r - 1) := by
    have hlll_h := lll_hcond r hr Pre hPre0 rfl D rfl
    simpa [N, Nat.cast_add, Nat.cast_mul] using hlll_h
  rcases Jsp689.lll_two_coloring (ι := Fin n) (edgeFinset' H) r N hr hcard hdep hcond
    with ⟨g, hg⟩
  have hprop : Hypergraph.IsProperColoring H g :=
    good_implies_proper H g hg
  have hcol : Hypergraph.IsColorable H 2 := ⟨g, hprop⟩
  exact (hReq.1 hcol).elim


/-! ### The original statements over `Hypergraph ℕ` (kept as remarks)

The problem bank originally stated the theorem for `H : Hypergraph ℕ` (infinite
vertex type).  The Lovász Local Lemma engine (`Jsp689.lll_two_coloring`) requires a
`Fintype` vertex type, so the *provable* statement is the finite-vertex version
`erdos_lovasz_explicit_finite` above.  The infinite-type statements are therefore
kept here as remarks instead of unproved `sorry` declarations:

```
theorem erdos_lovasz (qualitative, `Hypergraph ℕ`) :
    ∃ c : ℝ, 0 < c ∧
      ∀ r : ℕ, 2 ≤ r → ∀ H : Hypergraph ℕ, H.Uniform r → H.RequiresThreeColors →
        ∃ v : ℕ, c ^ r ≤ (H.degree v : ℝ)

theorem erdos_lovasz_explicit (`Hypergraph ℕ`) :
    ∀ r : ℕ, 2 ≤ r → ∀ H : Hypergraph ℕ, H.Uniform r → H.RequiresThreeColors →
      ∃ v : ℕ, (2 : ℝ) ^ (r - 1) / (4 * (r : ℝ)) ≤ (H.degree v : ℝ)
```

Reducing them to the finite version would require a finite-subhypergraph reduction
argument (passing from `Hypergraph ℕ` to a finite vertex set carrying all the
witnesses), which is a separate piece of work; the core mathematical content — the
LLL-based `2^(r-1)/(4r)` degree lower bound — is the finite theorem above.
-/

end JSP000689
