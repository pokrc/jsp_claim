import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Finite.Basic

/-!
# JSP000689 helpers: a self-contained, probability-free "Lovász Local Lemma"

We prove, by pure double counting over the finite set of 2-colorings of a finite
vertex type `ι`, the special case of the Lovász Local Lemma needed for
monochromatic-edge events:

  If `E₀` is a family of `r`-subsets of `ι` (`r ≥ 2`), every edge intersects at
  most `N` other edges, and `4·(N+1)² ≤ (N+2)·2^(r-1)`, then there exists a
  2-coloring of `ι` under which no edge of `E₀` is monochromatic.

This is the engine behind the Erdős–Lovász maximum-degree lower bound
(`erdos_lovasz_explicit` in `JSP000689.lean`).

A "coloring" is a function `g : ι → Fin 2`.  An edge `e` is *monochromatic* under
`g` if all its vertices receive the same color.
-/

open scoped BigOperators
open Classical

noncomputable section

namespace Jsp689

variable {ι : Type*}

/-- Edge `e` is monochromatic under the coloring `g`. -/
def Mono (e : Finset ι) (g : ι → Fin 2) : Prop :=
  ∃ c : Fin 2, ∀ x ∈ e, g x = c

/-- A coloring is *good* w.r.t. the edge family `E` if no edge is monochromatic. -/
def Good (E : Finset (Finset ι)) (g : ι → Fin 2) : Prop :=
  ∀ e ∈ E, ¬ Mono e g

/-- A `Fintype` instance for subtypes (needed since `Fintype.subtype` is not a
typeclass instance in mathlib).  Deliberately does not depend on the chosen
`DecidablePred` instance, so that `Fintype.card {x // p x}` elaborates
identically at every use site (this makes `rw`/`simp` proofs about subtype
cardinalities instance-independent). -/
instance instSubtypeFintype {α : Type*} [Fintype α] (p : α → Prop) : Fintype {x : α // p x} := by
  classical
  exact Fintype.subtype (Finset.univ.filter p) (by simp)

section Basic

variable [Fintype ι] [DecidableEq ι]

lemma card_compl_subtype (X : Finset ι) :
    Fintype.card {x : ι // x ∉ X} = Fintype.card ι - X.card := by
  have h : Fintype.card {x : ι // x ∉ X} = (Finset.univ.filter (fun x : ι => x ∉ X)).card := by
    simpa using (Fintype.subtype_card (s := Finset.univ.filter (fun x : ι => x ∉ X))
      (p := fun x : ι => x ∉ X) (H := by intro x; simp))
  rw [h]
  rw [show Finset.univ.filter (fun x : ι => x ∉ X) = Finset.univ \ X by
    ext x
    by_cases hx : x ∈ X <;> simp [hx]]
  rw [Finset.card_sdiff_of_subset]
  · simp
  · simp

lemma card_subtype_mem (X : Finset ι) :
    Fintype.card {x : ι // x ∈ X} = X.card := by
  have h : Fintype.card {x : ι // x ∈ X} = (Finset.univ.filter (fun x : ι => x ∈ X)).card := by
    simpa using (Fintype.subtype_card (s := Finset.univ.filter (fun x : ι => x ∈ X))
      (p := fun x : ι => x ∈ X) (H := by intro x; simp))
  rw [h]
  rw [show Finset.univ.filter (fun x : ι => x ∈ X) = X by
    ext x
    simp]

lemma card_fun_two :
    Fintype.card (ι → Fin 2) = 2 ^ Fintype.card ι := by
  rw [Fintype.card_pi]
  simp

lemma card_subtype_le_card (X : Finset ι) :
    X.card ≤ Fintype.card ι := by
  have h : Fintype.card {x : ι // x ∈ X} = X.card := card_subtype_mem X
  rw [← h]
  exact Fintype.card_le_of_injective (fun x : {x : ι // x ∈ X} => x.1) (by
    intro x y hxy
    apply Subtype.ext
    exact hxy)

/-- The colorings that make the edge `e` monochromatic are in bijection with
(colorings of the complement of `e`) × (the two possible common colors). -/
def monoColorEquiv (e : Finset ι) (he : e.Nonempty) :
    {g : ι → Fin 2 // Mono e g} ≃ (({x : ι // x ∉ e} → Fin 2) × Fin 2) where
  toFun g := (fun x : {x : ι // x ∉ e} => g.1 x.1, Classical.choose g.2)
  invFun p := ⟨fun x => if hx : x ∈ e then p.2 else p.1 ⟨x, hx⟩, ⟨p.2, by
    intro x hx
    simp [hx]⟩⟩
  left_inv := by
    intro g
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ e
    · have hc := Classical.choose_spec g.2 x hx
      simp [hx, hc]
    · simp [hx]
  right_inv := by
    intro p
    rcases he with ⟨x₀, hx₀⟩
    let gp : ι → Fin 2 := fun x => if hx : x ∈ e then p.2 else p.1 ⟨x, hx⟩
    have hgp : Mono e gp := ⟨p.2, by intro x hx; simp [gp, hx]⟩
    have hspec : ∀ x ∈ e, gp x = Classical.choose hgp := Classical.choose_spec hgp
    apply Prod.ext
    · funext y
      simp [gp, y.2]
    · have hx₀' : gp x₀ = p.2 := by
        simp [gp, hx₀]
      exact (hspec x₀ hx₀).symm.trans hx₀'

/-- The number of colorings under which the edge `e` (with `e.card = r ≥ 1`) is
monochromatic is `2 ^ (n - r + 1)`. -/
lemma card_mono (e : Finset ι) (r : ℕ) (hr : 1 ≤ r) (he : e.card = r) :
    Fintype.card {g : ι → Fin 2 // Mono e g} = 2 ^ (Fintype.card ι - r + 1) := by
  have hne : e.Nonempty := by
    rw [← Finset.card_pos]
    omega
  have hc₁ : Fintype.card {x : ι // x ∉ e} = Fintype.card ι - e.card := card_compl_subtype e
  calc
    Fintype.card {g : ι → Fin 2 // Mono e g}
        = Fintype.card (({x : ι // x ∉ e} → Fin 2) × Fin 2) :=
          Fintype.card_congr (monoColorEquiv e hne)
    _ = Fintype.card ({x : ι // x ∉ e} → Fin 2) * Fintype.card (Fin 2) := by
          rw [Fintype.card_prod]
    _ = 2 ^ (Fintype.card ι - e.card) * 2 := by
      congr 1
      rw [Fintype.card_pi]
      simp [hc₁]
    _ = 2 ^ (Fintype.card ι - e.card + 1) := by
      rw [← pow_succ]
    _ = 2 ^ (Fintype.card ι - r + 1) := by rw [he]

/-- `Mono e g` depends on `g` only through the values on `e`. -/
lemma mono_determined (e : Finset ι) {g h : ι → Fin 2}
    (heq : ∀ x ∈ e, g x = h x) : Mono e g ↔ Mono e h := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, fun x hx => (heq x hx).symm.trans (hc x hx)⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, fun x hx => (heq x hx).trans (hc x hx)⟩

/-- "Good for the edges in `T`" depends on `g` only through its values on the
vertices appearing in edges of `T`. -/
lemma good_determined (T : Finset (Finset ι)) {g h : ι → Fin 2}
    (heq : ∀ x ∈ T.biUnion (fun e' => e'), g x = h x) : Good T g ↔ Good T h := by
  constructor
  · intro hg e' he'
    have hg' : ¬ Mono e' g := hg e' he'
    intro hm
    apply hg'
    have hiff := mono_determined e' (g := h) (h := g) (by
      intro x hx
      exact (heq x (Finset.mem_biUnion.mpr ⟨e', he', hx⟩)).symm)
    exact hiff.mp hm
  · intro hg e' he'
    have hg' : ¬ Mono e' h := hg e' he'
    intro hm
    apply hg'
    have hiff := mono_determined e' (g := g) (h := h) (by
      intro x hx
      exact heq x (Finset.mem_biUnion.mpr ⟨e', he', hx⟩))
    exact hiff.mp hm

lemma card_good_empty : Fintype.card {g : ι → Fin 2 // Good ∅ g} = 2 ^ Fintype.card ι := by
  calc
    Fintype.card {g : ι → Fin 2 // Good ∅ g}
        = Fintype.card {g : ι → Fin 2 // True} := by
          apply Fintype.card_congr
          exact Equiv.subtypeEquivRight (by intro g; simp [Good])
    _ = Fintype.card (ι → Fin 2) := by
      simp
    _ = 2 ^ Fintype.card ι := card_fun_two

/-- Counting by adding a conjunct: `#(p) = #(p ∧ q) + #(p ∧ ¬q)`. -/
lemma card_subtype_add (p q : (ι → Fin 2) → Prop) :
    Fintype.card {g : ι → Fin 2 // p g ∧ q g} + Fintype.card {g : ι → Fin 2 // p g ∧ ¬ q g} =
      Fintype.card {g : ι → Fin 2 // p g} := by
  have hcong : Fintype.card {g : ι → Fin 2 // p g} =
      Fintype.card (({g : ι → Fin 2 // p g ∧ q g} ⊕ {g : ι → Fin 2 // p g ∧ ¬ q g})) := by
    apply Fintype.card_congr
    refine { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
    · intro g
      by_cases h : q g.1
      · exact Sum.inl ⟨g.1, ⟨g.2, h⟩⟩
      · exact Sum.inr ⟨g.1, ⟨g.2, h⟩⟩
    · intro s
      cases s with
      | inl g => exact ⟨g.1, g.2.1⟩
      | inr g => exact ⟨g.1, g.2.1⟩
    · intro g
      by_cases h : q g.1
      · have hto : (if h' : q g.1 then Sum.inl (⟨g.1, ⟨g.2, h'⟩⟩ : {g : ι → Fin 2 // p g ∧ q g})
              else Sum.inr (⟨g.1, ⟨g.2, h'⟩⟩ : {g : ι → Fin 2 // p g ∧ ¬ q g}))
            = Sum.inl (⟨g.1, ⟨g.2, h⟩⟩ : {g : ι → Fin 2 // p g ∧ q g}) := by
          rw [dif_pos h]
        dsimp
        rw [hto]
      · have hto : (if h' : q g.1 then Sum.inl (⟨g.1, ⟨g.2, h'⟩⟩ : {g : ι → Fin 2 // p g ∧ q g})
              else Sum.inr (⟨g.1, ⟨g.2, h'⟩⟩ : {g : ι → Fin 2 // p g ∧ ¬ q g}))
            = Sum.inr (⟨g.1, ⟨g.2, h⟩⟩ : {g : ι → Fin 2 // p g ∧ ¬ q g}) := by
          rw [dif_neg h]
        dsimp
        rw [hto]
    · intro s
      cases s with
      | inl g =>
          have hto : (if h' : q g.1 then Sum.inl (⟨g.1, ⟨g.2.1, h'⟩⟩ : {g : ι → Fin 2 // p g ∧ q g})
                else Sum.inr (⟨g.1, ⟨g.2.1, h'⟩⟩ : {g : ι → Fin 2 // p g ∧ ¬ q g}))
              = Sum.inl (⟨g.1, ⟨g.2.1, g.2.2⟩⟩ : {g : ι → Fin 2 // p g ∧ q g}) := by
            rw [dif_pos g.2.2]
          dsimp
          rw [hto]
      | inr g =>
          have hto : (if h' : q g.1 then Sum.inl (⟨g.1, ⟨g.2.1, h'⟩⟩ : {g : ι → Fin 2 // p g ∧ q g})
                else Sum.inr (⟨g.1, ⟨g.2.1, h'⟩⟩ : {g : ι → Fin 2 // p g ∧ ¬ q g}))
              = Sum.inr (⟨g.1, ⟨g.2.1, g.2.2⟩⟩ : {g : ι → Fin 2 // p g ∧ ¬ q g}) := by
            rw [dif_neg g.2.2]
          dsimp
          rw [hto]
  rw [hcong, Fintype.card_sum]

/-- `Good (insert e X) g` is equivalent to "not monochromatic on `e` and good on `X`". -/
lemma good_insert (e : Finset ι) (X : Finset (Finset ι)) (g : ι → Fin 2) :
    Good (insert e X) g ↔ ¬ Mono e g ∧ Good X g := by
  simp [Good]

end Basic

section Factorization

variable [Fintype ι] [DecidableEq ι]

/-- The number of colorings whose restriction to `X` lands in `S`: each
assignment on `X` has `2^(n-|X|)` extensions. -/
lemma ncard_lift' (X : Finset ι) (S : Set ({x : ι // x ∈ X} → Fin 2)) :
    ({g : ι → Fin 2 | (fun x : {x : ι // x ∈ X} => g x.1) ∈ S} : Set (ι → Fin 2)).ncard
      = S.ncard * 2 ^ (Fintype.card ι - X.card) := by
  let T : Set (({x : ι // x ∈ X} → Fin 2) × ({x : ι // x ∉ X} → Fin 2)) := {p | p.1 ∈ S}
  have hTcard : T.ncard = S.ncard * 2 ^ (Fintype.card ι - X.card) := by
    have hTset : T = (S : Set ({x : ι // x ∈ X} → Fin 2)) ×ˢ (Set.univ : Set ({x : ι // x ∉ X} → Fin 2)) := by
      ext p
      simp [T]
    rw [hTset, Set.ncard_prod]
    congr 1
    rw [← Set.fintypeCard_eq_ncard (s := (Set.univ : Set ({x : ι // x ∉ X} → Fin 2)))]
    have hcong : Fintype.card ({x : ι // x ∉ X} → Fin 2) =
        Fintype.card ({σ : {x : ι // x ∉ X} → Fin 2 // σ ∈ (Set.univ : Set ({x : ι // x ∉ X} → Fin 2))}) := by
      apply Fintype.card_congr
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro σ
        exact ⟨σ, by simp⟩
      · intro σ
        exact σ.1
      · intro σ
        rfl
      · intro σ
        apply Subtype.ext
        rfl
    rw [← hcong]
    rw [Fintype.card_pi]
    simp
  have hcong : ({g : ι → Fin 2 | (fun x : {x : ι // x ∈ X} => g x.1) ∈ S} : Set (ι → Fin 2)).ncard = T.ncard := by
    refine Set.ncard_congr (s := ({g : ι → Fin 2 | (fun x : {x : ι // x ∈ X} => g x.1) ∈ S} : Set (ι → Fin 2))) (t := T)
      (f := fun g hg => ((fun x : {x : ι // x ∈ X} => g x.1), (fun x : {x : ι // x ∉ X} => g x.1))) ?h₁ ?h₂ ?h₃
    · intro g hg
      exact hg
    · intro g h hg hh hpair
      apply funext
      intro y
      by_cases hy : y ∈ X
      · exact congrArg (fun p : (({x : ι // x ∈ X} → Fin 2) × ({x : ι // x ∉ X} → Fin 2)) => p.1 ⟨y, hy⟩) hpair
      · exact congrArg (fun p : (({x : ι // x ∈ X} → Fin 2) × ({x : ι // x ∉ X} → Fin 2)) => p.2 ⟨y, hy⟩) hpair
    · rintro ⟨σX, σXc⟩ hσX
      let g : ι → Fin 2 := fun y => if hy : y ∈ X then σX ⟨y, hy⟩ else σXc ⟨y, hy⟩
      refine ⟨g, ?_, ?_⟩
      · have hσXS : σX ∈ S := by simpa [T] using hσX
        have hgX : (fun x : {x : ι // x ∈ X} => g x.1) = σX := by
          funext x
          simp [g]
        change (fun x : {x : ι // x ∈ X} => g x.1) ∈ S
        rw [hgX]
        exact hσXS
      · ext x
        · simp [g, x.2]
        · simp [g, x.2]
  rw [hcong, hTcard]

/-- If `PX` depends on `g` only through the restriction to `X`, then the number
of colorings satisfying `PX` is `#(assignments on X satisfying PX) × 2^(n-|X|)`. -/
lemma card_determined (X : Finset ι) (PX : (ι → Fin 2) → Prop)
    (hPX : ∀ {g h : ι → Fin 2}, (∀ x ∈ X, g x = h x) → (PX g ↔ PX h)) :
    Fintype.card {g : ι → Fin 2 // PX g}
      = Fintype.card {σ : {x : ι // x ∈ X} → Fin 2 //
          PX (fun y => if hy : y ∈ X then σ ⟨y, hy⟩ else 0)}
        * 2 ^ (Fintype.card ι - X.card) := by
  let S : Set ({x : ι // x ∈ X} → Fin 2) :=
    {σ | PX (fun y => if hy : y ∈ X then σ ⟨y, hy⟩ else 0)}
  have hconv₁ : Fintype.card {g : ι → Fin 2 // PX g} =
      ({g : ι → Fin 2 | PX g} : Set (ι → Fin 2)).ncard := by
    change Fintype.card ↑({g : ι → Fin 2 | PX g} : Set (ι → Fin 2)) =
      ({g : ι → Fin 2 | PX g} : Set (ι → Fin 2)).ncard
    rw [Set.fintypeCard_eq_ncard (s := ({g : ι → Fin 2 | PX g} : Set (ι → Fin 2)))]
  have hconv₂ : Fintype.card {σ : {x : ι // x ∈ X} → Fin 2 // σ ∈ S} =
      (S : Set ({x : ι // x ∈ X} → Fin 2)).ncard := by
    change Fintype.card ↑(S : Set ({x : ι // x ∈ X} → Fin 2)) =
      (S : Set ({x : ι // x ∈ X} → Fin 2)).ncard
    rw [Set.fintypeCard_eq_ncard (s := (S : Set ({x : ι // x ∈ X} → Fin 2)))]
  have hseteq : ({g : ι → Fin 2 | PX g} : Set (ι → Fin 2)).ncard
      = ({g : ι → Fin 2 | (fun x : {x : ι // x ∈ X} => g x.1) ∈ S} : Set (ι → Fin 2)).ncard := by
    congr 1
    ext g
    change PX g ↔ PX (fun y => if hy : y ∈ X then (fun x : {x : ι // x ∈ X} => g x.1) ⟨y, hy⟩ else 0)
    exact hPX (fun x hx => by simp [hx])
  calc
    Fintype.card {g : ι → Fin 2 // PX g}
        = ({g : ι → Fin 2 | PX g} : Set (ι → Fin 2)).ncard := hconv₁
    _ = ({g : ι → Fin 2 | (fun x : {x : ι // x ∈ X} => g x.1) ∈ S} : Set (ι → Fin 2)).ncard := hseteq
    _ = (S : Set ({x : ι // x ∈ X} → Fin 2)).ncard * 2 ^ (Fintype.card ι - X.card) := by
          rw [ncard_lift' X]
    _ = Fintype.card {σ : {x : ι // x ∈ X} → Fin 2 // σ ∈ S} * 2 ^ (Fintype.card ι - X.card) := by
          rw [hconv₂]
    _ = Fintype.card {σ : {x : ι // x ∈ X} → Fin 2 //
          PX (fun y => if hy : y ∈ X then σ ⟨y, hy⟩ else 0)} * 2 ^ (Fintype.card ι - X.card) := by
          rfl

/-- If `PX` depends only on `X` and `PY` only on `Y`, with `X ∩ Y = ∅`, then
`#(PX ∧ PY) · 2^n = #PX · #PY`. -/
lemma card_and_determined_disjoint (X Y : Finset ι) (hXY : Disjoint X Y)
    (PX : (ι → Fin 2) → Prop) (hPX : ∀ {g h : ι → Fin 2}, (∀ x ∈ X, g x = h x) → (PX g ↔ PX h))
    (PY : (ι → Fin 2) → Prop) (hPY : ∀ {g h : ι → Fin 2}, (∀ x ∈ Y, g x = h x) → (PY g ↔ PY h)) :
    Fintype.card {g : ι → Fin 2 // PX g ∧ PY g} * 2 ^ Fintype.card ι
      = Fintype.card {g : ι → Fin 2 // PX g} * Fintype.card {g : ι → Fin 2 // PY g} := by
  let W := X ∪ Y
  have hPW : ∀ {g h : ι → Fin 2}, (∀ x ∈ W, g x = h x) → (PX g ∧ PY g ↔ PX h ∧ PY h) := by
    intro g h hw
    constructor
    · intro ⟨hpx, hpy⟩
      exact ⟨(hPX (fun x hx => hw x (by simp [W, hx]))).mp hpx,
        (hPY (fun x hx => hw x (by simp [W, hx]))).mp hpy⟩
    · intro ⟨hpx, hpy⟩
      exact ⟨(hPX (fun x hx => hw x (by simp [W, hx]))).mpr hpx,
        (hPY (fun x hx => hw x (by simp [W, hx]))).mpr hpy⟩
  have hWcard : W.card = X.card + Y.card := Finset.card_union_of_disjoint hXY
  have hXW : X ⊆ W := by intro x hx; simp [W, hx]
  have hYW : Y ⊆ W := by intro x hx; simp [W, hx]
  let SX : Set ({x : ι // x ∈ X} → Fin 2) :=
    {σ | PX (fun y => if hy : y ∈ X then σ ⟨y, hy⟩ else 0)}
  let SY : Set ({x : ι // x ∈ Y} → Fin 2) :=
    {σ | PY (fun y => if hy : y ∈ Y then σ ⟨y, hy⟩ else 0)}
  let SW : Set ({x : ι // x ∈ W} → Fin 2) :=
    {σ | PX (fun y => if hy : y ∈ W then σ ⟨y, hy⟩ else 0)
         ∧ PY (fun y => if hy : y ∈ W then σ ⟨y, hy⟩ else 0)}
  have hSW : SW.ncard = SX.ncard * SY.ncard := by
    let T : Set (({x : ι // x ∈ X} → Fin 2) × ({x : ι // x ∈ Y} → Fin 2)) :=
      {p | p.1 ∈ SX ∧ p.2 ∈ SY}
    have hTcard : T.ncard = SX.ncard * SY.ncard := by
      have hTset : T = (SX : Set ({x : ι // x ∈ X} → Fin 2)) ×ˢ (SY : Set ({x : ι // x ∈ Y} → Fin 2)) := by
        ext p
        simp [T]
      rw [hTset, Set.ncard_prod]
    have hcong : SW.ncard = T.ncard := by
      refine Set.ncard_congr (s := SW) (t := T)
        (f := fun σ hσ => ((fun x : {x : ι // x ∈ X} => σ ⟨x.1, hXW x.2⟩),
          (fun x : {x : ι // x ∈ Y} => σ ⟨x.1, hYW x.2⟩))) ?h₁ ?h₂ ?h₃
      · intro σ hσ
        constructor
        · change PX (fun y => if hy : y ∈ X then (fun x : {x : ι // x ∈ X} => σ ⟨x.1, hXW x.2⟩) ⟨y, hy⟩ else 0)
          exact (hPX (fun x hx => by simp [hx, hXW hx])).mpr hσ.1
        · change PY (fun y => if hy : y ∈ Y then (fun x : {x : ι // x ∈ Y} => σ ⟨x.1, hYW x.2⟩) ⟨y, hy⟩ else 0)
          exact (hPY (fun x hx => by simp [hx, hYW hx])).mpr hσ.2
      · intro σ τ hσ hτ hpair
        apply funext
        intro x
        by_cases hx : x.1 ∈ X
        · exact congrArg (fun p : ({x : ι // x ∈ X} → Fin 2) × ({x : ι // x ∈ Y} → Fin 2) =>
            p.1 ⟨x.1, hx⟩) hpair
        · have hy : x.1 ∈ Y := (Finset.mem_union.mp x.2).resolve_left hx
          exact congrArg (fun p : ({x : ι // x ∈ X} → Fin 2) × ({x : ι // x ∈ Y} → Fin 2) =>
            p.2 ⟨x.1, hy⟩) hpair
      · rintro ⟨σX, σY⟩ ⟨hσX, hσY⟩
        let σ : {x : ι // x ∈ W} → Fin 2 := fun x =>
          if hx : x.1 ∈ X then σX ⟨x.1, hx⟩ else σY ⟨x.1, (Finset.mem_union.mp x.2).resolve_left hx⟩
        refine ⟨σ, ?_, ?_⟩
        · constructor
          · have hσXS : PX (fun y => if hy : y ∈ X then σX ⟨y, hy⟩ else 0) := by
              change σX ∈ SX
              exact hσX
            change PX (fun y => if hy : y ∈ W then σ ⟨y, hy⟩ else 0)
            exact (hPX (fun x hx => by simp [σ, hx, hXW hx])).mp hσXS
          · have hσYS : PY (fun y => if hy : y ∈ Y then σY ⟨y, hy⟩ else 0) := by
              change σY ∈ SY
              exact hσY
            change PY (fun y => if hy : y ∈ W then σ ⟨y, hy⟩ else 0)
            exact (hPY (fun x hx => by
              have hxX : x ∉ X := by
                intro hxx
                exact (Finset.disjoint_left.mp hXY) hxx hx
              simp [σ, hx, hYW hx, hxX])).mp hσYS
        · apply Prod.ext
          · funext x
            simp [σ, x.2]
          · funext x
            have hxX : x.1 ∉ X := by
              intro hx
              exact (Finset.disjoint_left.mp hXY) hx x.2
            simp [σ, hxX, x.2]
    calc
      SW.ncard = T.ncard := hcong
      _ = SX.ncard * SY.ncard := hTcard
  have hSWf : Fintype.card {σ : {x : ι // x ∈ W} → Fin 2 //
        PX (fun y => if hy : y ∈ W then σ ⟨y, hy⟩ else 0) ∧ PY (fun y => if hy : y ∈ W then σ ⟨y, hy⟩ else 0)} =
      Fintype.card {σ : {x : ι // x ∈ X} → Fin 2 //
          PX (fun y => if hy : y ∈ X then σ ⟨y, hy⟩ else 0)} *
        Fintype.card {σ : {x : ι // x ∈ Y} → Fin 2 //
          PY (fun y => if hy : y ∈ Y then σ ⟨y, hy⟩ else 0)} := by
    change Fintype.card (SW : Set ({x : ι // x ∈ W} → Fin 2)) =
      Fintype.card (SX : Set ({x : ι // x ∈ X} → Fin 2)) *
        Fintype.card (SY : Set ({x : ι // x ∈ Y} → Fin 2))
    rw [Set.fintypeCard_eq_ncard (s := SW), Set.fintypeCard_eq_ncard (s := SX),
      Set.fintypeCard_eq_ncard (s := SY)]
    exact hSW
  rw [card_determined W (fun g => PX g ∧ PY g) hPW]
  rw [card_determined X PX hPX, card_determined Y PY hPY]
  rw [hSWf]
  have hle : X.card + Y.card ≤ Fintype.card ι := by
    rw [← hWcard]
    exact card_subtype_le_card W
  have hpow2 : 2 ^ (Fintype.card ι - W.card) * 2 ^ Fintype.card ι =
      2 ^ (Fintype.card ι - X.card) * 2 ^ (Fintype.card ι - Y.card) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  calc
    (Fintype.card {σ : {x : ι // x ∈ X} → Fin 2 //
          PX (fun y => if hy : y ∈ X then σ ⟨y, hy⟩ else 0)} *
          Fintype.card {σ : {x : ι // x ∈ Y} → Fin 2 //
            PY (fun y => if hy : y ∈ Y then σ ⟨y, hy⟩ else 0)} *
        2 ^ (Fintype.card ι - W.card)) *
        2 ^ Fintype.card ι
        = Fintype.card {σ : {x : ι // x ∈ X} → Fin 2 //
              PX (fun y => if hy : y ∈ X then σ ⟨y, hy⟩ else 0)} *
            Fintype.card {σ : {x : ι // x ∈ Y} → Fin 2 //
              PY (fun y => if hy : y ∈ Y then σ ⟨y, hy⟩ else 0)} *
            (2 ^ (Fintype.card ι - W.card) * 2 ^ Fintype.card ι) := by ring
    _ = Fintype.card {σ : {x : ι // x ∈ X} → Fin 2 //
          PX (fun y => if hy : y ∈ X then σ ⟨y, hy⟩ else 0)} *
          Fintype.card {σ : {x : ι // x ∈ Y} → Fin 2 //
            PY (fun y => if hy : y ∈ Y then σ ⟨y, hy⟩ else 0)} *
          (2 ^ (Fintype.card ι - X.card) * 2 ^ (Fintype.card ι - Y.card)) := by rw [hpow2]
    _ = (Fintype.card {σ : {x : ι // x ∈ X} → Fin 2 //
          PX (fun y => if hy : y ∈ X then σ ⟨y, hy⟩ else 0)} *
          2 ^ (Fintype.card ι - X.card)) *
          (Fintype.card {σ : {x : ι // x ∈ Y} → Fin 2 //
            PY (fun y => if hy : y ∈ Y then σ ⟨y, hy⟩ else 0)} *
          2 ^ (Fintype.card ι - Y.card)) := by ring

end Factorization

section LLL

variable [Fintype ι] [DecidableEq ι]

/-- The number of colorings that are monochromatic on `e` and good on `T`. -/
abbrev JMono (e : Finset ι) (T : Finset (Finset ι)) : ℕ :=
  Fintype.card {g : ι → Fin 2 // Mono e g ∧ Good T g}

/-- The number of colorings that are good on `T`. -/
abbrev GGood (T : Finset (Finset ι)) : ℕ :=
  Fintype.card {g : ι → Fin 2 // Good T g}

/-- Adding one edge: `GGood (insert e S) ≥ (1 - x) · GGood S`, provided the
conditioning estimate holds for `e` with conditioning set `S`. -/
lemma good_step_le (e : Finset ι) (S : Finset (Finset ι)) (x : ℝ)
    (hxpos : 0 < x) (hxlt : x < 1)
    (h : (JMono e S : ℝ) ≤ x * (GGood S : ℝ)) :
    (1 - x) * (GGood S : ℝ) ≤ GGood (insert e S) := by
  have hcardS : GGood S =
      Fintype.card {g : ι → Fin 2 // Mono e g ∧ Good S g} +
        Fintype.card {g : ι → Fin 2 // ¬ Mono e g ∧ Good S g} := by
    change Fintype.card {g : ι → Fin 2 // Good S g} =
      Fintype.card {g : ι → Fin 2 // Mono e g ∧ Good S g} +
        Fintype.card {g : ι → Fin 2 // ¬ Mono e g ∧ Good S g}
    rw [← card_subtype_add (fun g => Good S g) (fun g => Mono e g)]
    congr 1
    apply Fintype.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro g
    constructor
    · intro h
      exact ⟨h.2, h.1⟩
    · intro h
      exact ⟨h.2, h.1⟩
    apply Fintype.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro g
    constructor
    · intro h
      exact ⟨h.2, h.1⟩
    · intro h
      exact ⟨h.2, h.1⟩
  have hcardI : GGood (insert e S) =
      Fintype.card {g : ι → Fin 2 // ¬ Mono e g ∧ Good S g} := by
    apply Fintype.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro g
    exact good_insert e S g
  rw [hcardI]
  have hdec : (Fintype.card {g : ι → Fin 2 // ¬ Mono e g ∧ Good S g} : ℝ) =
      (GGood S : ℝ) - (JMono e S : ℝ) := by
    have hc : ((GGood S : ℕ) : ℝ) =
        ((Fintype.card {g : ι → Fin 2 // Mono e g ∧ Good S g} : ℕ) : ℝ) +
          ((Fintype.card {g : ι → Fin 2 // ¬ Mono e g ∧ Good S g} : ℕ) : ℝ) := by
      exact_mod_cast hcardS
    linarith
  rw [hdec]
  nlinarith [h, hxpos]

/-- The conditioning estimate of the Lovász Local Lemma for monochromatic-edge
events, proved by pure double counting (strong induction on the size of the
conditioning edge set `T`).  For every edge `e ∈ E₀` and every set `T ⊆ E₀` of
edges with `e ∉ T`, at most an `x`-fraction of the colorings that are good on
`T` are monochromatic on `e`. -/
lemma lll_cond (E₀ : Finset (Finset ι)) (N : ℕ) (x : ℝ)
    (hxpos : 0 < x) (hxlt : x < 1)
    (hlll : ∀ e ∈ E₀,
      (Fintype.card {g : ι → Fin 2 // Mono e g} : ℝ) ≤ x * (1 - x) ^ N * (2 : ℝ) ^ Fintype.card ι)
    (hdep : ∀ e ∈ E₀,
      (E₀.filter (fun e' => e' ≠ e ∧ (e ∩ e').Nonempty)).card ≤ N) :
    ∀ e ∈ E₀, ∀ T : Finset (Finset ι), T ⊆ E₀ → e ∉ T →
      (JMono e T : ℝ) ≤ x * (GGood T : ℝ) := by
  classical
  have hxle1 : (0 : ℝ) ≤ 1 - x := sub_nonneg.mpr (le_of_lt hxlt)
  have hx₀ : (0 : ℝ) ≤ x := le_of_lt hxpos
  let P : ℕ → Prop := fun n =>
    ∀ e ∈ E₀, ∀ T : Finset (Finset ι), T ⊆ E₀ → T.card = n → e ∉ T →
      (JMono e T : ℝ) ≤ x * (GGood T : ℝ)
  have hP : ∀ n, (∀ m, m < n → P m) → P n := by
    intro n ih e heE T hT hcard heT
    let T₁ := T.filter (fun e' => (e ∩ e').Nonempty)
    let T₂ := T.filter (fun e' => ¬ (e ∩ e').Nonempty)
    have hT₁₂ : T = T₁ ∪ T₂ := by
      ext e'
      constructor
      · intro he'
        by_cases h : (e ∩ e').Nonempty
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨he', h⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨he', h⟩))
      · intro he'
        rcases Finset.mem_union.mp he' with he₁ | he₂
        · exact (Finset.mem_filter.mp he₁).1
        · exact (Finset.mem_filter.mp he₂).1
    have hT₁₂disj : T₁ ∩ T₂ = ∅ := by
      ext e'
      constructor
      · intro he'
        have h₁ := (Finset.mem_filter.mp (Finset.mem_inter.mp he').1).2
        have h₂ := (Finset.mem_filter.mp (Finset.mem_inter.mp he').2).2
        exact (h₂ h₁).elim
      · intro he'
        simp at he' 
    have hT₂sub : T₂ ⊆ T := Finset.filter_subset _ _
    have hT₁sub : T₁ ⊆ T := Finset.filter_subset _ _
    have hT₂subE : T₂ ⊆ E₀ := subset_trans hT₂sub hT
    have hT₁subE : T₁ ⊆ E₀ := subset_trans hT₁sub hT
    have hT₁card : T₁.card ≤ N := by
      have hsub : T₁ ⊆ E₀.filter (fun e' => e' ≠ e ∧ (e ∩ e').Nonempty) := by
        intro e' he'
        have he'T : e' ∈ T := hT₁sub he'
        have hne : (e ∩ e').Nonempty := (Finset.mem_filter.mp he').2
        exact Finset.mem_filter.mpr ⟨hT he'T, ⟨by
          intro heq
          apply heT
          simpa [heq] using he'T, hne⟩⟩
      exact le_trans (Finset.card_le_card hsub) (hdep e heE)
    -- U := union of the edges in T₂; disjoint from e
    let U := T₂.biUnion (fun e' => e')
    have hdisj : Disjoint e U := by
      rw [Finset.disjoint_left]
      intro x hx hxU
      rcases Finset.mem_biUnion.mp hxU with ⟨e', he'T₂, hxe'⟩
      have hne : ¬ (e ∩ e').Nonempty := (Finset.mem_filter.mp he'T₂).2
      have hempty : e ∩ e' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hmem : x ∈ e ∩ e' := Finset.mem_inter.mpr ⟨hx, hxe'⟩
      rw [hempty] at hmem
      simp at hmem
    -- factorization: joint = mono · good / 2^n
    have hfac : Fintype.card {g : ι → Fin 2 // Mono e g ∧ Good T₂ g} * 2 ^ Fintype.card ι =
        Fintype.card {g : ι → Fin 2 // Mono e g} * Fintype.card {g : ι → Fin 2 // Good T₂ g} := by
      exact card_and_determined_disjoint e U hdisj (fun g => Mono e g) (by
        intro g h gh; exact mono_determined e gh) (fun g => Good T₂ g) (by
        intro g h gh; exact good_determined T₂ gh)
    -- joint upper bound (on T₂)
    have hjoint : (Fintype.card {g : ι → Fin 2 // Mono e g ∧ Good T₂ g} : ℝ) ≤
        x * (1 - x) ^ N * (GGood T₂ : ℝ) := by
      have h₂ : (Fintype.card {g : ι → Fin 2 // Mono e g} : ℝ) *
            (GGood T₂ : ℝ) ≤
          x * (1 - x) ^ N * (2 : ℝ) ^ Fintype.card ι * (GGood T₂ : ℝ) := by
        exact mul_le_mul_of_nonneg_right (hlll e heE) (by positivity)
      have h₃ : (Fintype.card {g : ι → Fin 2 // Mono e g ∧ Good T₂ g} : ℝ) *
            (2 : ℝ) ^ Fintype.card ι ≤
          x * (1 - x) ^ N * (2 : ℝ) ^ Fintype.card ι * (GGood T₂ : ℝ) := by
        rw [show (Fintype.card {g : ι → Fin 2 // Mono e g ∧ Good T₂ g} : ℝ) *
                (2 : ℝ) ^ Fintype.card ι =
              (Fintype.card {g : ι → Fin 2 // Mono e g} : ℝ) *
                (Fintype.card {g : ι → Fin 2 // Good T₂ g} : ℝ) by
          exact_mod_cast hfac]
        exact h₂
      have hpow : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι := pow_pos (by norm_num) _
      have h₃' : (Fintype.card {g : ι → Fin 2 // Mono e g ∧ Good T₂ g} : ℝ) *
            (2 : ℝ) ^ Fintype.card ι ≤
          (x * (1 - x) ^ N * (GGood T₂ : ℝ)) * (2 : ℝ) ^ Fintype.card ι := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using h₃
      exact le_of_mul_le_mul_right h₃' hpow
    -- good(T₁ ∪ T₂) ≥ (1-x)^{|T₁|} · good(T₂), by induction on T₁
    have hgood : ((1 - x) ^ T₁.card : ℝ) * (GGood T₂ : ℝ) ≤ GGood (T₁ ∪ T₂) := by
      refine (Finset.induction_on (s := T₁)
        (motive := fun U : Finset (Finset ι) => U ⊆ T₁ →
          ((1 - x) ^ U.card : ℝ) * (GGood T₂ : ℝ) ≤ GGood (U ∪ T₂)) ?base ?step) (by
          intro x hx
          exact hx)
      · intro hsub
        simp [GGood]
      · intro e' S he'S ihg hsub
        -- hsub : insert e' S ⊆ T₁;  ihg : S ⊆ T₁ → (1-x)^{|S|}·GGood T₂ ≤ GGood (S ∪ T₂)
        have he'T₁ : e' ∈ T₁ := hsub (Finset.mem_insert_self e' S)
        have hSsub : S ⊆ T₁ := fun x hx => hsub (Finset.mem_insert_of_mem hx)
        have hlll_e' : (JMono e' (S ∪ T₂) : ℝ) ≤ x * (GGood (S ∪ T₂) : ℝ) := by
          have he'E₀ : e' ∈ E₀ := hT₁subE he'T₁
          have hsub' : S ∪ T₂ ⊆ E₀ := by
            intro e'' he''
            rcases Finset.mem_union.mp he'' with he''S | he''T₂
            · exact hT₁subE (hSsub he''S)
            · exact hT₂subE he''T₂
          have hne' : e' ∉ S ∪ T₂ := by
            intro h
            rcases Finset.mem_union.mp h with hS | hT₂'
            · exact he'S hS
            · have h₁ : (e ∩ e').Nonempty := (Finset.mem_filter.mp he'T₁).2
              exact (Finset.mem_filter.mp hT₂').2 h₁
          have hlt : (S ∪ T₂).card < n := by
            have hStr : S ⊂ T₁ := by
              refine ⟨hSsub, ?_⟩
              intro hSall
              exact he'S (hSall he'T₁)
            have hcard1 : T.card = T₁.card + T₂.card := by
              rw [hT₁₂]
              exact Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr hT₁₂disj)
            have hS₂ : (S ∪ T₂).card = S.card + T₂.card := by
              apply Finset.card_union_of_disjoint
              rw [Finset.disjoint_iff_inter_eq_empty]
              ext x
              constructor
              · intro hx
                have hxT₁ : x ∈ T₁ := hSsub (Finset.mem_inter.mp hx).1
                have hxT₂ : x ∈ T₂ := (Finset.mem_inter.mp hx).2
                have hp := (Finset.mem_filter.mp hxT₁).2
                have hn := (Finset.mem_filter.mp hxT₂).2
                exact (hn hp).elim
              · intro hx
                simp at hx
            have hSlt : S.card < T₁.card := Finset.card_lt_card hStr
            rw [← hcard, hcard1, hS₂]
            omega
          exact ih (S ∪ T₂).card hlt e' he'E₀ (S ∪ T₂) hsub' rfl hne'
        have hstep : (1 - x) * (GGood (S ∪ T₂) : ℝ) ≤ GGood (insert e' S ∪ T₂) := by
          rw [show insert e' S ∪ T₂ = insert e' (S ∪ T₂) by simp [Finset.insert_union]]
          exact good_step_le e' (S ∪ T₂) x hxpos hxlt hlll_e'
        calc
          (1 - x) ^ (insert e' S).card * (GGood T₂ : ℝ)
              = (1 - x) ^ (S.card + 1) * (GGood T₂ : ℝ) := by
                rw [Finset.card_insert_of_notMem he'S]
          _ = (1 - x) * ((1 - x) ^ S.card * (GGood T₂ : ℝ)) := by
                rw [pow_succ]
                ring
          _ ≤ (1 - x) * (GGood (S ∪ T₂) : ℝ) := by
                exact mul_le_mul_of_nonneg_left (ihg hSsub) hxle1
          _ ≤ GGood (insert e' S ∪ T₂) := hstep
    -- combine everything
    have hleJ : Fintype.card {g : ι → Fin 2 // Mono e g ∧ Good T g} ≤
        Fintype.card {g : ι → Fin 2 // Mono e g ∧ Good T₂ g} := by
      exact Fintype.card_le_of_injective (fun g : {g : ι → Fin 2 // Mono e g ∧ Good T g} =>
        ⟨g.1, g.2.1, by
          intro e' he'
          exact g.2.2 e' (hT₂sub he')⟩) (by
        intro g h hgh
        apply Subtype.ext
        simpa using congrArg Subtype.val hgh)
    have hgoodT : ((1 - x) ^ T₁.card : ℝ) * (GGood T₂ : ℝ) ≤ (GGood T : ℝ) := by
      rw [hT₁₂]
      exact hgood
    have hA : x * (1 - x) ^ N * (GGood T₂ : ℝ) ≤
        x * (1 - x) ^ (N - T₁.card) * (GGood T : ℝ) := by
      have hmul : x * (1 - x) ^ (N - T₁.card) * ((1 - x) ^ T₁.card * (GGood T₂ : ℝ)) ≤
          x * (1 - x) ^ (N - T₁.card) * (GGood T : ℝ) := by
        exact mul_le_mul_of_nonneg_left hgoodT (mul_nonneg hx₀ (pow_nonneg hxle1 _))
      have hpow : (1 - x) ^ (N - T₁.card) * (1 - x) ^ T₁.card = (1 - x) ^ N := by
        rw [← pow_add, Nat.sub_add_cancel hT₁card]
      have hpow' : x * (1 - x) ^ (N - T₁.card) * ((1 - x) ^ T₁.card * (GGood T₂ : ℝ)) =
          x * (1 - x) ^ N * (GGood T₂ : ℝ) := by
        calc
          x * (1 - x) ^ (N - T₁.card) * ((1 - x) ^ T₁.card * (GGood T₂ : ℝ))
              = x * ((1 - x) ^ (N - T₁.card) * (1 - x) ^ T₁.card) * (GGood T₂ : ℝ) := by ring
          _ = x * (1 - x) ^ N * (GGood T₂ : ℝ) := by rw [hpow]
      rwa [hpow'] at hmul
    have hB : x * (1 - x) ^ (N - T₁.card) * (GGood T : ℝ) ≤ x * (GGood T : ℝ) := by
      have hp : (1 - x) ^ (N - T₁.card) ≤ 1 := pow_le_one₀ hxle1 (by nlinarith [hx₀])
      have h₁ : x * (1 - x) ^ (N - T₁.card) * (GGood T : ℝ) ≤ x * 1 * (GGood T : ℝ) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hp (by positivity : (0 : ℝ) ≤ GGood T)) hx₀)
      nlinarith
    calc
      ((Fintype.card {g : ι → Fin 2 // Mono e g ∧ Good T g} : ℕ) : ℝ) ≤
          (Fintype.card {g : ι → Fin 2 // Mono e g ∧ Good T₂ g} : ℝ) := by
        exact_mod_cast hleJ
      _ ≤ x * (1 - x) ^ N * (GGood T₂ : ℝ) := hjoint
      _ ≤ x * (1 - x) ^ (N - T₁.card) * (GGood T : ℝ) := hA
      _ ≤ x * (GGood T : ℝ) := hB
  intro e heE T hT heT
  exact (show P T.card from Nat.strong_induction_on T.card hP) e heE T hT rfl heT

/-- The Bernoulli-based sufficient condition for the Lovász Local Lemma:
`2^(r-1) · x · (1-x)^N ≥ 1` for `x = 1/(2(N+1))`, under
`4·(N+1)² ≤ (N+2)·2^(r-1)`. -/
lemma lll_condition_bound (N r : ℕ) (hr : 2 ≤ r)
    (hcond : 4 * ((N + 1 : ℕ) : ℝ) ^ 2 ≤ ((N + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (r - 1)) :
    (1 : ℝ) ≤ (2 : ℝ) ^ (r - 1) * (1 / (2 * ((N + 1 : ℕ) : ℝ))) *
      (1 - 1 / (2 * ((N + 1 : ℕ) : ℝ))) ^ N := by
  let x : ℝ := 1 / (2 * ((N + 1 : ℕ) : ℝ))
  have hxpos : 0 < x := by
    dsimp [x]
    exact div_pos one_pos (mul_pos (by norm_num) (by exact_mod_cast (Nat.succ_pos N)))
  have hxle2 : x ≤ 2 := by
    dsimp [x]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [show (1 : ℝ) ≤ (N + 1 : ℕ) by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le N))]
  have hbern : 1 - N * x ≤ (1 - x) ^ N := by
    have h₂ : (-2 : ℝ) ≤ -x := by linarith
    simpa [x, sub_eq_add_neg] using one_add_mul_le_pow (a := -x) h₂ N
  have hmul : x * (1 - N * x) ≤ x * (1 - x) ^ N :=
    mul_le_mul_of_nonneg_left hbern hxpos.le
  have hxeq : x * (1 - N * x) = ((N + 2 : ℕ) : ℝ) / (4 * ((N + 1 : ℕ) : ℝ) ^ 2) := by
    dsimp [x]
    field_simp
    push_cast
    ring
  have h₁ : (1 : ℝ) ≤ (2 : ℝ) ^ (r - 1) * (((N + 2 : ℕ) : ℝ) / (4 * ((N + 1 : ℕ) : ℝ) ^ 2)) := by
    have hd : (0 : ℝ) < 4 * ((N + 1 : ℕ) : ℝ) ^ 2 := by positivity
    rw [show (2 : ℝ) ^ (r - 1) * (((N + 2 : ℕ) : ℝ) / (4 * ((N + 1 : ℕ) : ℝ) ^ 2)) =
        ((N + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (r - 1) / (4 * ((N + 1 : ℕ) : ℝ) ^ 2) by ring]
    exact (le_div_iff₀ hd).mpr (by
      rw [mul_comm]
      simpa using hcond)
  calc
    (1 : ℝ) ≤ (2 : ℝ) ^ (r - 1) * (((N + 2 : ℕ) : ℝ) / (4 * ((N + 1 : ℕ) : ℝ) ^ 2)) := h₁
    _ = (2 : ℝ) ^ (r - 1) * (x * (1 - N * x)) := by rw [hxeq]
    _ ≤ (2 : ℝ) ^ (r - 1) * (x * (1 - x) ^ N) := by
      exact mul_le_mul_of_nonneg_left hmul (pow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (r - 1) * x * (1 - x) ^ N := by ring
    _ = (2 : ℝ) ^ (r - 1) * (1 / (2 * ((N + 1 : ℕ) : ℝ))) *
        (1 - 1 / (2 * ((N + 1 : ℕ) : ℝ))) ^ N := by rfl

/-- The Lovász Local Lemma for monochromatic-edge events: if every edge
intersects at most `N` other edges and `4·(N+1)² ≤ (N+2)·2^(r-1)`, then there is
a 2-coloring of `ι` under which no edge of `E₀` is monochromatic. -/
lemma lll_two_coloring [Fintype ι] [DecidableEq ι] (E₀ : Finset (Finset ι))
    (r N : ℕ) (hr : 2 ≤ r)
    (hcard : ∀ e ∈ E₀, e.card = r)
    (hdep : ∀ e ∈ E₀, (E₀.filter (fun e' => e' ≠ e ∧ (e ∩ e').Nonempty)).card ≤ N)
    (hcond : 4 * ((N + 1 : ℕ) : ℝ) ^ 2 ≤ ((N + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (r - 1)) :
    ∃ g : ι → Fin 2, Good E₀ g := by
  classical
  let x : ℝ := 1 / (2 * ((N + 1 : ℕ) : ℝ))
  have hxpos : 0 < x := by
    dsimp [x]
    exact div_pos one_pos (mul_pos (by norm_num) (by exact_mod_cast (Nat.succ_pos N)))
  have hxlt : x < 1 := by
    dsimp [x]
    rw [div_lt_one (by positivity)]
    nlinarith [show (1 : ℝ) ≤ (N + 1 : ℕ) by exact_mod_cast (Nat.succ_le_iff.mpr (Nat.succ_pos N))]
  have hlll : ∀ e ∈ E₀,
      (Fintype.card {g : ι → Fin 2 // Mono e g} : ℝ) ≤ x * (1 - x) ^ N * (2 : ℝ) ^ Fintype.card ι := by
    intro e he
    rw [card_mono e r (by omega) (hcard e he)]
    rw [Nat.cast_pow]
    have hn : r ≤ Fintype.card ι := by
      rw [← hcard e he]
      exact card_subtype_le_card e
    have hb := lll_condition_bound N r hr hcond
    have hp : (0 : ℝ) < (2 : ℝ) ^ (Fintype.card ι - r + 1) := pow_pos (by norm_num) _
    have h₄ : (2 : ℝ) ^ (Fintype.card ι - r + 1) ≤
        (2 : ℝ) ^ (r - 1) * x * (1 - x) ^ N * (2 : ℝ) ^ (Fintype.card ι - r + 1) := by
      simpa [x] using mul_le_mul_of_nonneg_right hb (le_of_lt hp)
    calc
      (2 : ℝ) ^ (Fintype.card ι - r + 1)
          ≤ (2 : ℝ) ^ (r - 1) * x * (1 - x) ^ N * (2 : ℝ) ^ (Fintype.card ι - r + 1) := h₄
      _ = x * (1 - x) ^ N * ((2 : ℝ) ^ (r - 1) * (2 : ℝ) ^ (Fintype.card ι - r + 1)) := by ring
      _ = x * (1 - x) ^ N * (2 : ℝ) ^ Fintype.card ι := by
        congr 1
        rw [← pow_add]
        congr 1
        omega
  have hcond' : ∀ e ∈ E₀, ∀ T : Finset (Finset ι), T ⊆ E₀ → e ∉ T →
      (JMono e T : ℝ) ≤ x * (GGood T : ℝ) :=
    lll_cond E₀ N x hxpos hxlt hlll hdep
  -- GGood E₀ > 0 by the product bound
  have hG : ((1 - x) ^ E₀.card : ℝ) * (2 : ℝ) ^ Fintype.card ι ≤ (GGood E₀ : ℝ) := by
    refine (Finset.induction_on (s := E₀)
      (motive := fun U : Finset (Finset ι) => U ⊆ E₀ →
        ((1 - x) ^ U.card : ℝ) * (2 : ℝ) ^ Fintype.card ι ≤ GGood U) ?base ?step) (by
        intro x hx
        exact hx)
    · intro hsub
      simp [GGood, card_good_empty]
    · intro e S heS ih hsub
      have heE : e ∈ E₀ := hsub (Finset.mem_insert_self e S)
      have hSsub : S ⊆ E₀ := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      have hc : (JMono e S : ℝ) ≤ x * (GGood S : ℝ) := by
        exact hcond' e heE S hSsub heS
      have hstep : (1 - x) * (GGood S : ℝ) ≤ GGood (insert e S) :=
        good_step_le e S x hxpos hxlt hc
      calc
        (1 - x) ^ (insert e S).card * (2 : ℝ) ^ Fintype.card ι
            = (1 - x) ^ (S.card + 1) * (2 : ℝ) ^ Fintype.card ι := by
              rw [Finset.card_insert_of_notMem heS]
        _ = (1 - x) * ((1 - x) ^ S.card * (2 : ℝ) ^ Fintype.card ι) := by
              rw [pow_succ]
              ring
        _ ≤ (1 - x) * (GGood S : ℝ) := by
              exact mul_le_mul_of_nonneg_left (ih hSsub) (sub_nonneg.mpr (le_of_lt hxlt))
        _ ≤ GGood (insert e S) := hstep
  have hpos : (0 : ℝ) < GGood E₀ := by
    have hpow : (0 : ℝ) < (1 - x) ^ E₀.card * (2 : ℝ) ^ Fintype.card ι := by
      positivity
    exact lt_of_lt_of_le hpow hG
  have hcardpos : 0 < Fintype.card {g : ι → Fin 2 // Good E₀ g} := by
    exact_mod_cast hpos
  have hne : (Finset.univ : Finset {g : ι → Fin 2 // Good E₀ g}).Nonempty := by
    rw [← Finset.card_pos]
    simpa using hcardpos
  rcases hne with ⟨g, hg⟩
  exact ⟨g.1, g.2⟩

end LLL

end Jsp689