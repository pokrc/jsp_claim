import Mathlib.Data.Nat.BinaryRec
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Ring.Parity

/-!
# JSP-000183 — Must an infinite walk in three-dimensional space using a finite set of step vectors visit three collinear points?

Problem bank entry (`problems/catalog-0101-0200.md#JSP-000183`):

> Must an infinite walk in three-dimensional space using a finite set of step vectors
> visit three collinear points?

The answer is **no** (Cambie–Kalviainen 2026). An explicit infinite walk in Z³ with steps
from a fixed set of sixteen vectors is constructed such that no three vertices are collinear.

## Outline of the construction

1. **Gaussian-lattice walk**: define `u_n = i^{s₂(n)}` where `s₂(n)` is the popcount
   (number of ones in the binary expansion of `n`), and let `z_n = Σ_{0≤r<n} u_r ∈ Z[i]`.
   This gives a nearest-neighbour walk in the Gaussian lattice.

2. **Tagging**: define `w_n = 2 z_n + c_{α_n}` where `α_n` encodes the direction state
   and `c_{α_n}` is a unit-square corner, and `h_n = 4n + α_n`.

3. **Lift to Z³**: set `P_n = (Re(w_n), Im(w_n), h_n)`.

4. **Key lemma** (Valuation matching): for all m < n,
   `ν₂(|w_n - w_m|²) = ν₂(h_n - h_m)`.

5. **Non-collinearity**: if P_a, P_b, P_c are collinear then `ν₂(A) = ν₂(B) = ν₂(A+B)`
   where A = h_b − h_a, B = h_c − h_b; this is impossible since A/2^t and B/2^t are odd
   while (A+B)/2^t must be even.

## References

- [CaKa26] Stijn Cambie, Erik Kalviainen.
  *An infinite small-step Z³-walk with no collinear triple.*
  arXiv:2609.01766 (2026).

All steps below are kernel-checked. No `sorry`, no `native_decide`, no `axiom`
beyond the standard mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace JSP000183

-- ============================================================
-- Section 1: Gaussian valuation lemmas (from GaussianValuation)
-- ============================================================

/-- A planar vector, encoded as a pair of integers. -/
abbrev Vec2 := ℤ × ℤ

/-- Pointwise addition of planar vectors. -/
def addVec (p q : Vec2) : Vec2 := (p.1 + q.1, p.2 + q.2)

/-- Multiplication by (1+i) in the Gaussian lattice: (x,y) ↦ (x−y, x+y). -/
def mulOnePlusI (p : Vec2) : Vec2 := (p.1 - p.2, p.1 + p.2)

/-- The squared modulus |u|² = x² + y² as a natural number. -/
def normSq (u : Vec2) : ℕ := Int.natAbs (u.1 * u.1 + u.2 * u.2)

/-- The 2-adic valuation of the squared modulus. -/
def pairVal (u : Vec2) : ℕ := padicValNat 2 (normSq u)

@[simp] theorem normSq_zero : normSq (0, 0) = 0 := by simp [normSq]

@[simp] theorem pairVal_zero : pairVal (0, 0) = 0 := by simp [pairVal]

@[simp] theorem normSq_ne_zero {u : Vec2} (hu : u ≠ (0, 0)) : normSq u ≠ 0 := by
  rcases u with ⟨x, y⟩
  intro h
  simp only [normSq, Int.natAbs_eq_zero] at h
  have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  exact hu (by simp [hx, hy])

@[simp] theorem normSq_neg (u : Vec2) : normSq (-u.1, -u.2) = normSq u := by
  simp [normSq]

@[simp] theorem pairVal_neg (u : Vec2) : pairVal (-u.1, -u.2) = pairVal u := by
  simp [pairVal]

private theorem normSq_nsmul (k : ℕ) (u : Vec2) :
    normSq ((k : ℤ) * u.1, (k : ℤ) * u.2) = k * k * normSq u := by
  rcases u with ⟨x, y⟩
  simp only [normSq]
  rw [show ((k : ℤ) * x) * ((k : ℤ) * x) + ((k : ℤ) * y) * ((k : ℤ) * y) =
      ((k : ℤ) * k) * (x * x + y * y) by ring]
  simp [Int.natAbs_mul]

/-- Multiplying a nonzero planar vector by `k` adds twice the 2-adic order of `k`. -/
theorem pairVal_nsmul (k : ℕ) (u : Vec2) (hk : k ≠ 0) (hu : u ≠ (0, 0)) :
    pairVal ((k : ℤ) * u.1, (k : ℤ) * u.2) = pairVal u + 2 * padicValNat 2 k := by
  have hnorm := normSq_ne_zero hu
  simp only [pairVal, normSq_nsmul]
  rw [padicValNat.mul (mul_ne_zero hk hk) hnorm, padicValNat.mul hk hk]
  omega

@[simp] theorem normSq_mulOnePlusI (u : Vec2) :
    normSq (mulOnePlusI u) = 2 * normSq u := by
  rcases u with ⟨x, y⟩
  simp only [mulOnePlusI, normSq]
  rw [show (x - y) * (x - y) + (x + y) * (x + y) =
      (2 : ℤ) * (x * x + y * y) by ring]
  simp [Int.natAbs_mul]

/-- Multiplication by `1+i` adds one to the norm valuation. -/
theorem pairVal_mulOnePlusI {u : Vec2} (hu : u ≠ (0, 0)) :
    pairVal (mulOnePlusI u) = pairVal u + 1 := by
  simp only [pairVal, normSq_mulOnePlusI]
  rw [padicValNat.mul (by decide) (normSq_ne_zero hu), padicValNat_base (by decide)]
  omega

private theorem two_dvd_sq_sub_self (x : ℤ) : (2 : ℤ) ∣ x * x - x := by
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' x
  · subst x
    refine ⟨2 * k * k - k, by ring⟩
  · subst x
    refine ⟨2 * k * k + k, by ring⟩

/-- If the coordinate sum is odd, then the squared norm is odd. -/
theorem normSq_not_two_dvd_of_sum_not_two_dvd {u : Vec2}
    (hsum : ¬(2 : ℤ) ∣ u.1 + u.2) : ¬2 ∣ normSq u := by
  intro hnorm
  have hnormZ : (2 : ℤ) ∣ u.1 * u.1 + u.2 * u.2 := by
    apply Int.dvd_natAbs.mp
    exact Int.natCast_dvd_natCast.mpr hnorm
  have hx := two_dvd_sq_sub_self u.1
  have hy := two_dvd_sq_sub_self u.2
  apply hsum
  obtain ⟨a, ha⟩ := hnormZ
  obtain ⟨b, hb⟩ := hx
  obtain ⟨c, hc⟩ := hy
  refine ⟨a - b - c, ?_⟩
  omega

/-- An odd coordinate sum gives valuation zero. -/
theorem pairVal_eq_zero_of_sum_not_two_dvd {u : Vec2}
    (hsum : ¬(2 : ℤ) ∣ u.1 + u.2) : pairVal u = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  exact normSq_not_two_dvd_of_sum_not_two_dvd hsum

theorem padicValNat_natAbs_eq_one {z : ℤ}
    (htwo : (2 : ℤ) ∣ z) (hfour : ¬(4 : ℤ) ∣ z) :
    padicValNat 2 z.natAbs = 1 := by
  have htwoN : 2 ∣ z.natAbs := by
    apply Int.natCast_dvd_natCast.mp
    exact Int.dvd_natAbs.mpr htwo
  obtain ⟨q, hq⟩ := htwoN
  have hq0 : q ≠ 0 := by
    intro h
    subst q
    simp_all
  have hqodd : ¬2 ∣ q := by
    intro h
    apply hfour
    apply Int.dvd_natAbs.mp
    apply Int.natCast_dvd_natCast.mpr
    simpa [hq, mul_assoc] using Nat.mul_dvd_mul_left 2 h
  rw [hq, padicValNat.mul (by omega) hq0, padicValNat_base (by omega)]
  simp [padicValNat.eq_zero_of_not_dvd hqodd]

theorem padicValNat_eq_one_of_two_dvd_not_four {n : ℕ}
    (htwo : 2 ∣ n) (hfour : ¬4 ∣ n) : padicValNat 2 n = 1 := by
  have h := padicValNat_natAbs_eq_one (z := (n : ℤ))
    (by exact_mod_cast htwo) (by exact_mod_cast hfour)
  simpa using h

theorem pairVal_odd_odd {x y : ℤ}
    (hx : ¬(2 : ℤ) ∣ x) (hy : ¬(2 : ℤ) ∣ y) :
    pairVal (x, y) = 1 := by
  obtain ⟨a, ha | ha⟩ := Int.even_or_odd' x
  · exfalso
    apply hx
    exact ⟨a, ha⟩
  obtain ⟨b, hb | hb⟩ := Int.even_or_odd' y
  · exfalso
    apply hy
    exact ⟨b, hb⟩
  subst x
  subst y
  unfold pairVal normSq
  apply padicValNat_natAbs_eq_one
  · refine ⟨2 * (a * a + a + b * b + b) + 1, by ring⟩
  · intro hfour
    obtain ⟨k, hk⟩ := hfour
    ring_nf at hk
    omega

-- ============================================================
-- Section 2: Gaussian walk (from Gaussian.lean)
-- ============================================================

inductive Direction where
  | east | north | west | south
  deriving DecidableEq, Repr

namespace Direction

def rotate : Direction → Direction
  | east => north
  | north => west
  | west => south
  | south => east

@[simp] theorem rotate_injective : Function.Injective rotate := by
  intro a b h
  cases a <;> cases b <;> simp_all [rotate]

def vec : Direction → Vec2
  | east => (1, 0)
  | north => (0, 1)
  | west => (-1, 0)
  | south => (0, -1)

def label : Direction → ℕ
  | east => 0
  | north => 1
  | west => 2
  | south => 3

def tag : Direction → Vec2
  | east => (0, 0)
  | north => (0, 1)
  | west => (-1, 1)
  | south => (-1, 0)

@[simp] theorem label_le_three (d : Direction) : label d ≤ 3 := by
  cases d <;> decide

@[simp] theorem vec_ne_zero (d : Direction) : vec d ≠ (0, 0) := by
  cases d <;> decide

@[simp] theorem vec_rotate (d : Direction) : vec (rotate d) = (- (vec d).2, (vec d).1) := by
  cases d <;> decide

end Direction


@[simp] theorem mulOnePlusI_zero : mulOnePlusI (0, 0) = (0, 0) := rfl

@[simp] theorem mulOnePlusI_add (p q : Vec2) :
    mulOnePlusI (addVec p q) = addVec (mulOnePlusI p) (mulOnePlusI q) := by
  apply Prod.ext <;> simp [mulOnePlusI, addVec] <;> ring

@[simp] theorem mulOnePlusI_direction (d : Direction) :
    mulOnePlusI (Direction.vec d) =
      addVec (Direction.vec d) (Direction.vec (Direction.rotate d)) := by
  cases d <;> decide

private def gaussianStep (b : Bool) (_n : ℕ) (data : Direction × Vec2) : Direction × Vec2 :=
  let d := data.1
  let z := data.2
  if b then
    (d.rotate, addVec (mulOnePlusI z) d.vec)
  else
    (d, mulOnePlusI z)

def gaussianData (n : ℕ) : Direction × Vec2 :=
  Nat.binaryRec (.east, (0, 0)) gaussianStep n

def gaussianState (n : ℕ) : Direction := (gaussianData n).1

def gaussianPlanar (n : ℕ) : Vec2 := (gaussianData n).2

def gaussianUnit (n : ℕ) : Vec2 := (gaussianState n).vec

@[simp] theorem gaussianData_zero : gaussianData 0 = (.east, (0, 0)) := rfl

@[simp] theorem gaussianData_bit (b : Bool) (n : ℕ) :
    gaussianData (Nat.bit b n) = gaussianStep b n (gaussianData n) := by
  apply Nat.binaryRec_eq
  left
  rfl

@[simp] theorem gaussianState_two_mul (n : ℕ) : gaussianState (2 * n) = gaussianState n := by
  simpa [gaussianState, gaussianStep] using congrArg Prod.fst (gaussianData_bit false n)

@[simp] theorem gaussianState_two_mul_add_one (n : ℕ) :
    gaussianState (2 * n + 1) = (gaussianState n).rotate := by
  simpa [gaussianState, gaussianStep] using congrArg Prod.fst (gaussianData_bit true n)

@[simp] theorem gaussianPlanar_two_mul (n : ℕ) :
    gaussianPlanar (2 * n) = mulOnePlusI (gaussianPlanar n) := by
  simpa [gaussianPlanar, gaussianStep] using congrArg Prod.snd (gaussianData_bit false n)

@[simp] theorem gaussianPlanar_two_mul_add_one (n : ℕ) :
    gaussianPlanar (2 * n + 1) =
      addVec (mulOnePlusI (gaussianPlanar n)) (gaussianUnit n) := by
  simpa [gaussianPlanar, gaussianUnit, gaussianState, gaussianStep] using
    congrArg Prod.snd (gaussianData_bit true n)

@[simp] theorem gaussianUnit_two_mul (n : ℕ) : gaussianUnit (2 * n) = gaussianUnit n := by
  simp [gaussianUnit]

@[simp] theorem gaussianUnit_two_mul_add_one (n : ℕ) :
    gaussianUnit (2 * n + 1) = (-(gaussianUnit n).2, (gaussianUnit n).1) := by
  simp [gaussianUnit, Direction.vec_rotate]

@[simp] theorem gaussianPlanar_succ (n : ℕ) :
    gaussianPlanar (n + 1) = addVec (gaussianPlanar n) (gaussianUnit n) := by
  induction n using Nat.binaryRec with
  | zero => decide
  | bit b n ih =>
      cases b
      · simp [addVec]
      · rw [Nat.bit_true_apply]
        have heq : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
        rw [heq, gaussianPlanar_two_mul, ih, mulOnePlusI_add,
          gaussianPlanar_two_mul_add_one, gaussianUnit_two_mul_add_one]
        have hu := mulOnePlusI_direction (gaussianState n)
        rw [Direction.vec_rotate] at hu
        change mulOnePlusI (gaussianUnit n) =
          addVec (gaussianUnit n) (-(gaussianUnit n).2, (gaussianUnit n).1) at hu
        rw [hu]
        apply Prod.ext <;> simp [addVec] <;> ring


def subVec (p q : Vec2) : Vec2 := (p.1 - q.1, p.2 - q.2)

@[simp] theorem gaussianUnit_sum_parity (n : ℕ) :
    (2 : ℤ) ∣ (gaussianUnit n).1 + (gaussianUnit n).2 - 1 := by
  unfold gaussianUnit
  cases gaussianState n <;> simp [Direction.vec]

theorem gaussianPlanar_sum_parity (n : ℕ) :
    (2 : ℤ) ∣ (gaussianPlanar n).1 + (gaussianPlanar n).2 - n := by
  induction n with
  | zero => simp [gaussianPlanar]
  | succ n ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨b, hb⟩ := gaussianUnit_sum_parity n
      refine ⟨a + b, ?_⟩
      rw [gaussianPlanar_succ]
      simp only [addVec]
      omega

theorem subVec_sum_odd_of_gap_odd {m n : ℕ}
    (hgap : ¬(2 : ℤ) ∣ (n : ℤ) - m) :
    ¬(2 : ℤ) ∣ (subVec (gaussianPlanar n) (gaussianPlanar m)).1 +
      (subVec (gaussianPlanar n) (gaussianPlanar m)).2 := by
  intro hsum
  apply hgap
  obtain ⟨a, ha⟩ := gaussianPlanar_sum_parity n
  obtain ⟨b, hb⟩ := gaussianPlanar_sum_parity m
  obtain ⟨c, hc⟩ := hsum
  refine ⟨c - a + b, ?_⟩
  simp only [subVec] at hc
  omega

@[simp] theorem mulOnePlusI_sub (p q : Vec2) :
    subVec (mulOnePlusI p) (mulOnePlusI q) = mulOnePlusI (subVec p q) := by
  apply Prod.ext <;> simp [subVec, mulOnePlusI] <;> ring

theorem mulOnePlusI_ne_zero {u : Vec2} (hu : u ≠ (0, 0)) :
    mulOnePlusI u ≠ (0, 0) := by
  intro h
  apply hu
  apply Prod.ext
  · have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    simp [mulOnePlusI] at hx hy
    omega
  · have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    simp [mulOnePlusI] at hx hy
    omega

private theorem padicValNat_two_mul (d : ℕ) (hd : d ≠ 0) :
    padicValNat 2 (2 * d) = padicValNat 2 d + 1 := by
  rw [padicValNat.mul (by decide) hd, padicValNat_base (by decide)]
  omega

/-- Stijn Cambie's halving law, strengthened with nonvanishing of the chord. -/
private theorem gaussian_same_state_pair_law_aux {m n : ℕ} (hmn : m < n)
    (hstate : gaussianState m = gaussianState n) :
    pairVal (subVec (gaussianPlanar n) (gaussianPlanar m)) =
        padicValNat 2 (n - m) ∧
      subVec (gaussianPlanar n) (gaussianPlanar m) ≠ (0, 0) := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
      obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' m
      · obtain ⟨b, rfl | rfl⟩ := Nat.even_or_odd' n
        · have hab : a < b := by omega
          have hstate' : gaussianState a = gaussianState b := by simpa using hstate
          have hp := ih b (by omega) hab hstate'
          constructor
          · rw [gaussianPlanar_two_mul, gaussianPlanar_two_mul, mulOnePlusI_sub,
              pairVal_mulOnePlusI hp.2,
              show 2 * b - 2 * a = 2 * (b - a) by omega,
              padicValNat_two_mul (b - a) (by omega), hp.1]
          · rw [gaussianPlanar_two_mul, gaussianPlanar_two_mul, mulOnePlusI_sub]
            exact mulOnePlusI_ne_zero hp.2
        · have hodd := subVec_sum_odd_of_gap_odd (m := 2 * a) (n := 2 * b + 1) (by
            intro hd
            obtain ⟨k, hk⟩ := hd
            push_cast at hk
            omega)
          constructor
          · rw [pairVal_eq_zero_of_sum_not_two_dvd hodd]
            refine (padicValNat.eq_zero_of_not_dvd ?_).symm
            omega
          · intro hz
            have hsumzero := congrArg (fun p : Vec2 => p.1 + p.2) hz
            apply hodd
            rw [hsumzero]
            simp
      · obtain ⟨b, rfl | rfl⟩ := Nat.even_or_odd' n
        · have hodd := subVec_sum_odd_of_gap_odd (m := 2 * a + 1) (n := 2 * b) (by
            intro hd
            obtain ⟨k, hk⟩ := hd
            push_cast at hk
            omega)
          constructor
          · rw [pairVal_eq_zero_of_sum_not_two_dvd hodd]
            refine (padicValNat.eq_zero_of_not_dvd ?_).symm
            omega
          · intro hz
            have hsumzero := congrArg (fun p : Vec2 => p.1 + p.2) hz
            apply hodd
            rw [hsumzero]
            simp
        · have hab : a < b := by omega
          have hstate' : gaussianState a = gaussianState b := by
            apply Direction.rotate_injective
            simpa using hstate
          have hp := ih b (by omega) hab hstate'
          have hunit : gaussianUnit a = gaussianUnit b := by simp [gaussianUnit, hstate']
          have hchord :
              subVec
                  (addVec (mulOnePlusI (gaussianPlanar b)) (gaussianUnit b))
                  (addVec (mulOnePlusI (gaussianPlanar a)) (gaussianUnit a)) =
                mulOnePlusI (subVec (gaussianPlanar b) (gaussianPlanar a)) := by
            rw [hunit]
            apply Prod.ext <;> simp [subVec, addVec, mulOnePlusI] <;> ring
          constructor
          · rw [gaussianPlanar_two_mul_add_one, gaussianPlanar_two_mul_add_one,
              hchord, pairVal_mulOnePlusI hp.2,
              show (2 * b + 1) - (2 * a + 1) = 2 * (b - a) by omega,
              padicValNat_two_mul (b - a) (by omega), hp.1]
          · rw [gaussianPlanar_two_mul_add_one, gaussianPlanar_two_mul_add_one,
              hchord]
            exact mulOnePlusI_ne_zero hp.2

/-- Equal Gaussian direction states give the exact two-adic chord law. -/
theorem gaussian_same_state_pair_law {m n : ℕ} (hmn : m < n)
    (hstate : gaussianState m = gaussianState n) :
    pairVal (subVec (gaussianPlanar n) (gaussianPlanar m)) =
      padicValNat 2 (n - m) :=
  (gaussian_same_state_pair_law_aux hmn hstate).1

theorem gaussianPlanar_ne_of_same_state {m n : ℕ} (hmn : m < n)
    (hstate : gaussianState m = gaussianState n) :
    gaussianPlanar m ≠ gaussianPlanar n := by
  intro h
  apply (gaussian_same_state_pair_law_aux hmn hstate).2
  simp [subVec, h]

-- ============================================================
-- Section 3: Tagged construction and non-collinearity (from Construction.lean)
-- ============================================================

/-- Double the Gaussian point and append its direction as a Gray-code corner. -/
def taggedPlanar (n : ℕ) : Vec2 :=
  (2 * (gaussianPlanar n).1 + (gaussianState n).tag.1,
    2 * (gaussianPlanar n).2 + (gaussianState n).tag.2)

/-- Append the same direction state as the low base-4 height digit. -/
def taggedHeight (n : ℕ) : ℕ := 4 * n + (gaussianState n).label

@[ext] structure Point3 where
  x : ℤ
  y : ℤ
  z : ℤ
  deriving DecidableEq, Repr

/-- The explicit all-index Gaussian-lattice lift. -/
def taggedLift (n : ℕ) : Point3 where
  x := (taggedPlanar n).1
  y := (taggedPlanar n).2
  z := taggedHeight n

/-- Exact ordered collinearity equations for increasing heights. -/
def OrderedCollinear (p q r : Point3) : Prop :=
  (r.z - q.z) * (q.x - p.x) = (q.z - p.z) * (r.x - q.x) ∧
  (r.z - q.z) * (q.y - p.y) = (q.z - p.z) * (r.y - q.y)

private theorem doubled_tags_ne (p q : Direction) (hpq : p ≠ q) (X Y : Vec2) :
    ((2 * X.1 + p.tag.1, 2 * X.2 + p.tag.2) : Vec2) ≠
      (2 * Y.1 + q.tag.1, 2 * Y.2 + q.tag.2) := by
  cases p <;> cases q <;> simp [Direction.tag] at hpq ⊢ <;> omega

theorem taggedPlanar_ne {m n : ℕ} (hmn : m < n) : taggedPlanar m ≠ taggedPlanar n := by
  by_cases hs : gaussianState m = gaussianState n
  · intro htag
    apply gaussianPlanar_ne_of_same_state hmn hs
    apply Prod.ext
    · have hx := congrArg Prod.fst htag
      simp [taggedPlanar, hs] at hx
      omega
    · have hy := congrArg Prod.snd htag
      simp [taggedPlanar, hs] at hy
      omega
  · exact doubled_tags_ne (gaussianState m) (gaussianState n) hs
      (gaussianPlanar m) (gaussianPlanar n)

private theorem unequal_tag_pair_law (p q : Direction) (hpq : p ≠ q)
    (X : Vec2) (d : ℕ) (hd : d ≠ 0) :
    pairVal
        (2 * X.1 + q.tag.1 - p.tag.1,
          2 * X.2 + q.tag.2 - p.tag.2) =
      padicValNat 2 (4 * d + q.label - p.label) := by
  cases p <;> cases q <;>
    simp [Direction.tag, Direction.label] at hpq ⊢
  all_goals
    try rw [pairVal_eq_zero_of_sum_not_two_dvd (by omega),
      padicValNat.eq_zero_of_not_dvd (by omega)]
  all_goals
    rw [pairVal_odd_odd (by omega) (by omega)]
    symm
    apply padicValNat_eq_one_of_two_dvd_not_four <;> omega

private theorem padicValNat_four_mul (d : ℕ) (hd : d ≠ 0) :
    padicValNat 2 (4 * d) = padicValNat 2 d + 2 := by
  rw [show 4 * d = 2 * (2 * d) by ring,
    padicValNat.mul (by decide) (mul_ne_zero (by decide) hd),
    padicValNat.mul (by decide) hd, padicValNat_base (by decide)]
  omega

/-- The matching tags extend the Gaussian pair law to every ordered pair. -/
theorem tagged_pair_law {m n : ℕ} (hmn : m < n) :
    pairVal (subVec (taggedPlanar n) (taggedPlanar m)) =
      padicValNat 2 (taggedHeight n - taggedHeight m) := by
  by_cases hs : gaussianState m = gaussianState n
  · let u := subVec (gaussianPlanar n) (gaussianPlanar m)
    have hu : u ≠ (0, 0) := by
      intro h
      apply gaussianPlanar_ne_of_same_state hmn hs
      apply Prod.ext
      · have hx := congrArg Prod.fst h
        simp [u, subVec] at hx
        omega
      · have hy := congrArg Prod.snd h
        simp [u, subVec] at hy
        omega
    have hp := gaussian_same_state_pair_law hmn hs
    have hscale := pairVal_nsmul 2 u (by decide) hu
    have hplanar : subVec (taggedPlanar n) (taggedPlanar m) = (2 * u.1, 2 * u.2) := by
      apply Prod.ext <;> simp [taggedPlanar, subVec, u, hs] <;> ring
    have hheight : taggedHeight n - taggedHeight m = 4 * (n - m) := by
      simp [taggedHeight, hs]
      omega
    rw [hplanar, hheight]
    calc
      pairVal (2 * u.1, 2 * u.2) = pairVal u + 2 := by
        simpa using hscale
      _ = padicValNat 2 (4 * (n - m)) := by
        rw [hp, padicValNat_four_mul (n - m) (by omega)]
  · let X := subVec (gaussianPlanar n) (gaussianPlanar m)
    have hp := unequal_tag_pair_law (gaussianState m) (gaussianState n) hs X
      (n - m) (by omega)
    have hplanar :
        subVec (taggedPlanar n) (taggedPlanar m) =
          (2 * X.1 + (gaussianState n).tag.1 - (gaussianState m).tag.1,
            2 * X.2 + (gaussianState n).tag.2 - (gaussianState m).tag.2) := by
      apply Prod.ext <;> simp [taggedPlanar, subVec, X] <;> ring
    have hheight :
        taggedHeight n - taggedHeight m =
          4 * (n - m) + (gaussianState n).label - (gaussianState m).label := by
      have hm := Direction.label_le_three (gaussianState m)
      have hn := Direction.label_le_three (gaussianState n)
      simp [taggedHeight]
      omega
    rw [hplanar, hheight]
    exact hp

/-- Consecutive tagged heights increase by between one and seven. -/
theorem taggedHeight_succ_bounds (n : ℕ) :
    1 ≤ taggedHeight (n + 1) - taggedHeight n ∧
      taggedHeight (n + 1) - taggedHeight n ≤ 7 := by
  have ha := Direction.label_le_three (gaussianState n)
  have hb := Direction.label_le_three (gaussianState (n + 1))
  unfold taggedHeight
  omega

theorem taggedHeight_strictMono : StrictMono taggedHeight := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := taggedHeight_succ_bounds n
  omega

private theorem unequal_sum_valuation {A B : ℕ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : padicValNat 2 A = padicValNat 2 B) :
    padicValNat 2 (A + B) ≠ padicValNat 2 B := by
  let g := Nat.gcd A B
  let r := A / g
  let s := B / g
  have hg : g ≠ 0 := Nat.gcd_ne_zero_left hA
  have hgA : g ∣ A := Nat.gcd_dvd_left A B
  have hgB : g ∣ B := Nat.gcd_dvd_right A B
  have hAr : A = r * g := (Nat.div_mul_cancel hgA).symm
  have hBs : B = s * g := (Nat.div_mul_cancel hgB).symm
  have hr : r ≠ 0 := by intro h; rw [hAr, h, zero_mul] at hA; exact hA rfl
  have hs : s ≠ 0 := by intro h; rw [hBs, h, zero_mul] at hB; exact hB rfl
  have hrs : Nat.Coprime r s :=
    Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left B (Nat.pos_of_ne_zero hA))
  have hvrvs : padicValNat 2 r = padicValNat 2 s := by
    rw [hAr, hBs, padicValNat.mul hr hg, padicValNat.mul hs hg] at hAB
    omega
  have hvr : padicValNat 2 r = 0 := by
    by_contra hn
    have hdr : 2 ∣ r := by
      by_contra hnd
      exact hn (padicValNat.eq_zero_of_not_dvd hnd)
    have hds : 2 ∣ s := by
      by_contra hnd
      exact hn (hvrvs.trans (padicValNat.eq_zero_of_not_dvd hnd))
    have : 2 ∣ Nat.gcd r s := Nat.dvd_gcd hdr hds
    rw [hrs.gcd_eq_one] at this
    omega
  have hvs : padicValNat 2 s = 0 := hvrvs.symm.trans hvr
  have hrsEven : 2 ∣ r + s := by
    have hrodd : r % 2 = 1 := by
      apply Nat.mod_two_ne_zero.mp
      intro hm
      have hd : 2 ∣ r := Nat.dvd_iff_mod_eq_zero.mpr hm
      rw [padicValNat.eq_zero_iff] at hvr
      rcases hvr with hbad | hzero | hnot <;> omega
    have hsodd : s % 2 = 1 := by
      apply Nat.mod_two_ne_zero.mp
      intro hm
      have hd : 2 ∣ s := Nat.dvd_iff_mod_eq_zero.mpr hm
      rw [padicValNat.eq_zero_iff] at hvs
      rcases hvs with hbad | hzero | hnot <;> omega
    omega
  have hrs0 : r + s ≠ 0 := by
    intro h
    exact hr (Nat.eq_zero_of_add_eq_zero_right h)
  have hvsum : padicValNat 2 (r + s) ≠ 0 := by
    intro hz
    rw [padicValNat.eq_zero_iff] at hz
    rcases hz with hbad | hzero | hnot
    · omega
    · exact hrs0 hzero
    · exact hnot hrsEven
  intro heq
  have hsum : A + B = (r + s) * g := by rw [hAr, hBs, Nat.add_mul]
  rw [hsum, hBs, padicValNat.mul hrs0 hg, padicValNat.mul hs hg, hvs] at heq
  omega

/-- No three points of the explicit Gaussian tagged lift are collinear. -/
theorem taggedLift_no_three {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    ¬OrderedCollinear (taggedLift i) (taggedLift j) (taggedLift k) := by
  intro hcol
  let A := taggedHeight j - taggedHeight i
  let B := taggedHeight k - taggedHeight j
  have hA : A ≠ 0 := by have := taggedHeight_strictMono hij; omega
  have hB : B ≠ 0 := by have := taggedHeight_strictMono hjk; omega
  let u := subVec (taggedPlanar j) (taggedPlanar i)
  let v := subVec (taggedPlanar k) (taggedPlanar j)
  have hu : u ≠ (0, 0) := by
    intro h
    apply taggedPlanar_ne hij
    apply Prod.ext <;> have := congrArg Prod.fst h <;> simp [u, subVec] at * <;> omega
  have hv : v ≠ (0, 0) := by
    intro h
    apply taggedPlanar_ne hjk
    apply Prod.ext <;> have := congrArg Prod.fst h <;> simp [v, subVec] at * <;> omega
  have huw : addVec u v ≠ (0, 0) := by
    intro h
    apply taggedPlanar_ne (lt_trans hij hjk)
    apply Prod.ext
    · have hx := congrArg Prod.fst h
      simp [u, v, addVec, subVec] at hx
      omega
    · have hy := congrArg Prod.snd h
      simp [u, v, addVec, subVec] at hy
      omega
  have hHeightIJ : taggedHeight i ≤ taggedHeight j := (taggedHeight_strictMono hij).le
  have hHeightJK : taggedHeight j ≤ taggedHeight k := (taggedHeight_strictMono hjk).le
  have hx : (B : ℤ) * u.1 = (A : ℤ) * v.1 := by
    rcases hcol with ⟨hx, _⟩
    dsimp [A, B, u, v]
    rw [Nat.cast_sub hHeightJK, Nat.cast_sub hHeightIJ]
    simpa [subVec, OrderedCollinear, taggedLift] using hx
  have hy : (B : ℤ) * u.2 = (A : ℤ) * v.2 := by
    rcases hcol with ⟨_, hy⟩
    dsimp [A, B, u, v]
    rw [Nat.cast_sub hHeightJK, Nat.cast_sub hHeightIJ]
    simpa [subVec, OrderedCollinear, taggedLift] using hy
  have hU : pairVal u = padicValNat 2 A := by simpa [u, A] using tagged_pair_law hij
  have hV : pairVal v = padicValNat 2 B := by simpa [v, B] using tagged_pair_law hjk
  have hUV : pairVal (addVec u v) = padicValNat 2 (A + B) := by
    have hp := tagged_pair_law (lt_trans hij hjk)
    have hgap : taggedHeight k - taggedHeight i = A + B := by
      have hi := taggedHeight_strictMono hij
      have hj := taggedHeight_strictMono hjk
      simp [A, B]
      omega
    rw [hgap] at hp
    have hchord : subVec (taggedPlanar k) (taggedPlanar i) = addVec u v := by
      apply Prod.ext <;> simp [u, v, addVec, subVec]
    rwa [hchord] at hp
  have hscaled :
      ((B : ℤ) * u.1, (B : ℤ) * u.2) = ((A : ℤ) * v.1, (A : ℤ) * v.2) :=
    Prod.ext hx hy
  have hscaleB := pairVal_nsmul B u hB hu
  have hscaleA := pairVal_nsmul A v hA hv
  rw [hscaled, hscaleA, hU, hV] at hscaleB
  have hAB : padicValNat 2 A = padicValNat 2 B := by omega
  have hscaledSum :
      ((B : ℤ) * (addVec u v).1, (B : ℤ) * (addVec u v).2) =
        (((A + B : ℕ) : ℤ) * v.1, ((A + B : ℕ) : ℤ) * v.2) := by
    apply Prod.ext <;> simp [addVec] <;> ring_nf at hx hy ⊢ <;> omega
  have hscaleSumB := pairVal_nsmul B (addVec u v) hB huw
  have hscaleSumAB := pairVal_nsmul (A + B) v (by omega) hv
  rw [hscaledSum, hscaleSumAB, hUV, hV] at hscaleSumB
  have hsumEq : padicValNat 2 (A + B) = padicValNat 2 B := by omega
  exact unequal_sum_valuation hA hB hAB hsumEq

-- ============================================================
-- Section 4: Step bounds and final theorem (from Continuity.lean)
-- ============================================================

/-- Difference between two 3D points. -/
def displacement (p q : Point3) : Point3 where
  x := q.x - p.x
  y := q.y - p.y
  z := q.z - p.z

/-- The step determined by the current and next Gaussian directions. -/
def gaussianStepVector (p q : Direction) : Point3 where
  x := 2 * p.vec.1 + q.tag.1 - p.tag.1
  y := 2 * p.vec.2 + q.tag.2 - p.tag.2
  z := 4 + q.label - p.label

def Direction.toFin : Direction → Fin 4
  | .east => 0
  | .north => 1
  | .west => 2
  | .south => 3

def directionOfFin (i : Fin 4) : Direction :=
  match i.1 with
  | 0 => .east
  | 1 => .north
  | 2 => .west
  | _ => .south

@[simp] theorem directionOfFin_toFin (d : Direction) :
    directionOfFin d.toFin = d := by cases d <;> rfl

/-- The fixed menu indexed by the sixteen ordered pairs of direction states. -/
def finiteStepMenu : Set Point3 :=
  Set.range fun pq : Fin 4 × Fin 4 =>
    gaussianStepVector (directionOfFin pq.1) (directionOfFin pq.2)

theorem finiteStepMenu_finite : finiteStepMenu.Finite := Set.finite_range _

theorem gaussianStepVector_bounds (p q : Direction) :
    -2 ≤ (gaussianStepVector p q).x ∧ (gaussianStepVector p q).x ≤ 2 ∧
    -2 ≤ (gaussianStepVector p q).y ∧ (gaussianStepVector p q).y ≤ 2 ∧
    1 ≤ (gaussianStepVector p q).z ∧ (gaussianStepVector p q).z ≤ 7 := by
  cases p <;> cases q <;>
    norm_num [gaussianStepVector, Direction.vec, Direction.tag, Direction.label]

/-- Each successive displacement is one of the sixteen state-pair vectors. -/
theorem taggedLift_step_mem (n : ℕ) :
    displacement (taggedLift n) (taggedLift (n + 1)) ∈ finiteStepMenu := by
  refine ⟨((gaussianState n).toFin, (gaussianState (n + 1)).toFin), ?_⟩
  apply Point3.ext
  · simp [displacement, taggedLift, taggedPlanar, gaussianStepVector,
      gaussianPlanar_succ, addVec, gaussianUnit]
    ring
  · simp [displacement, taggedLift, taggedPlanar, gaussianStepVector,
      gaussianPlanar_succ, addVec, gaussianUnit]
    ring
  · simp [displacement, taggedLift, taggedHeight, gaussianStepVector]
    ring

/-- **The complete answer to JSP-000183.** There exists an infinite walk in Z³ with
steps from a finite set of sixteen vectors, with no three collinear vertices.

This is the Cambie–Kalviainen construction (arXiv:2609.01766, 2026) answering a
problem of Gerver and Ramsey (1979), popularized as Erdős Problem 193. -/
theorem jsp000183 :
    ∃ (S : Set Point3) (P : ℕ → Point3),
      S.Finite ∧
      (∀ n, displacement (P n) (P (n + 1)) ∈ S) ∧
      (∀ ⦃i j k⦄, i < j → j < k → ¬ OrderedCollinear (P i) (P j) (P k)) := by
  refine ⟨finiteStepMenu, taggedLift, finiteStepMenu_finite, taggedLift_step_mem, ?_⟩
  intro i j k hij hjk
  exact taggedLift_no_three hij hjk

end JSP000183
