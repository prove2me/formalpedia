-- Prove2me | Definitions.Def_Logic_ConstructiveAnalysis_ComputableReals
-- name    : Logic_ConstructiveAnalysis_ComputableReals
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:50:54.784413+00:00
-- url     : https://prove2.me/theorems/e9c5340e-e727-43fe-a1df-e5672e727365
-- title:
--   Aether Catalog definitions — Logic_ConstructiveAnalysis_ComputableReals
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.ConstructiveAnalysis.ComputableReals`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/ConstructiveAnalysis/ComputableReals.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
/-
# Computable arithmetic on Bishop reals, and a concrete computable irrational

The Bishop reals of `Logic/ConstructiveAnalysis/BishopReals.lean` are *data*: a
regular sequence of rationals is a computable object whenever its approximating
function is.  This file supplies the basic algebraic operations in Bishop's
explicit form — with the index shifts that make the results regular again — and
verifies that they compute the classical operations under `toReal`.

* `Bishop.Reg.ofRat`, `Reg.neg`, `Reg.add`, `Reg.mul` are ordinary (computable)
  definitions; only `toReal` is noncomputable.
* `Bishop.Reg.toReal_ofRat`, `toReal_neg`, `toReal_add`, `toReal_mul` verify them.
* `Bishop.sqrtTwo` is an explicitly computable Bishop real (its `n`-th approximation
  is `⌊√(2(n+1)²)⌋/(n+1)`, computed with `Nat.sqrt`), and
  `Bishop.toReal_sqrtTwo`, `Bishop.sqrtTwo_sq` prove that it denotes `√2`.
-/


namespace Bishop

namespace Reg

/-! ## Rational constants -/

/-- The Bishop real determined by a rational number. -/
def ofRat (q : ℚ) : Reg where
  approx _ := q
  regular m n := by
    have : (0 : ℚ) ≤ 1 / (m + 1) + 1 / (n + 1) := by positivity
    simpa using this



/-! ## Negation -/

/-- Negation of a Bishop real (no index shift is needed). -/
def neg (x : Reg) : Reg where
  approx n := -x.approx n
  regular m n := by
    have h := x.regular m n
    calc |(-x.approx m) - (-x.approx n)| = |x.approx m - x.approx n| := by
          rw [← abs_neg]; ring_nf
      _ ≤ 1 / (m + 1) + 1 / (n + 1) := h



/-! ## Addition -/

/-- Addition of Bishop reals, with Bishop's index shift `n ↦ 2n+1`. -/
def add (x y : Reg) : Reg where
  approx n := x.approx (2 * n + 1) + y.approx (2 * n + 1)
  regular m n := by
    have hx := x.regular (2 * m + 1) (2 * n + 1)
    have hy := y.regular (2 * m + 1) (2 * n + 1)
    have e1 : ((2 * m + 1 : ℕ) : ℚ) + 1 = 2 * ((m : ℚ) + 1) := by push_cast; ring
    have e2 : ((2 * n + 1 : ℕ) : ℚ) + 1 = 2 * ((n : ℚ) + 1) := by push_cast; ring
    rw [e1, e2] at hx hy
    have hm : (1 : ℚ) / (2 * ((m : ℚ) + 1)) = (1 / ((m : ℚ) + 1)) / 2 := by
      rw [div_div]; ring_nf
    have hn : (1 : ℚ) / (2 * ((n : ℚ) + 1)) = (1 / ((n : ℚ) + 1)) / 2 := by
      rw [div_div]; ring_nf
    rw [hm, hn] at hx hy
    have habs : |(x.approx (2 * m + 1) + y.approx (2 * m + 1))
        - (x.approx (2 * n + 1) + y.approx (2 * n + 1))|
        ≤ |x.approx (2 * m + 1) - x.approx (2 * n + 1)|
          + |y.approx (2 * m + 1) - y.approx (2 * n + 1)| := by
      have : (x.approx (2 * m + 1) + y.approx (2 * m + 1))
          - (x.approx (2 * n + 1) + y.approx (2 * n + 1))
          = (x.approx (2 * m + 1) - x.approx (2 * n + 1))
            + (y.approx (2 * m + 1) - y.approx (2 * n + 1)) := by ring
      rw [this]
      exact abs_add_le _ _
    have hgoal : (1 : ℚ) / ((m : ℚ) + 1) + 1 / ((n : ℚ) + 1)
        = ((1 / ((m : ℚ) + 1)) / 2 + (1 / ((n : ℚ) + 1)) / 2)
          + ((1 / ((m : ℚ) + 1)) / 2 + (1 / ((n : ℚ) + 1)) / 2) := by ring
    rw [hgoal]
    linarith



/-! ## Multiplication

Multiplication needs an explicit *bound* for the factors; Bishop's canonical bound
`⌈|x₀|⌉ + 2` is used, and the index shift is by the sum of the two bounds. -/

/-- Bishop's canonical bound for a regular sequence: `|x n| ≤ x.bound` for all `n`. -/
def bound (x : Reg) : ℕ := ⌈|x.approx 0|⌉₊ + 2

lemma one_le_bound (x : Reg) : 1 ≤ x.bound := by
  simp only [bound]
  omega

lemma abs_approx_le_bound (x : Reg) (n : ℕ) : |x.approx n| ≤ (x.bound : ℚ) := by
  have hreg := x.regular n 0
  have e0 : ((0 : ℕ) : ℚ) + 1 = 1 := by norm_num
  rw [e0, div_one] at hreg
  have h0 : (1 : ℚ) / ((n : ℚ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
    linarith
  have h1 : |x.approx n| ≤ |x.approx 0| + |x.approx n - x.approx 0| := by
    have hx : x.approx n = x.approx 0 + (x.approx n - x.approx 0) := by ring
    calc |x.approx n| = |x.approx 0 + (x.approx n - x.approx 0)| := by rw [← hx]
      _ ≤ |x.approx 0| + |x.approx n - x.approx 0| := abs_add_le _ _
  have hceil : |x.approx 0| ≤ (⌈|x.approx 0|⌉₊ : ℚ) := Nat.le_ceil _
  have hb : ((x.bound : ℕ) : ℚ) = (⌈|x.approx 0|⌉₊ : ℚ) + 2 := by
    simp only [bound]; push_cast; ring
  rw [hb]
  linarith


/-- The index shift used in the product: `n ↦ M(n+1)` with `M = x.bound + y.bound`. -/
def mulIdx (x y : Reg) (n : ℕ) : ℕ := (x.bound + y.bound) * (n + 1)

lemma inv_mulIdx_le (x y : Reg) (n : ℕ) :
    ((x.bound + y.bound : ℕ) : ℚ) * (1 / ((mulIdx x y n : ℕ) + 1)) ≤ 1 / ((n : ℚ) + 1) := by
  set M : ℕ := x.bound + y.bound with hM
  have hM1 : 1 ≤ M := le_trans x.one_le_bound (Nat.le_add_right _ _)
  have hMQ : (1 : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM1
  have hidx : ((mulIdx x y n : ℕ) : ℚ) + 1 = (M : ℚ) * ((n : ℚ) + 1) + 1 := by
    simp only [mulIdx, hM]
    push_cast
    ring
  rw [hidx, mul_one_div]
  refine (div_le_div_iff₀ (by positivity) (by positivity)).mpr ?_
  have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
  nlinarith

/-- Product of Bishop reals, with Bishop's index shift by the sum of the bounds. -/
def mul (x y : Reg) : Reg where
  approx n := x.approx (mulIdx x y n) * y.approx (mulIdx x y n)
  regular m n := by
    set a := mulIdx x y m with ha
    set b := mulIdx x y n with hb
    have hx := x.regular a b
    have hy := y.regular a b
    have hxb := x.abs_approx_le_bound a
    have hyb := y.abs_approx_le_bound b
    have hsplit : |x.approx a * y.approx a - x.approx b * y.approx b|
        ≤ |x.approx a| * |y.approx a - y.approx b|
          + |y.approx b| * |x.approx a - x.approx b| := by
      have he : x.approx a * y.approx a - x.approx b * y.approx b
          = x.approx a * (y.approx a - y.approx b) + y.approx b * (x.approx a - x.approx b) := by
        ring
      rw [he]
      calc |x.approx a * (y.approx a - y.approx b) + y.approx b * (x.approx a - x.approx b)|
          ≤ |x.approx a * (y.approx a - y.approx b)|
            + |y.approx b * (x.approx a - x.approx b)| := abs_add_le _ _
        _ = |x.approx a| * |y.approx a - y.approx b|
            + |y.approx b| * |x.approx a - x.approx b| := by rw [abs_mul, abs_mul]
    -- bound each term by `bound * (1/(a+1) + 1/(b+1))`
    have hterm1 : |x.approx a| * |y.approx a - y.approx b|
        ≤ (x.bound : ℚ) * (1 / ((a : ℚ) + 1) + 1 / ((b : ℚ) + 1)) := by
      apply mul_le_mul hxb hy (abs_nonneg _) (by positivity)
    have hterm2 : |y.approx b| * |x.approx a - x.approx b|
        ≤ (y.bound : ℚ) * (1 / ((a : ℚ) + 1) + 1 / ((b : ℚ) + 1)) := by
      apply mul_le_mul hyb hx (abs_nonneg _) (by positivity)
    have hsum : |x.approx a * y.approx a - x.approx b * y.approx b|
        ≤ ((x.bound : ℚ) + (y.bound : ℚ)) * (1 / ((a : ℚ) + 1) + 1 / ((b : ℚ) + 1)) := by
      nlinarith [hsplit, hterm1, hterm2]
    have hA : ((x.bound + y.bound : ℕ) : ℚ) * (1 / ((a : ℚ) + 1)) ≤ 1 / ((m : ℚ) + 1) :=
      inv_mulIdx_le x y m
    have hB : ((x.bound + y.bound : ℕ) : ℚ) * (1 / ((b : ℚ) + 1)) ≤ 1 / ((n : ℚ) + 1) :=
      inv_mulIdx_le x y n
    have hcast : ((x.bound + y.bound : ℕ) : ℚ) = (x.bound : ℚ) + (y.bound : ℚ) := by push_cast; ring
    rw [hcast] at hA hB
    nlinarith [hsum, hA, hB]



end Reg

/-! ## A concrete computable irrational: `√2`

`sqrtTwo.approx n = ⌊√(2(n+1)²)⌋ / (n+1)`, computed with `Nat.sqrt`; the regularity
proof is the elementary estimate `⌊√(2m²)⌋/m ≤ √2 < ⌊√(2m²)⌋/m + 1/m`. -/

lemma sqrt_two_approx_bound (m : ℕ) (hm : 0 < m) :
    |((Nat.sqrt (2 * m ^ 2) : ℚ) / m : ℚ) - Real.sqrt 2| ≤ 1 / (m : ℝ) := by
  set s : ℕ := Nat.sqrt (2 * m ^ 2) with hs
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlow : (s : ℝ) ≤ Real.sqrt 2 * m := by
    have h : s ^ 2 ≤ 2 * m ^ 2 := Nat.sqrt_le' _
    have hR : (s : ℝ) ^ 2 ≤ 2 * (m : ℝ) ^ 2 := by exact_mod_cast h
    have h2 : (Real.sqrt 2 * m) ^ 2 = 2 * (m : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    by_contra hcon
    push_neg at hcon
    have hprod : (0 : ℝ) ≤ Real.sqrt 2 * m := by positivity
    have hlt : (Real.sqrt 2 * m) ^ 2 < (s : ℝ) ^ 2 := by nlinarith
    linarith
  have hhigh : Real.sqrt 2 * m < (s : ℝ) + 1 := by
    have h : 2 * m ^ 2 < (s + 1) ^ 2 := Nat.lt_succ_sqrt' _
    have hR : 2 * (m : ℝ) ^ 2 < ((s : ℝ) + 1) * ((s : ℝ) + 1) := by
      have : ((2 * m ^ 2 : ℕ) : ℝ) < (((s + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this
      nlinarith [this]
    have h2 : (Real.sqrt 2 * m) ^ 2 = 2 * (m : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith [Real.sqrt_nonneg 2, Nat.cast_nonneg (α := ℝ) s, mul_pos hmR hmR]
  have hcast : (((Nat.sqrt (2 * m ^ 2) : ℚ) / m : ℚ) : ℝ) = (s : ℝ) / (m : ℝ) := by
    simp only [hs]
    push_cast
    ring
  rw [hcast, abs_le]
  constructor
  · have hB : Real.sqrt 2 - 1 / (m : ℝ) ≤ (s : ℝ) / m := by
      rw [le_div_iff₀ hmR]
      have he : (Real.sqrt 2 - 1 / (m : ℝ)) * m = Real.sqrt 2 * m - 1 := by
        field_simp
      rw [he]
      linarith
    linarith
  · have hA : (s : ℝ) / m ≤ Real.sqrt 2 := by
      rw [div_le_iff₀ hmR]
      linarith
    have hpos : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
    linarith

/-- An explicitly computable Bishop real denoting `√2`: the `n`-th approximation is
`⌊√(2(n+1)²)⌋ / (n+1)`, computed with `Nat.sqrt`. -/
def sqrtTwo : Reg where
  approx n := (Nat.sqrt (2 * (n + 1) ^ 2) : ℚ) / (n + 1)
  regular m n := by
    have hm := sqrt_two_approx_bound (m + 1) (Nat.succ_pos m)
    have hn := sqrt_two_approx_bound (n + 1) (Nat.succ_pos n)
    push_cast at hm hn
    have h2 : |Real.sqrt 2
          - (Nat.sqrt (2 * (n + 1) ^ 2) : ℝ) / ((n : ℝ) + 1)| ≤ 1 / ((n : ℝ) + 1) := by
      rw [abs_sub_comm]; exact hn
    have h1 := abs_sub_le ((Nat.sqrt (2 * (m + 1) ^ 2) : ℝ) / ((m : ℝ) + 1)) (Real.sqrt 2)
      ((Nat.sqrt (2 * (n + 1) ^ 2) : ℝ) / ((n : ℝ) + 1))
    have hR : |(Nat.sqrt (2 * (m + 1) ^ 2) : ℝ) / ((m : ℝ) + 1)
          - (Nat.sqrt (2 * (n + 1) ^ 2) : ℝ) / ((n : ℝ) + 1)|
        ≤ 1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by linarith
    have h' : ((|(Nat.sqrt (2 * (m + 1) ^ 2) : ℚ) / ((m : ℚ) + 1)
        - (Nat.sqrt (2 * (n + 1) ^ 2) : ℚ) / ((n : ℚ) + 1)| : ℚ) : ℝ)
        ≤ (((1 : ℚ) / ((m : ℚ) + 1) + 1 / ((n : ℚ) + 1) : ℚ) : ℝ) := by
      push_cast
      exact hR
    exact_mod_cast h'

-- The approximations of `sqrtTwo` are genuinely computable rationals:
#guard sqrtTwo.approx 4 = 7 / 5
#guard sqrtTwo.approx 99 = 141 / 100



end Bishop


