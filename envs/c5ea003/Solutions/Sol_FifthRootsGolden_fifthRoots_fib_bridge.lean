-- Prove2me | solution 1 for FifthRootsGolden.fifthRoots_fib_bridge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:55:46.044029+00:00
-- url     : https://prove2.me/submissions/ddf4c3da-7606-4d55-b12f-1aceb9340f7f

-- Sol generated from Novelty/FifthRootsGoldenBridge.lean
import Mathlib
import Definitions.Def_Novelty_FifthRootsGoldenBridge
import Theorems.Thm_FifthRootsGolden_periods_golden
/-
# A Cross-Domain Bridge: Fifth Roots of Unity ↔ Fibonacci and Lucas Numbers

This file establishes, in a fully self-contained way, the algebraic bridge that
underlies the study of `σ₅(n)`, the minimal absolute value of a non-vanishing sum
of `n` fifth roots of unity.

The key objects are the two *Gaussian periods* of the fifth cyclotomic field:

* `p ζ = ζ + ζ⁴`
* `q ζ = ζ² + ζ³`

for a primitive fifth root of unity `ζ`.  These are real quadratic irrationals and
are exactly the two roots of `x² + x - 1 = 0`, i.e. `{-φ, -ψ}` where `φ` is the golden
ratio and `ψ = goldenConj` its conjugate.  This is the bridge between:

* **fifth roots of unity** (cyclotomic / algebraic number theory), and
* **the golden ratio, Fibonacci and Lucas numbers** (combinatorial number theory).

Main results (all unconditional in the choice of primitive root `ζ`):

* `periods_sum_prod`  : `p ζ + q ζ = -1` and `p ζ * q ζ = -1`.
* `periods_golden`    : `{p ζ, q ζ} = {-φ, -ψ}`.
* `fifthRoots_lucas_bridge` : `(p ζ)^n + (q ζ)^n = (-1)^n · Lₙ`  (Lucas numbers).
* `fifthRoots_fib_bridge`   : `((p ζ)^n - (q ζ)^n)² = 5 · (Fₙ)²`  (Fibonacci numbers).
* `golden_ratio_is_modulus` : `{‖p ζ‖, ‖q ζ‖} = {φ, φ⁻¹}`, so the golden ratio is
  realized *exactly* as the modulus of a sum of two fifth roots of unity — and `φ⁻¹`
  is the minimal such modulus, which is precisely `σ₅(2)`.
* `sigma5_two` : `IsLeast {‖ζ^i + ζ^j‖ | i j} φ⁻¹`, a fully formal statement that `φ⁻¹`
  is the least modulus among *all* two-term sums of fifth roots of unity, i.e. the value
  `σ₅(2) = φ⁻¹`.

The full monotonicity / jump characterization of `σ₅(n)` (with jumps located at
`5Fₘ, Lₘ, 2Lₘ`) is discussed in `FUTURE_DIRECTIONS.md`; this file proves the exact
algebraic connection that makes Fibonacci and Lucas numbers appear in that problem.
-/

open Real

open FifthRootsGolden

/-! ## Lucas numbers and their Binet formula -/



/-! ## The Gaussian periods of the fifth cyclotomic field -/





/-! ## The cross-domain bridge theorems -/



/-! ## The golden ratio as a modulus of a sum of fifth roots of unity -/




/-! ## `σ₅(2) = φ⁻¹`: the golden ratio inverse is the minimal two-term modulus -/





/-! ## Non-vacuity: a concrete primitive fifth root of unity -/







open FifthRootsGolden in
theorem solution(ζ : ℂ) (h : IsPrimitiveRoot ζ 5) (n : ℕ) :
    ((p ζ) ^ n - (q ζ) ^ n) ^ 2 = 5 * (Nat.fib n : ℂ) ^ 2 := by
  -- `φⁿ - ψⁿ = √5 · Fₙ`, hence `(φⁿ - ψⁿ)² = 5 Fₙ²` over `ℂ`.
  have key : (((goldenRatio : ℝ) : ℂ) ^ n - ((goldenConj : ℝ) : ℂ) ^ n) ^ 2
      = 5 * (Nat.fib n : ℂ) ^ 2 := by
    have hfib : goldenRatio ^ n - goldenConj ^ n = Real.sqrt 5 * (Nat.fib n : ℝ) := by
      have := Real.coe_fib_eq n
      field_simp at this ⊢
      linear_combination -this
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_sub, hfib]
    rw [Complex.ofReal_mul, mul_pow, ← Complex.ofReal_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    push_cast; ring
  -- The square is symmetric under negating both periods.
  have hswap : ∀ x y : ℂ, ((-x) ^ n - (-y) ^ n) ^ 2 = (x ^ n - y ^ n) ^ 2 := by
    intro x y
    rw [neg_pow x n, neg_pow y n, ← mul_sub, mul_pow, ← pow_mul, mul_comm n 2, pow_mul,
      neg_one_sq, one_pow, one_mul]
  rcases periods_golden ζ h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, hswap]; exact key
  · rw [h1, h2, hswap,
      show (((goldenConj : ℝ) : ℂ) ^ n - ((goldenRatio : ℝ) : ℂ) ^ n) ^ 2
        = (((goldenRatio : ℝ) : ℂ) ^ n - ((goldenConj : ℝ) : ℂ) ^ n) ^ 2 by ring]
    exact key
