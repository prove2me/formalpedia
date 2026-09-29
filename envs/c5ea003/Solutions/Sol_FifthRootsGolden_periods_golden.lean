-- Prove2me | solution 1 for FifthRootsGolden.periods_golden
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:54:17.135065+00:00
-- url     : https://prove2.me/submissions/75809133-0bed-4f52-8ba7-b9f5b7b6f136

-- Sol generated from Novelty/FifthRootsGoldenBridge.lean
import Mathlib
import Definitions.Def_Novelty_FifthRootsGoldenBridge
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



/-- The two Gaussian periods have sum `-1` and product `-1`; hence each is a root of
`x² + x - 1 = 0`, the (negated) minimal polynomial of the golden ratio. -/
theorem periods_sum_prod (ζ : ℂ) (h : IsPrimitiveRoot ζ 5) :
    p ζ + q ζ = -1 ∧ p ζ * q ζ = -1 := by
  have h5 : ζ ^ 5 = 1 := h.pow_eq_one
  have hsum : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
    have := h.geom_sum_eq_zero (by norm_num)
    simp [Finset.sum_range_succ] at this
    linear_combination this
  refine ⟨by simp only [p, q]; linear_combination hsum, ?_⟩
  simp only [p, q]; linear_combination hsum + (ζ + ζ ^ 2) * h5


/-! ## The cross-domain bridge theorems -/



/-! ## The golden ratio as a modulus of a sum of fifth roots of unity -/




/-! ## `σ₅(2) = φ⁻¹`: the golden ratio inverse is the minimal two-term modulus -/





/-! ## Non-vacuity: a concrete primitive fifth root of unity -/







open FifthRootsGolden in
theorem solution(ζ : ℂ) (h : IsPrimitiveRoot ζ 5) :
    (p ζ = -((goldenRatio : ℝ) : ℂ) ∧ q ζ = -((goldenConj : ℝ) : ℂ)) ∨
    (p ζ = -((goldenConj : ℝ) : ℂ) ∧ q ζ = -((goldenRatio : ℝ) : ℂ)) := by
  obtain ⟨hsum, hprod⟩ := periods_sum_prod ζ h
  set a : ℂ := ((goldenRatio : ℝ) : ℂ) with ha
  set b : ℂ := ((goldenConj : ℝ) : ℂ) with hb
  have hs : a + b = 1 := by
    rw [ha, hb, ← Complex.ofReal_add, goldenRatio_add_goldenConj]; norm_num
  have hproot : p ζ ^ 2 + p ζ - 1 = 0 := by
    have hq : q ζ = -1 - p ζ := by linear_combination hsum
    rw [hq] at hprod; linear_combination -hprod
  have hpval : p ζ = -a ∨ p ζ = -b := by
    have hp2 : a * b = -1 := by
      rw [ha, hb, ← Complex.ofReal_mul, goldenRatio_mul_goldenConj]; norm_num
    have factored : (p ζ + a) * (p ζ + b) = 0 := by
      have e : (p ζ + a) * (p ζ + b) = p ζ ^ 2 + p ζ - 1 := by
        linear_combination (p ζ) * hs + hp2
      rw [e, hproot]
    rcases mul_eq_zero.1 factored with h1 | h1
    · left; linear_combination h1
    · right; linear_combination h1
  have hqval : q ζ = -1 - p ζ := by linear_combination hsum
  rcases hpval with hp | hp
  · left; refine ⟨hp, ?_⟩; rw [hqval, hp]; linear_combination hs
  · right; refine ⟨hp, ?_⟩; rw [hqval, hp]; linear_combination hs
