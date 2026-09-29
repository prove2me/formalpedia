-- Prove2me | solution 1 for FifthRootsGolden.re_period
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:55:47.324089+00:00
-- url     : https://prove2.me/submissions/6ac0a77a-2356-4490-9f98-ccfab3ab8f65

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





/-! ## The cross-domain bridge theorems -/



/-! ## The golden ratio as a modulus of a sum of fifth roots of unity -/




/-! ## `σ₅(2) = φ⁻¹`: the golden ratio inverse is the minimal two-term modulus -/





/-! ## Non-vacuity: a concrete primitive fifth root of unity -/







open FifthRootsGolden in
theorem solution(ζ : ℂ) (h : IsPrimitiveRoot ζ 5) (e : ℕ) :
    ζ ^ e + (ζ ^ e) ^ 4 = 2 ∨ ζ ^ e + (ζ ^ e) ^ 4 = p ζ ∨ ζ ^ e + (ζ ^ e) ^ 4 = q ζ := by
  have h5 : ζ ^ 5 = 1 := h.pow_eq_one
  have hpow : ζ ^ e = ζ ^ (e % 5) := by
    conv_lhs => rw [← Nat.div_add_mod e 5]
    rw [pow_add, pow_mul, h5, one_pow, one_mul]
  rw [hpow]
  have hlt : e % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases (e % 5)
  · left; norm_num
  · right; left; simp only [p]; ring
  · right; right; simp only [q]
    have he2 : (ζ ^ 2) ^ 4 = ζ ^ 3 := by
      have : (ζ ^ 2) ^ 4 = (ζ ^ 5) * ζ ^ 3 := by ring
      rw [this, h5, one_mul]
    rw [he2]
  · right; right; simp only [q]
    have he3 : (ζ ^ 3) ^ 4 = ζ ^ 2 := by
      have : (ζ ^ 3) ^ 4 = (ζ ^ 5) ^ 2 * ζ ^ 2 := by ring
      rw [this, h5, one_pow, one_mul]
    rw [he3]; ring
  · right; left; simp only [p]
    have he4 : (ζ ^ 4) ^ 4 = ζ := by
      have : (ζ ^ 4) ^ 4 = (ζ ^ 5) ^ 3 * ζ := by ring
      rw [this, h5, one_pow, one_mul]
    rw [he4]; ring
