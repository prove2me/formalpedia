-- Prove2me | solution 1 for FifthRootsGolden.two_term_modulus_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:57:31.390078+00:00
-- url     : https://prove2.me/submissions/109ad50f-60d2-4897-b626-b3b51b8659d0

-- Sol generated from Novelty/FifthRootsGoldenBridge.lean
import Mathlib
import Definitions.Def_Novelty_FifthRootsGoldenBridge
import Theorems.Thm_FifthRootsGolden_periods_golden
import Theorems.Thm_FifthRootsGolden_re_period
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
theorem solution(ζ : ℂ) (h : IsPrimitiveRoot ζ 5) (i j : ℕ) :
    goldenRatio⁻¹ ≤ ‖ζ ^ i + ζ ^ j‖ := by
  have h5 : ζ ^ 5 = 1 := h.pow_eq_one
  have hnorm : ‖ζ‖ = 1 := by
    have hn : ‖ζ‖ ^ 5 = 1 := by rw [← norm_pow, h5, norm_one]
    have hnn : (0 : ℝ) ≤ ‖ζ‖ := norm_nonneg ζ
    nlinarith [hn, hnn, sq_nonneg (‖ζ‖ - 1), pow_nonneg hnn 3, pow_nonneg hnn 4]
  have hns : Complex.normSq ζ = 1 := by
    have := Complex.normSq_eq_norm_sq ζ; rw [this, hnorm]; norm_num
  have hconj : (starRingEnd ℂ) ζ = ζ ^ 4 := by
    have hinv : ζ⁻¹ = (starRingEnd ℂ) ζ := by rw [Complex.inv_def, hns]; simp
    have hmul : ζ * ζ ^ 4 = 1 := by rw [← pow_succ']; exact h5
    rw [← hinv, inv_eq_of_mul_eq_one_right hmul]
  have hnsp : ∀ k : ℕ, Complex.normSq (ζ ^ k) = 1 := by
    intro k; rw [Complex.normSq_eq_norm_sq, norm_pow, hnorm]; simp
  have hcj : (starRingEnd ℂ) (ζ ^ j) = ζ ^ (4 * j) := by
    rw [map_pow, hconj, ← pow_mul, Nat.mul_comm]
  set e := i + 4 * j with he
  have hprod : ζ ^ i * (starRingEnd ℂ) (ζ ^ j) = ζ ^ e := by rw [hcj, ← pow_add]
  have hre : ((2 * (ζ ^ e).re : ℝ) : ℂ) = ζ ^ e + (ζ ^ e) ^ 4 := by
    have hc : (starRingEnd ℂ) (ζ ^ e) = (ζ ^ e) ^ 4 := by
      rw [map_pow, hconj, ← pow_mul, ← pow_mul, Nat.mul_comm 4 e]
    have hadd := Complex.add_conj (ζ ^ e)
    rw [hc] at hadd
    exact hadd.symm
  have hexp : Complex.normSq (ζ ^ i + ζ ^ j) = 2 + 2 * (ζ ^ e).re := by
    rw [Complex.normSq_add, hnsp, hnsp, hprod]; ring
  have hval := re_period ζ h e
  have key : (2 * (ζ ^ e).re : ℝ) = 2 ∨ (2 * (ζ ^ e).re : ℝ) = (p ζ).re ∨
      (2 * (ζ ^ e).re : ℝ) = (q ζ).re := by
    rcases hval with hh | hh | hh
    · left
      have hcast : ((2 * (ζ ^ e).re : ℝ) : ℂ) = 2 := by rw [hre, hh]
      exact_mod_cast hcast
    · right; left
      have hcast : ((2 * (ζ ^ e).re : ℝ) : ℂ) = p ζ := by rw [hre, hh]
      have := congrArg Complex.re hcast; simpa using this
    · right; right
      have hcast : ((2 * (ζ ^ e).re : ℝ) : ℂ) = q ζ := by rw [hre, hh]
      have := congrArg Complex.re hcast; simpa using this
  have hφ : (1 : ℝ) < goldenRatio := Real.one_lt_goldenRatio
  have hψ : goldenConj < 0 := Real.goldenConj_neg
  have hbound : 2 - goldenRatio ≤ Complex.normSq (ζ ^ i + ζ ^ j) := by
    rw [hexp]
    rcases periods_golden ζ h with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;>
      rw [hp, hq] at key <;> simp only [Complex.neg_re, Complex.ofReal_re] at key <;>
      rcases key with k | k | k <;> rw [k] <;> nlinarith
  have hsq : (goldenRatio⁻¹) ^ 2 = 2 - goldenRatio := by
    have hg : goldenRatio ^ 2 = goldenRatio + 1 := Real.goldenRatio_sq
    have hprod1 : (2 - goldenRatio) * goldenRatio ^ 2 = 1 := by nlinarith [hg]
    rw [inv_pow]; exact inv_eq_of_mul_eq_one_left hprod1
  have hns2 : ‖ζ ^ i + ζ ^ j‖ ^ 2 = Complex.normSq (ζ ^ i + ζ ^ j) := by
    rw [Complex.normSq_eq_norm_sq]
  have hsqle : (goldenRatio⁻¹) ^ 2 ≤ ‖ζ ^ i + ζ ^ j‖ ^ 2 := by rw [hsq, hns2]; exact hbound
  have hnn : (0 : ℝ) ≤ goldenRatio⁻¹ := by positivity
  calc goldenRatio⁻¹ = Real.sqrt ((goldenRatio⁻¹) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (‖ζ ^ i + ζ ^ j‖ ^ 2) := Real.sqrt_le_sqrt hsqle
    _ = ‖ζ ^ i + ζ ^ j‖ := Real.sqrt_sq (norm_nonneg _)
