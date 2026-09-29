-- Prove2me | solution 1 for IharaZeta.root_norm_of_ramanujan
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T04:19:13.4629+00:00
-- url     : https://prove2.me/submissions/7f3ba7e7-90e1-4be7-878b-00d06ba1248e

import Mathlib
import Definitions.Def_Novelty_IharaZetaRamanujanRH
open IharaZeta in
theorem solution (q lam : ℝ) (hq : 0 < q)
    (hlam : |lam| ≤ 2 * Real.sqrt q) (u : ℂ) (hu : iharaFactor q lam u = 0) :
    ‖u‖ = 1 / Real.sqrt q := by
  -- real and imaginary parts of `q u² - λ u + 1 = 0`
  have hre := congrArg Complex.re hu
  have him := congrArg Complex.im hu
  simp only [iharaFactor, pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.zero_re, Complex.add_im,
    Complex.sub_im, Complex.mul_im, Complex.one_im, Complex.zero_im] at hre him
  set x := u.re with hx
  set y := u.im with hy
  have hlam2 : lam ^ 2 ≤ 4 * q := by
    have := pow_le_pow_left₀ (abs_nonneg lam) hlam 2
    rw [sq_abs, mul_pow, Real.sq_sqrt hq.le] at this
    linarith
  -- the real part of every root is `λ / 2q`
  have hkey : 2 * q * x = lam := by
    by_cases hy0 : y = 0
    · rw [hy0] at hre
      have hsq : (2 * q * x - lam) ^ 2 ≤ 0 := by nlinarith
      have h0 : (2 * q * x - lam) ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
      linarith
    · have hprod : y * (2 * q * x - lam) = 0 := by linarith
      have := (mul_eq_zero.mp hprod).resolve_left hy0
      linarith
  -- hence `q (x² + y²) = 1`
  have hnorm2 : x * x + y * y = 1 / q := by
    rw [eq_div_iff hq.ne']
    linear_combination (-1 : ℝ) * hre + x * hkey
  rw [Complex.norm_def, Complex.normSq_apply, ← hx, ← hy, hnorm2,
    Real.sqrt_div zero_le_one, Real.sqrt_one]
