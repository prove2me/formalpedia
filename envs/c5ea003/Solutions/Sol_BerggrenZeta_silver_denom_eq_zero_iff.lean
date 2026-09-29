-- Prove2me | solution 1 for BerggrenZeta.silver_denom_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:47:56.105486+00:00
-- url     : https://prove2.me/submissions/c6b66926-3402-44cd-b53e-81831f90d0df

-- Sol generated from Novelty/BerggrenTreeCriticalLine.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeCriticalLine
import Definitions.Def_Novelty_BerggrenTreeSilverGrowth
import Theorems.Thm_BerggrenZeta_log_silverUnit_pos
import Theorems.Thm_BerggrenZeta_silver_cpow_eq_exp

/-!
# A provable critical line: the silver Ihara zeta of the Berggren tree

The Berggren tree is a regular ternary tree whose extremal (Pell) branch grows at the rate
`ε² = 3 + 2√2`, where `ε = 1 + √2` is the fundamental unit of `ℤ[√2]` and the eigenvalue of
the hyperbolic Berggren generator (`Novelty.BerggrenTreeSilverGrowth`).  Weighting each of
the `3^k` nodes at depth `k` by the *silver length* `ε^{2k}` instead of by its actual
hypotenuse gives the **silver Ihara-type zeta function** of the tree,

`Z_ε(s) = ∑_{k ≥ 0} 3^k ε^{-2ks} = (1 - 3 ε^{-2s})⁻¹`.

Unlike the true tree zeta (whose abscissa is `1`, see `Novelty.BerggrenTreeZetaAbscissa`),
this object is *exactly solvable*: it is a rational function of `ε^{-2s}`, hence
meromorphic on all of `ℂ`, and its poles can be computed in closed form.  The result is a
rigorous analogue of the Riemann Hypothesis for the Berggren tree:

> **All poles of `Z_ε` lie on the single vertical line `Re s = σ₀`, where
> `σ₀ = log 3 / (2 log(1+√2))`, and on that line they form the arithmetic progression
> `s = σ₀ + i k π / log(1+√2)`, `k ∈ ℤ`.**

The "critical line" is therefore determined by exactly two pieces of tree geometry: the
branching number `3` and the silver growth exponent `2 log ε`; the spacing of the poles is
the reciprocal silver length `π / log ε`, the analogue of the Ihara/Selberg spectral gap.

## Main results

* `silverZeta_eq_tsum` — the Dirichlet series `∑ 3^k ε^{-2ks}` converges exactly on the
  half-plane `Re s > σ₀` and sums to `Z_ε`;
* `silver_denom_eq_zero_iff` — **the critical line theorem**: the pole set of `Z_ε` is
  `{s : Re s = σ₀, Im s ∈ (π / log ε) ℤ}`;
* `silverZeta_analyticAt` and `silverZeta_meromorphicOn` — meromorphic continuation to `ℂ`;
* `silverAbscissa_lt_one` — the silver critical abscissa is strictly smaller than the true
  abscissa `1` of the tree zeta function: the silver model *underestimates* the density of
  small hypotenuses, which is the precise reason the moonshot conjecture fails.
-/

open BerggrenZeta

open Real Complex








/-! ## Part A. The half-plane of convergence -/




/-! ## Part B. The critical line -/





/-! ## Part C. Meromorphic continuation -/




/-! ## Part D. The silver abscissa is strictly below the true abscissa -/




open BerggrenZeta in
theorem solution(s : ℂ) :
    1 - 3 * (silverUnit : ℂ) ^ (-2 * s) = 0 ↔
      s.re = silverAbscissa ∧ ∃ k : ℤ, s.im = k * Real.pi / Real.log silverUnit := by
  have hL : 0 < Real.log silverUnit := log_silverUnit_pos
  have hLC : (Real.log silverUnit : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have h3 : Complex.exp (-(Real.log 3 : ℂ)) = 1 / 3 := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg,
      Real.exp_log (by norm_num : (0:ℝ) < 3)]
    norm_num
  have hiff : (1 - 3 * (silverUnit : ℂ) ^ (-2 * s) = 0) ↔
      Complex.exp (-2 * s * (Real.log silverUnit : ℂ))
        = Complex.exp (-(Real.log 3 : ℂ)) := by
    rw [silver_cpow_eq_exp, h3]
    constructor
    · intro h
      linear_combination (-1 / 3 : ℂ) * h
    · intro h
      linear_combination (-3 : ℂ) * h
  rw [hiff, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    have hs_eq : s = ((Real.log 3 / (2 * Real.log silverUnit) : ℝ) : ℂ)
        + ((-(n : ℝ) * Real.pi / Real.log silverUnit : ℝ) : ℂ) * I := by
      push_cast
      field_simp
      linear_combination -hn
    refine ⟨?_, ⟨-n, ?_⟩⟩
    · rw [hs_eq, silverAbscissa]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    · rw [hs_eq]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
      push_cast
      ring
  · rintro ⟨hre, k, him⟩
    refine ⟨-k, ?_⟩
    have hs : s = (s.re : ℂ) + (s.im : ℂ) * I := (Complex.re_add_im s).symm
    rw [hs, hre, him, silverAbscissa]
    push_cast
    field_simp
    ring
