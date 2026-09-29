-- Prove2me | solution 1 for Logic.PhaseRoute.msse_excess_of_cov_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:35:30.575551+00:00
-- url     : https://prove2.me/submissions/6a9f9340-524d-417a-8b44-d2f4b0811b52

-- Sol generated from Logic/PhaseRouteLeastSquares.lean
import Mathlib
import Definitions.Def_Logic_PhaseRouteLeastSquares
import Theorems.Thm_Logic_PhaseRoute_avg_add
import Theorems.Thm_Logic_PhaseRoute_avg_const_mul
import Theorems.Thm_Logic_PhaseRoute_avg_sub
/-
# Finite-sample least squares: the exact incremental-`R²` calculus

This file builds, from scratch, the algebraic core needed to state and prove
*negative* results about feature encodings in a finite-sample linear model:

* `Logic.PhaseRoute.avg`, `cov`, `varr`   — empirical mean / covariance / variance,
* `Logic.PhaseRoute.msse`                — mean squared error of a predictor,
* `Logic.PhaseRoute.Rsq`                 — coefficient of determination against the
  constant (intercept-only) baseline.

The main results are exact identities, not inequalities-with-slack:

* `msse_decomp` : `msse y h = varr y - 2*cov y h + varr h + (avg y - avg h)^2`,
  the complete bias/variance/alignment split of the error of *any* predictor;
* `msse_ge_varr_of_cov_eq_zero` and its strict form `msse_gt_varr_of_cov_eq_zero`
  : a predictor uncorrelated with the target is *never* useful and is strictly
  harmful unless it is constant;
* `msse_affine_lower_bound` / `msse_affine_opt` : the optimal single-feature
  affine fit and its exact error, hence
* `Rsq_affine_le_corr_sq` / `Rsq_affine_opt_eq_corr_sq` : the best attainable
  `R²` of a one-feature model is *exactly* the squared empirical correlation.

As a by-product we derive Cauchy–Schwarz for the empirical covariance
(`cov_sq_le`) from the regression identity rather than the other way round.

This is the "dial" calculus used in `Logic.PhaseRouteAlignment` to prove that a
whole family of encodings is provably worthless while a degree-`2` interaction
encoding is provably perfect.
-/

open Logic.PhaseRoute

open Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]







/-! ### Linearity of the empirical mean -/







/-! ### Variance -/





/-! ### The exact error decomposition -/

omit [Nonempty ι] in
lemma msse_eq (y h : ι → ℝ) :
    msse y h = avg (fun i => y i * y i) - 2 * avg (fun i => y i * h i)
      + avg (fun i => h i * h i) := by
  have hcong : (fun i => (y i - h i) * (y i - h i))
      = (fun i => (y i * y i - 2 * (y i * h i)) + h i * h i) := by
    funext i; ring
  rw [msse, hcong, avg_add, avg_sub, avg_const_mul]

omit [Nonempty ι] in
/-- **Exact bias/variance/alignment split.** For every predictor `h`, the mean
squared error decomposes into the target variance, minus twice the covariance,
plus the predictor variance, plus the squared mean offset. -/
theorem msse_decomp (y h : ι → ℝ) :
    msse y h = varr y - 2 * cov y h + varr h + (avg y - avg h) * (avg y - avg h) := by
  rw [msse_eq]
  simp [varr, cov]
  ring






/-! ### Uncorrelated predictors are useless, and strictly harmful unless constant -/





/-! ### The optimal single-feature affine model -/











open Logic.PhaseRoute in
omit [Nonempty ι] in
theorem solution{y h : ι → ℝ} (hc : cov y h = 0) :
    msse y h - varr y = varr h + (avg y - avg h) * (avg y - avg h) := by
  rw [msse_decomp, hc]; ring
