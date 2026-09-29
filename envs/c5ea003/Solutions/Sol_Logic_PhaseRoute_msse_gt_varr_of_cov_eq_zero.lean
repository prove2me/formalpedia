-- Prove2me | solution 1 for Logic.PhaseRoute.msse_gt_varr_of_cov_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:35:31.094245+00:00
-- url     : https://prove2.me/submissions/3afc82ce-925a-461b-9382-969431387c21

-- Sol generated from Logic/PhaseRouteLeastSquares.lean
import Mathlib
import Definitions.Def_Logic_PhaseRouteLeastSquares
import Theorems.Thm_Logic_PhaseRoute_avg_add
import Theorems.Thm_Logic_PhaseRoute_avg_const
import Theorems.Thm_Logic_PhaseRoute_avg_const_mul
import Theorems.Thm_Logic_PhaseRoute_avg_nonneg
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

lemma varr_eq_avg_centered_sq (f : ι → ℝ) :
    varr f = avg (fun i => (f i - avg f) * (f i - avg f)) := by
  have hcong : (fun i => (f i - avg f) * (f i - avg f))
      = (fun i => (f i * f i - 2 * (avg f * f i)) + avg f * avg f) := by
    funext i; ring
  rw [hcong, avg_add, avg_sub, avg_const_mul, avg_const_mul, avg_const]
  simp only [varr, cov]
  ring

lemma varr_nonneg (f : ι → ℝ) : 0 ≤ varr f := by
  rw [varr_eq_avg_centered_sq]
  exact avg_nonneg fun i => mul_self_nonneg _



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
theorem solution{y h : ι → ℝ} (hc : cov y h = 0)
    (hv : varr h ≠ 0) : varr y < msse y h := by
  have hv' : 0 < varr h := lt_of_le_of_ne (varr_nonneg h) (Ne.symm hv)
  have hsq : 0 ≤ (avg y - avg h) * (avg y - avg h) := mul_self_nonneg _
  rw [msse_decomp, hc]
  linarith
