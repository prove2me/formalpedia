-- Prove2me | Definitions.Def_Logic_PhaseRouteLeastSquares
-- name    : Logic_PhaseRouteLeastSquares
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:54:36.853101+00:00
-- url     : https://prove2.me/theorems/d7e667a3-23f3-4498-b66d-f6fc3dcaac53
-- title:
--   Aether Catalog definitions — Logic_PhaseRouteLeastSquares
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.PhaseRouteLeastSquares`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/PhaseRouteLeastSquares.lean by skeleton subtraction
import Mathlib
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

namespace Logic.PhaseRoute

open Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Empirical mean of `f` over the (finite, nonempty) sample space. -/
noncomputable def avg (f : ι → ℝ) : ℝ := (∑ i, f i) / (Fintype.card ι : ℝ)

/-- Empirical covariance. -/
noncomputable def cov (f g : ι → ℝ) : ℝ := avg (fun i => f i * g i) - avg f * avg g

/-- Empirical variance. -/
noncomputable def varr (f : ι → ℝ) : ℝ := cov f f

/-- Mean squared error of the predictor `h` for the target `y`. -/
noncomputable def msse (y h : ι → ℝ) : ℝ := avg (fun i => (y i - h i) * (y i - h i))

/-- Coefficient of determination of `h` relative to the intercept-only baseline. -/
noncomputable def Rsq (y h : ι → ℝ) : ℝ := 1 - msse y h / varr y


/-! ### Linearity of the empirical mean -/







/-! ### Variance -/





/-! ### The exact error decomposition -/








/-! ### Uncorrelated predictors are useless, and strictly harmful unless constant -/





/-! ### The optimal single-feature affine model -/










end Logic.PhaseRoute


