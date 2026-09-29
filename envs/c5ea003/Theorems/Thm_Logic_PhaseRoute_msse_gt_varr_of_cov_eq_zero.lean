-- Prove2me | Theorems.Thm_Logic_PhaseRoute_msse_gt_varr_of_cov_eq_zero
-- name    : Logic.PhaseRoute.msse_gt_varr_of_cov_eq_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:31:40.733407+00:00
-- url     : https://prove2.me/theorems/7f79db3c-b44d-451d-8515-f119c5e5494b
-- title:
--   Strict-harm theorem.
-- statement:
--   **Strict-harm theorem.** An uncorrelated *nonconstant* predictor is strictly
--   worse than the baseline: the excess error is exactly its own variance.
--
--   ```lean
--   theorem Logic.PhaseRoute.msse_gt_varr_of_cov_eq_zero{y h : ι → ℝ} (hc : cov y h = 0)
--       (hv : varr h ≠ 0) : varr y < msse y h := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/PhaseRouteLeastSquares.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/PhaseRouteLeastSquares.lean#L179

-- Thm stub generated from Logic/PhaseRouteLeastSquares.lean
import Mathlib
import Definitions.Def_Logic_PhaseRouteLeastSquares
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








/-! ### Uncorrelated predictors are useless, and strictly harmful unless constant -/

theorem Logic.PhaseRoute.msse_gt_varr_of_cov_eq_zero{y h : ι → ℝ} (hc : cov y h = 0)
    (hv : varr h ≠ 0) : varr y < msse y h := by sorry
