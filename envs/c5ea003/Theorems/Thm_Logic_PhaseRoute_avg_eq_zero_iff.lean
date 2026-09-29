-- Prove2me | Theorems.Thm_Logic_PhaseRoute_avg_eq_zero_iff
-- name    : Logic.PhaseRoute.avg_eq_zero_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:31:16.182665+00:00
-- url     : https://prove2.me/theorems/b396d51d-3d7a-49e9-96f6-608cd4026259
-- title:
--   The mean of a nonnegative function vanishes only if the function vanishes.
-- statement:
--   The mean of a nonnegative function vanishes only if the function vanishes.
--
--   ```lean
--   theorem Logic.PhaseRoute.avg_eq_zero_iff{f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) : avg f = 0 ↔ ∀ i, f i = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/PhaseRouteLeastSquares.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/PhaseRouteLeastSquares.lean#L83

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

theorem Logic.PhaseRoute.avg_eq_zero_iff{f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) : avg f = 0 ↔ ∀ i, f i = 0 := by sorry
